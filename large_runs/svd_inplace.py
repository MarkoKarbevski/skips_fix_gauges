"""Singular values of a float64 torch matrix in place, with the MKL LAPACK that ships inside torch (dgesdd, jobz='N').
torch.linalg.svdvals copies its input before calling LAPACK; this does not, so the peak memory is one matrix."""
import ctypes, os

import numpy as np
import torch

_lib = ctypes.CDLL(os.path.join(os.path.dirname(torch.__file__), "lib", "libtorch_cpu.so"))
_dgesdd = _lib.dgesdd_
_P = ctypes.POINTER(ctypes.c_double)
_I = ctypes.POINTER(ctypes.c_int)


def svdvals_inplace(J):
    """Singular values, largest first, of the contiguous float64 matrix J (rows x cols); J is overwritten."""
    assert J.dtype == torch.float64 and J.is_contiguous()
    rows, cols = J.shape
    A = J.numpy()                      # shares memory; row-major rows x cols = column-major cols x rows
    M, N = cols, rows
    k = min(M, N)
    s = np.empty(k)
    dummy = np.empty(1)
    iwork = np.empty(8 * k, dtype=np.int32)
    info = ctypes.c_int(0)
    jobz = ctypes.c_char(b"N")
    m_, n_, lda, one = ctypes.c_int(M), ctypes.c_int(N), ctypes.c_int(M), ctypes.c_int(1)

    def call(work, lwork):
        _dgesdd(ctypes.byref(jobz), ctypes.byref(m_), ctypes.byref(n_), A.ctypes.data_as(_P), ctypes.byref(lda),
                s.ctypes.data_as(_P), dummy.ctypes.data_as(_P), ctypes.byref(one), dummy.ctypes.data_as(_P),
                ctypes.byref(one), work.ctypes.data_as(_P), ctypes.byref(ctypes.c_int(lwork)),
                iwork.ctypes.data_as(_I), ctypes.byref(info), ctypes.c_size_t(1))

    query = np.empty(1)
    call(query, -1)
    call(np.empty(int(query[0]) + 1), int(query[0]))
    if info.value != 0:
        raise RuntimeError(f"dgesdd failed, info = {info.value}")
    return s


if __name__ == "__main__":
    import time
    torch.manual_seed(0)
    for shape in [(3000, 2500), (2500, 3000)]:
        X = torch.randn(*shape, dtype=torch.float64) @ torch.diag(torch.logspace(0, -12, shape[1], dtype=torch.float64))
        t0 = time.perf_counter(); ref = torch.linalg.svdvals(X).numpy(); t1 = time.perf_counter()
        got = svdvals_inplace(X.clone()); t2 = time.perf_counter()
        print(shape, "max rel diff", float(np.max(np.abs(got - ref) / ref)), f"torch {t1-t0:.2f}s  inplace {t2-t1:.2f}s")
