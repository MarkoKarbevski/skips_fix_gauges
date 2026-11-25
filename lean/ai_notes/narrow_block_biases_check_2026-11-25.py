import importlib.util, sys, io, contextlib
spec = importlib.util.spec_from_file_location("chk", "/home/claude/proj_up/biases_inside_blocks_check_2026-11-25.py")
m = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(m)
for kind in ['relu', 'swiglu', 'reglu']:
    for (d, din, dout, w) in [(3, 3, 3, [1]), (3, 4, 3, [1]), (3, 3, 4, [2]), (2, 2, 2, [1])]:
        for skip in [True, False]:
            m.run(kind, d, din, dout, w, skip, 500)
