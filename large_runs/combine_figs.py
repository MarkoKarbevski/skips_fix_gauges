"""Concatenate the figures in paper docs/figs/large into one PDF, all_large_figures.pdf, with a bookmark per figure.
The separate PDFs stay as they are. Run from the repository root: python large_runs/combine_figs.py"""
import os
from pypdf import PdfReader, PdfWriter

FIGS = os.path.join("paper docs", "figs", "large")
ACTS = [("relu", "ReLU"), ("gelu", "GELU"), ("tanh", "tanh"), ("relu2", "ReLU^2"), ("reglu", "ReGLU"),
        ("swiglu", "SwiGLU"), ("geglu", "GeGLU")]
ORDER = ([(f"spectra_depth_{a}.pdf", f"Depths 2, 4, 8: {n}") for a, n in ACTS]
         + [(f"spectra_deep_{a}.pdf", f"64 blocks: {n}") for a, n in ACTS]
         + [("spectra_eps8.pdf", "eps sweep, 8 blocks"), ("spectra_eps.pdf", "eps sweep"),
            ("almost_sym.pdf", "Almost-symmetries, Lemma A.2")])
OUT = "all_large_figures.pdf"

writer = PdfWriter()
listed = {f for f, _ in ORDER}
extra = sorted(f for f in os.listdir(FIGS) if f.endswith(".pdf") and f != OUT and f not in listed)
for name, title in ORDER + [(f, f[:-4]) for f in extra]:
    path = os.path.join(FIGS, name)
    if not os.path.exists(path):
        continue
    start = len(writer.pages)
    for page in PdfReader(path).pages:
        writer.add_page(page)
    writer.add_outline_item(title, start)
writer.page_mode = "/UseOutlines"
with open(os.path.join(FIGS, OUT), "wb") as f:
    writer.write(f)
print(f"{len(writer.pages)} pages written to {os.path.join(FIGS, OUT)}")
