"""Lemma A.2, simulated: for each hidden state h_l of 8 skipless blocks under pre-RMSNorm (d = 16, 256 inputs), the
largest singular value of the Jacobian on the d(d+1)/2 directions e^{tS} at h_l, relative to s_1, against eps.
Solid with markers: computed in double precision (almost_sym.jsonl); dashed: the formula of the lemma
(formula_curves.json), which has no floor. GELU blocks are not homogeneous: no such directions."""
import json, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
ink, muted, grid = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.family": "serif", "font.serif": ["Times New Roman", "Times", "Nimbus Roman", "DejaVu Serif"],
                     "mathtext.fontset": "stix", "font.size": 8, "axes.edgecolor": muted, "axes.labelcolor": ink,
                     "xtick.color": muted, "ytick.color": muted, "axes.linewidth": 0.6})
recs = [json.loads(l) for l in open("almost_sym.jsonl")]
form = json.load(open("formula_curves.json"))
PANELS = [("relu", "ReLU, $k = 1$"), ("relu2", "ReLU$^2$, $k = 2$"), ("reglu", "ReGLU, $k = 2$"),
          ("gelu", "GELU, not homogeneous")]
L, FLOOR = 8, 1e-24
cmap = plt.get_cmap("copper")
fig, axes = plt.subplots(1, 4, figsize=(7.2, 2.7), sharey=True)
for ax, (act, title) in zip(axes, PANELS):
    runs = sorted((r for r in recs if r["act"] == act), key=lambda r: -r["eps"])
    eps = np.array([r["eps"] for r in runs])
    ax.axhspan(FLOOR, 2e-16, color=grid, lw=0, zorder=0)
    fr = sorted((v for v in form.values() if v["act"] == act), key=lambda v: -v["eps"])
    for l in range(L):
        c = cmap(0.1 + 0.8 * l / (L - 1))
        if fr:
            fe = np.array([v["eps"] for v in fr]); fs = np.array([v["smax_rel"][l] for v in fr])
            ax.plot(fe, np.maximum(fs, FLOOR / 10), color=c, lw=0.8, ls=(0, (2.5, 1.5)), zorder=2)
        s = np.array([max(r["states"][l]["smax_rel"], FLOOR) for r in runs])
        ax.plot(eps, s, color=c, lw=1.0, marker="o", ms=2.2, zorder=3)
        if act == "relu" and l in (0, 7):
            ax.text(eps[0] * 1.5, s[0], f"$h_{l}$", color=c, fontsize=6.8, va="center", ha="right")
    ax.set_title(title, fontsize=8, color=ink, pad=4)
    ax.set_xscale("log"); ax.set_yscale("log")
    ax.set_xlim(2e-1, 5e-13); ax.set_ylim(FLOOR, 3)
    ax.set_xticks([1e-2, 1e-7, 1e-12]); ax.set_yticks([1e-20, 1e-15, 1e-10, 1e-5, 1])
    ax.set_xlabel(r"$\varepsilon$")
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
axes[0].set_ylabel(r"largest singular value $/\,s_1$")
axes[3].text(3e-6, 1e-20, "below double\nprecision", fontsize=6.8, color=muted, va="center", ha="center")
handles = [Line2D([], [], color=muted, lw=1.0, marker="o", ms=2.2), Line2D([], [], color=muted, lw=0.8, ls=(0, (2.5, 1.5)))]
fig.legend(handles, ["computed in double precision", "Lemma A.2"], loc="upper center", ncol=2, frameon=False,
           fontsize=7.3, bbox_to_anchor=(0.5, 1.0))
fig.text(0.5, 0.875, r"directions $e^{tS}$ at each hidden state $h_\ell$: 8 skipless blocks, pre-RMSNorm, $d_{\mathrm{model}} = 16$",
         ha="center", fontsize=8, color=ink)
fig.subplots_adjust(left=0.095, right=0.975, bottom=0.16, top=0.76, wspace=0.2)
fig.savefig(sys.argv[1])
fig.savefig(sys.argv[1].rsplit(".", 1)[0] + ".png", dpi=200)
print("wrote", sys.argv[1])
