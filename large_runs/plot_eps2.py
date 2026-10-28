"""Skipless ReLU networks under pre-RMSNorm at several eps: where the spectrum drops.
Usage: python3 plot_eps.py spectra_eps.npz OUT.pdf

Rows: 64 blocks (d_model = 4) and 8 blocks (d_model = 16); left the whole spectrum, right a zoom on the drops.
Gray lines: the count for eps > 0 (solid) and for eps -> 0 (dashed); ticks at the bottom of the zoom mark whole
blocks of d(d+1)/2 above the eps -> 0 count. A colored line marks where each draw drops (the largest gap).
"""
import json, sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.legend_handler import HandlerTuple
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

EPS = [1e-1, 1e-2, 1e-5, 1e-11]
COLORS = ["#f3a35f", "#e06a2c", "#a7461c", "#5c260f"]    # the orange of networks without skips, darker as eps -> 0
# rows: activation, label, hidden width, start suffix of the network name, symmetries inside per unit, homogeneous
ROWS = [("relu", "ReLU", 64, "ll0.3", 1, True), ("relu2", "ReLU$^2$", 64, "pairs0.1", 1, True),
        ("reglu", "ReGLU", 42, "pairs0.1", 2, True), ("gelu", "GELU", 64, "ll0.3", 0, False)]
FAM, L, d = "L8", 8, 16
ink, muted, grid = "#0b0b0b", "#52514e", "#e4e3df"
FLOOR = -19.5
plt.rcParams.update({"font.family": "serif", "font.serif": ["Times New Roman", "Times", "Nimbus Roman", "DejaVu Serif"],
                     "mathtext.fontset": "stix", "font.size": 8, "axes.edgecolor": muted, "axes.labelcolor": ink,
                     "xtick.color": muted, "ytick.color": muted, "axes.linewidth": 0.6})


def eps_tex(e):
    return rf"$\varepsilon = 10^{{{int(round(np.log10(e)))}}}$"


def main():
    npz, out = sys.argv[1:3]
    z = np.load(npz)
    fig, axes = plt.subplots(len(ROWS), 2, figsize=(5.5, 2.3 * len(ROWS) + 0.6), squeeze=False)
    for i, (act, label, m, start, per_unit, homogeneous) in enumerate(ROWS):
        o, step = d * (d - 1) // 2, d * (d + 1) // 2
        P = None
        for e, c in zip(EPS, COLORS):
            net = f"{FAM}_L{L}_d{d}_m{m}_rms{e:.0e}_none_{act}_{start}"
            if net + "_median" not in z.files:
                continue
            P = int(z[net + "_info"][0])
            med, lo, hi = z[net + "_median"], z[net + "_min"], z[net + "_max"]
            idx = np.arange(1, len(med) + 1)
            # the drop of every draw that has one (a draw without a gap reads a rank near the top: left out)
            drops = sorted({int(r) for r in z[net + "_ranks"] if r > P // 2})
            for ax in axes[i]:
                ax.fill_between(idx, 10 ** np.maximum(lo, FLOOR), 10 ** np.maximum(hi, FLOOR), color=c, alpha=0.16,
                                lw=0, rasterized=True)
                ax.semilogy(idx, 10 ** np.maximum(med, FLOOR), color=c, lw=1.0, rasterized=True)
                for r in drops:
                    ax.axvline(r + 0.5, color=c, lw=0.9, ls=(0, (1.5, 1.5)))
        s = L * m * per_unit
        count = P - (L + 1) * o - s                       # eps > 0: O(d) at h_0, ..., h_L
        if homogeneous:                                   # eps -> 0: GL(d) at h_0, ..., h_{L-1}, CO(d) at h_L
            count0 = P - L * d * d - (o + 1) - s
        else:                                             # eps -> 0: CO(d) at every hidden state
            count0 = P - (L + 1) * (o + 1) - s
        for j, ax in enumerate(axes[i]):
            ax.axvline(count + 0.5, color=muted, lw=0.9)
            ax.axvline(count0 + 0.5, color=muted, lw=0.9, ls=(0, (4, 2)))
            ax.set_ylim(10 ** FLOOR, 3)
            ax.set_yticks([1e-15, 1e-10, 1e-5, 1])
            ax.grid(axis="y", color=grid, lw=0.5)
            ax.set_axisbelow(True)
            for side in ("top", "right"):
                ax.spines[side].set_visible(False)
        axes[i, 0].set_xlim(1, P * 1.01)
        axes[i, 0].set_ylabel(r"$s_i/s_1$")
        z1 = axes[i, 1]
        z1.set_xlim(count0 - 2 * step, count + 2 * step) if homogeneous else z1.set_xlim(count0 - 40, count + 40)
        # whole blocks of d(d+1)/2 above the eps -> 0 count
        if homogeneous:
            blocks = count0 + step * np.arange(0, L + 2)
            z1.plot(blocks + 0.5, np.full(len(blocks), 10 ** FLOOR), ls="none", marker="|", ms=5, color=muted,
                    mew=0.7, clip_on=False)
        z1.set_xticks([count0, count])
        z1.set_xticklabels([f"{count0:,}", f"{count:,}"])
        if not homogeneous:                               # the two counts are close: labels on either side
            for lab, ha in zip(z1.get_xticklabels(), ("right", "left")):
                lab.set_horizontalalignment(ha)
        if homogeneous:
            z1.text(0.98, 0.96, rf"ticks: blocks of $d(d+1)/2 = {step}$", transform=z1.transAxes, ha="right",
                    va="top", fontsize=6.8, color=muted)
        axes[i, 0].text(0.0, 1.05, rf"{L} {label} blocks without skips, $d_{{\mathrm{{model}}}} = {d}$"
                        + ("" if homogeneous else ", not homogeneous"),
                        transform=axes[i, 0].transAxes, ha="left", va="bottom", fontsize=8, color=ink,
                        fontweight="bold")
        if i == len(ROWS) - 1:
            for ax in axes[i]:
                ax.set_xlabel("singular value index (largest first)")
    H = fig.get_figheight()
    fig.subplots_adjust(left=0.105, right=0.985, bottom=0.45 / H, top=1 - 0.95 / H, wspace=0.17, hspace=0.42)
    for j, t in enumerate(["whole spectrum", "near the drops"]):
        bb = axes[0, j].get_position()
        fig.text((bb.x0 + bb.x1) / 2, bb.y1 + 0.36 / H, t, ha="center", va="bottom", fontsize=8.5, color=ink)
    handles = [(Patch(color=c, alpha=0.16, lw=0), Line2D([], [], color=c, lw=1.0)) for c in COLORS]
    handles += [Line2D([], [], color=muted, lw=0.9), Line2D([], [], color=muted, lw=0.9, ls=(0, (4, 2)))]
    labels = [eps_tex(e) for e in EPS] + [r"count, $\varepsilon > 0$", r"count, $\varepsilon \to 0$"]
    fig.legend(handles, labels, handler_map={tuple: HandlerTuple(ndivide=1)}, loc="upper center", ncol=6,
               frameon=False, fontsize=7.3, handlelength=1.6, columnspacing=1.1, bbox_to_anchor=(0.5, 1.0))
    fig.savefig(out, dpi=400)
    fig.savefig(out.rsplit(".", 1)[0] + ".png", dpi=200)
    print("wrote", out)


if __name__ == "__main__":
    main()
