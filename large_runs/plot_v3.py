"""Spectra of the networks of queue3.json for one activation, drawn from the saved statistics alone (aggregate.py).
Usage: python3 plot_v3.py spectra_v3.npz OUT.pdf --act gelu [--eps 1e-5]

Rows: the families present for the activation (64 MLP blocks, the transformer, 8 MLP blocks); columns: without
normalization and with pre-RMSNorm. In each panel one line per kind of skip: the median over the draws of s_i / s_1,
a band from the smallest to the largest draw, and a dotted vertical line at the count when every readable draw sits
there. Dotted lines mark the counts; each note gives the number P of parameters and the count, so the curves and bands show
whether and how sharply the draws drop there. Networks without skips are solid when they start near the identity
(looks-linear or odd pairs) and dotted when they start from Gaussian weights; networks with skips start Gaussian.
"""
import argparse, json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.legend_handler import HandlerTuple
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.ticker import MaxNLocator

# (skip, start, label, color, line style). The line style of a network without skips says how it starts: solid
# near the identity (looks-linear or odd pairs), dotted from Gaussian weights. Networks with skips start Gaussian.
NEAR = ("none", "near", "without skips, start near the identity", "#eb6834", "solid")
GAUSS = ("none", "gauss", "without skips, Gaussian start", "#eb6834", (0, (1, 1.4)))
SKIPS = [
    ("id", "gauss", "identity skips", "#2a78d6", "solid"),
    ("full", "gauss", "learned skips, full", "#1baf7a", "solid"),
    ("tri", "gauss", "learned skips, triangular", "#eda100", (0, (3, 1.6))),
]
SERIES = [NEAR, GAUSS] + SKIPS
FAMILIES = ["deep", "tf", "L8"]
ink, muted, grid = "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({"font.family": "serif", "font.serif": ["Times New Roman", "Times", "Nimbus Roman", "DejaVu Serif"],
                     "mathtext.fontset": "stix", "font.size": 8, "axes.edgecolor": muted, "axes.labelcolor": ink,
                     "xtick.color": muted, "ytick.color": muted, "axes.linewidth": 0.6})


NAMES = {"gelu": "GELU", "relu": "ReLU", "relu2": "ReLU$^2$", "tanh": "tanh", "swiglu": "SwiGLU", "geglu": "GeGLU",
         "reglu": "ReGLU"}


def title(m):
    dm = rf"$d_{{\mathrm{{model}}}} = {m['d']}$"
    act = NAMES[m["act"]]
    if m.get("arch") == "tf":
        return rf"{act} transformer, {m['L']} layers, {dm}, {m['H']} heads, {m['T']} tokens, $m = {m['m']}$"
    return rf"$L = {m['L']}$ {act} blocks, {dm}, $m = {m['m']}$ hidden units"


def find(meta, fam, act, norm, skip, start):
    """The network of the family with this activation, normalization, skip and start ("near": looks-linear or odd
    pairs; "gauss": Gaussian weights), or None."""
    hits = {m.get("init", "gauss"): net for net, m in meta.items()
            if m["family"] == fam and m["act"] == act and m["norm"] == norm and m["skip"] == skip}
    return hits.get("ll", hits.get("pairs")) if start == "near" else hits.get("gauss")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("npz")
    ap.add_argument("out")
    ap.add_argument("--act", default="gelu")
    ap.add_argument("--eps", type=float, default=1e-5)
    ap.add_argument("--gauss", action="store_true")
    a = ap.parse_args()
    z = np.load(a.npz)
    meta = json.loads(z["meta_json"].item())
    fams = [f for f in FAMILIES if any(m["family"] == f and m["act"] == a.act for m in meta.values())]
    # looks-linear starts make each block the identity; the odd pairs of degree-2 blocks make it about c|h|h instead
    near_label = NEAR[2] if a.act in ("gelu", "relu", "tanh") else "without skips"
    series = [NEAR[:2] + (near_label,) + NEAR[3:], GAUSS] + SKIPS
    used = set()                                             # the series that appear somewhere, for the legend
    fig, axes = plt.subplots(len(fams), 2, figsize=(5.5, 2.35 * len(fams) + 0.45), squeeze=False)
    for i, fam in enumerate(fams):
        row_meta = None
        for j, norm in enumerate(("none", "rms")):
            ax = axes[i, j]
            xmax, notes = 0, []
            near_here = find(meta, fam, a.act, norm, "none", "near") is not None
            for skip, start, label, c, ls in series:
                net = find(meta, fam, a.act, norm, skip, start)
                if net is None:
                    continue
                used.add(label)
                m = meta[net]
                row_meta = row_meta or m
                P, pred = (int(v) for v in z[net + "_info"][:2])
                n = len(z[net + "_ranks"])
                xmax = max(xmax, P)
                second = skip == "none" and start == "gauss" and near_here   # a comparison next to the solid line
                # degree-two blocks without normalization drive the outputs like |x|^(2^L), far beyond the range in
                # which a double-precision Jacobian keeps its rank: such a network gets a note, no curve, no count line
                bad = m.get("overflowed", 0)
                lost = bad == n or m.get("max_abs_out", 0.0) > 1e12
                if net + "_median" in z.files and not lost:
                    med, lo, hi = z[net + "_median"], z[net + "_min"], z[net + "_max"]
                    idx = np.arange(1, len(med) + 1)
                    floor = -19.5
                    if not second:
                        ax.fill_between(idx, 10 ** np.maximum(lo, floor), 10 ** np.maximum(hi, floor), color=c,
                                        alpha=0.18, lw=0, rasterized=True)
                    ax.semilogy(idx, 10 ** np.maximum(med, floor), color=c, lw=0.9 if second else 1.1, ls=ls,
                                solid_capstyle="round", rasterized=True)
                # the dotted line marks the count; the curves and bands show whether and how sharply the draws
                # drop there, so the note gives only P and the count
                if not second and not lost:
                    ax.axvline(pred + 0.5, color=c, lw=0.8, ls=(0, (1.5, 2)))
                sub = None                                   # a second, gray line with the reason
                if lost:
                    text = f"count ${pred}$: not computable"
                    if m.get("arch", "mlp") == "mlp":
                        sub = "outputs overflow" if bad == n else f"outputs grow like $|x|^{{{2 ** m['L']}}}$"
                else:
                    text = f"count ${pred}$" + (f", overflow in {bad} of {n}" if bad else "")
                    ranks = [r for r in m.get("ranks", []) if r > 0]
                    if m.get("matches", 0) == 0:
                        below = (m.get("min_gap") or 0) >= 10 and ranks and all(pred / 2 < r < pred for r in ranks)
                        text += ": drops below it" if below else ": no clear drop"
                notes.append((c, ls, "Gaussian start, same count" if second else f"$P = {P}$, {text}", sub))
            if not notes:                                    # nothing computed for this panel yet
                ax.text(0.5, 0.5, "running", transform=ax.transAxes, ha="center", va="center", color=muted,
                        fontsize=8)
                ax.set_xticks([]); ax.set_yticks([])
                for side in ("left", "bottom"):
                    ax.spines[side].set_color(grid)
                for side in ("top", "right"):
                    ax.spines[side].set_visible(False)
                if i == len(fams) - 1:
                    ax.set_xlabel("singular value index (largest first)")
                continue
            lines = sum(1 + (sub is not None) for *_, sub in notes)
            y = 0.36 + 0.095 * max(0, lines - 4)
            for c, ls, text, sub in notes:
                ax.plot([0.03, 0.10], [y, y], transform=ax.transAxes, color=c, lw=1.1, ls=ls, solid_capstyle="round")
                ax.text(0.115, y, text, transform=ax.transAxes, ha="left", va="center", color=ink, fontsize=6.6)
                y -= 0.095
                if sub is not None:
                    ax.text(0.115, y + 0.012, sub, transform=ax.transAxes, ha="left", va="center", color=muted,
                            fontsize=6.2)
                    y -= 0.085
            ax.set_xlim(1, max(xmax, 2) * 1.01)
            ax.xaxis.set_major_locator(MaxNLocator(4, integer=True))
            ax.set_ylim(10 ** -19.5, 3)
            ax.set_yticks([1e-15, 1e-10, 1e-5, 1])
            ax.grid(axis="y", color=grid, lw=0.5)
            ax.set_axisbelow(True)
            for side in ("top", "right"):
                ax.spines[side].set_visible(False)
            if j == 0:
                ax.set_ylabel(r"$s_i/s_1$")
            if i == len(fams) - 1:
                ax.set_xlabel("singular value index (largest first)")
        if row_meta is not None:
            axes[i, 0].text(0.0, 1.06, title(row_meta), transform=axes[i, 0].transAxes, ha="left", va="bottom",
                            fontsize=8, color=ink, fontweight="bold")
    legend = [x for x in series if x[2] in used]
    H = fig.get_figheight()
    two_rows = len(legend) > 4 or sum(len(x[2]) for x in legend) > 90   # one row would not fit the width
    extra = 0.2 if two_rows else 0.0
    fig.subplots_adjust(left=0.105, right=0.985, bottom=0.45 / H, top=1 - (0.86 + extra) / H, wspace=0.17,
                        hspace=0.62 / 2.35 * 1.6)
    exponent = int(round(np.log10(a.eps)))
    for j, t in enumerate(["no normalization", rf"pre-RMSNorm, $\varepsilon = 10^{{{exponent}}}$"]):
        bb = axes[0, j].get_position()
        fig.text((bb.x0 + bb.x1) / 2, bb.y1 + 0.40 / H, t, ha="center", va="bottom", fontsize=8.5, color=ink,
                 fontweight="bold")
    handles = [(Patch(color=c, alpha=0.18, lw=0), Line2D([], [], color=c, lw=1.1, ls=ls)) for *_, c, ls in legend]
    labels = [x[2] for x in legend]
    fig.legend(handles, labels, handler_map={tuple: HandlerTuple(ndivide=1)}, loc="upper center",
               ncol=3 if two_rows else len(labels), frameon=False, fontsize=7.3,
               handlelength=1.8, bbox_to_anchor=(0.5, 1.0))
    fig.savefig(a.out, dpi=400)     # the curves and bands are rasterized, the text and axes stay vector
    fig.savefig(a.out.rsplit(".", 1)[0] + ".png", dpi=200)
    print("wrote", a.out)


if __name__ == "__main__":
    main()
