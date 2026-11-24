#!/usr/bin/env python3
"""
analyse.py -- turn optimal-Golomb-ruler lengths into exact h(N) and compare with sqrt(N).

Run as:  python -I analyse.py --own ogr_results.json --brute brute_force_results.json \
             --oeis-dir <folder with oeis_A003022.json, oeis_A143824.json> --outdir .

Definitions (index conventions CHECKED against the "offset" fields of the JSON files):
    G(k)  = length of the shortest Golomb ruler with k marks.  G(1)=0, G(2)=1.
            OEIS A003022 has offset 2: its first listed term (1) is G(2), so
            G(k) = A003022_data[k-2].
    h(N)  = max |A|, A a Sidon subset of {1..N};   h(0)=0.  OEIS A143824 has
            offset 0: its first listed term is h(0)=0, so h(N) = A143824_data[N].
    A Sidon set of size k inside {1..N} is a k-mark ruler of length <= N-1, hence
            h(N) = max{ k : G(k) + 1 <= N }.

What is produced
    h_N_data.csv       one row per N (requested columns first, extras after)
    tables.md          per-k table (jump points, peak excess, bound margins)
    analysis.json      all numbers quoted in summary.md
Nothing is hard-coded except the mathematical bounds quoted below.

Bounds tested
    counting bound : the k(k-1)/2 differences are distinct integers in [1, N-1]
                     =>  k(k-1) <= 2(N-1).
    Lindstrom bound: h(N) <= sqrt(N) + N^(1/4) + 1   (B. Lindstrom 1969; stated
                     here as the classical form, tested numerically, not re-proved).
"""
import argparse
import csv
import json
import math
import os


def load_oeis(path):
    d = json.load(open(path))[0]
    data = [int(x) for x in d["data"].split(",")]
    offset = int(str(d["offset"]).split(",")[0])
    return data, offset, d


def h_from_G(G, n_max):
    """h(N) for N = 0..n_max from G (dict k -> length); needs G[k] for every k with
    G[k] + 1 <= n_max, and G[kmax+1] > n_max - 1 guaranteed by the caller."""
    ks = sorted(G)
    h = []
    for N in range(n_max + 1):
        best = 0
        for k in ks:
            if G[k] + 1 <= N:
                best = k
        h.append(best)
    return h


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--own", required=True)
    ap.add_argument("--brute", default=None)
    ap.add_argument("--oeis-dir", required=True)
    ap.add_argument("--outdir", default=".")
    ap.add_argument("--controls", nargs="*", default=[],
                    help="other ogr_search.py result files (serial / other worker counts) "
                         "that must agree with --own on every common k (determinism check)")
    args = ap.parse_args()

    out = {}

    # ---------------- load ----------------
    own = json.load(open(args.own))
    G_own = {int(k): v for k, v in own["G"].items()}
    K_own = max(G_own)
    # lengths below this are fully ruled out for k = K_own + 1 (exclusive of nothing else)
    inc = own.get("incomplete")
    if inc and inc["k"] == K_own + 1:
        ruled_out_below = inc["lengths_fully_ruled_out_below"]
    else:
        ruled_out_below = G_own[K_own] + 1       # trivial: G(K+1) > G(K)
    N_own_exact = ruled_out_below                 # h(N) exactly known by own search for N <= this
    out["own"] = {"K_own": K_own, "G_own": G_own,
                  "G(K+1)_lower_bound_proved_by_own_search": ruled_out_below,
                  "exact_h_range_N_le": N_own_exact}

    A3022, off3022, meta3022 = load_oeis(os.path.join(args.oeis_dir, "oeis_A003022.json"))
    A143824, off143824, meta143824 = load_oeis(os.path.join(args.oeis_dir, "oeis_A143824.json"))
    assert off3022 == 2 and off143824 == 0, (off3022, off143824)
    G_ref = {1: 0}
    for i, v in enumerate(A3022):
        G_ref[i + off3022] = v
    K_ref = max(G_ref)
    out["reference"] = {"offset_A003022": off3022, "offset_A143824": off143824,
                        "A003022_terms": len(A3022), "k_range": [2, K_ref],
                        "A143824_terms": len(A143824), "A143824_N_range": [0, len(A143824) - 1]}

    # ---------------- cross-checks ----------------
    mism = []
    for k in sorted(G_own):
        if k in G_ref and G_ref[k] != G_own[k]:
            mism.append(("own_vs_A003022", k, G_own[k], G_ref[k]))
    checked_own_vs_ref = [k for k in sorted(G_own) if k in G_ref]
    out["check_own_vs_A003022"] = {"k_checked": [min(checked_own_vs_ref), max(checked_own_vs_ref)],
                                   "n_checked": len(checked_own_vs_ref),
                                   "mismatches": [list(m) for m in mism if m[0] == "own_vs_A003022"]}
    if args.brute and os.path.exists(args.brute):
        br = json.load(open(args.brute))
        Gb = {int(k): v for k, v in br["G"].items()}
        bad = [(k, Gb[k], G_own.get(k)) for k in Gb if G_own.get(k) != Gb[k]]
        cnt_bad = []
        for k, c in br["n_optimal_up_to_reflection"].items():
            mine = own["per_k"].get(k, {}).get("n_optimal_up_to_reflection")
            if mine is None:        # k = 3 is set by hand in ogr_search.py (not searched)
                continue
            if mine != c:
                cnt_bad.append((int(k), c, mine))
        out["check_own_vs_bruteforce"] = {"k_checked": [min(Gb), max(Gb)], "G_mismatches": bad,
                                          "optimal_ruler_count_mismatches": cnt_bad,
                                          "counts_compared_for_k": sorted(int(k) for k in br["n_optimal_up_to_reflection"]
                                                                          if k in own["per_k"])}
        mism += [("own_vs_bruteforce", *b) for b in bad]
        bi = br.get("incomplete")
        if bi:
            # brute force ran out of time on k=bi["k"]: it proved G(k) >= ruled_out_below
            out["check_own_vs_bruteforce"]["brute_force_partial"] = {
                "k": bi["k"], "no_ruler_shorter_than": bi["ruled_out_below"],
                "consistent_with_own_G": G_own.get(bi["k"], 10 ** 9) >= bi["ruled_out_below"]}

    # determinism: other runs (serial, different scheduling) must give identical G, rulers, node counts
    ctrl = {}
    for cpath in args.controls:
        c = json.load(open(cpath))
        diffs = []
        common = sorted(set(own["per_k"]) & set(c["per_k"]), key=int)
        for k in common:
            a, b = own["per_k"][k], c["per_k"][k]
            for fld in ("G", "optimal_rulers_up_to_reflection", "nodes_total_all_lengths"):
                if a[fld] != b[fld]:
                    diffs.append((int(k), fld))
            la = [(x["L"], x["nodes"], x["n_rulers"]) for x in a["per_length"]]
            lb = [(x["L"], x["nodes"], x["n_rulers"]) for x in b["per_length"]]
            if la != lb:
                diffs.append((int(k), "per_length"))
        ctrl[os.path.basename(cpath)] = {
            "k_compared": [int(common[0]), int(common[-1])] if common else None,
            "workers": c["meta"].get("workers"), "differences": diffs}
    out["determinism_controls"] = ctrl

    # h(N) derived from the reference table vs A143824 data, over all N listed there
    h_ref_full = h_from_G(G_ref, len(A143824) - 1)
    bad_h = [(N, h_ref_full[N], A143824[N]) for N in range(len(A143824)) if h_ref_full[N] != A143824[N]]
    out["check_h_from_A003022_vs_A143824"] = {"N_range": [0, len(A143824) - 1], "mismatches": bad_h}
    # h(N) from own G vs A143824
    n_cmp = min(N_own_exact, len(A143824) - 1)
    h_own_small = h_from_G(G_own, n_cmp)
    bad_h2 = [(N, h_own_small[N], A143824[N]) for N in range(n_cmp + 1) if h_own_small[N] != A143824[N]]
    out["check_h_own_vs_A143824"] = {"N_range": [0, n_cmp], "mismatches": bad_h2}

    # A003022 internal consistency: strictly increasing, G(k) >= k(k-1)/2, A227590 = A003022 + 1
    out["reference_sanity"] = {
        "strictly_increasing": all(G_ref[k + 1] > G_ref[k] for k in range(1, K_ref)),
        "G_ge_k_k1_over_2": all(G_ref[k] >= k * (k - 1) // 2 for k in G_ref),
    }
    a227590 = load_oeis(os.path.join(args.oeis_dir, "oeis_A227590.json"))[0]
    out["reference_sanity"]["A227590_equals_A003022_plus_1"] = (
        a227590 == [1] + [v + 1 for v in A3022[:len(a227590) - 1]] or
        a227590 == [v + 1 for v in A3022][:len(a227590)] or
        a227590[1:] == [v + 1 for v in A3022][:len(a227590) - 1])

    # ---------------- build h(N) for N = 1..N_ref_max ----------------
    # exact (assuming the published table) for N <= G_ref[K_ref] + 1 = A003022_last + 1
    N_ref_max = G_ref[K_ref] + 1
    G_union = dict(G_ref)
    for k, v in G_own.items():
        G_union[k] = v                      # own values override (identical wherever both exist)
    h = h_from_G(G_union, N_ref_max)
    out["N_ref_max"] = N_ref_max

    def source(N):
        return "own_search" if N <= N_own_exact else "OEIS_A003022_reference"

    rows = []
    for N in range(1, N_ref_max + 1):
        hn = h[N]
        sq = math.sqrt(N)
        q4 = N ** 0.25
        ex = hn - sq
        lind = sq + q4 + 1.0
        rows.append({
            "N": N, "h": hn, "sqrt_N": sq, "h_minus_sqrt_N": ex, "N_pow_quarter": q4,
            "excess_over_N_quarter": ex / q4,
            "lindstrom_bound": lind, "lindstrom_margin": lind - hn,
            "counting_margin": 2 * (N - 1) - hn * (hn - 1),
            "source": source(N)})
    with open(os.path.join(args.outdir, "h_N_data.csv"), "w", newline="") as f:
        cols = ["N", "h", "sqrt_N", "h_minus_sqrt_N", "N_pow_quarter", "excess_over_N_quarter",
                "lindstrom_margin", "counting_margin", "source"]
        w = csv.writer(f, lineterminator="\n")
        w.writerow(cols)
        for r in rows:
            w.writerow([r["N"], r["h"], f"{r['sqrt_N']:.6f}", f"{r['h_minus_sqrt_N']:.6f}",
                        f"{r['N_pow_quarter']:.6f}", f"{r['excess_over_N_quarter']:.6f}",
                        f"{r['lindstrom_margin']:.6f}", r["counting_margin"], r["source"]])

    # ---------------- statistics ----------------
    def stats(rs, label):
        s = {"label": label, "N_range": [rs[0]["N"], rs[-1]["N"]], "count": len(rs)}
        m = max(rs, key=lambda r: (r["h_minus_sqrt_N"], -r["N"]))
        s["max_h_minus_sqrt"] = {"value": m["h_minus_sqrt_N"], "N": m["N"], "h": m["h"]}
        mn = min(rs, key=lambda r: (r["h_minus_sqrt_N"], r["N"]))
        s["min_h_minus_sqrt"] = {"value": mn["h_minus_sqrt_N"], "N": mn["N"], "h": mn["h"]}
        rs2 = [r for r in rs if r["N"] >= 2]          # N=1 is the degenerate 1-1=0
        if rs2:
            mn = min(rs2, key=lambda r: (r["h_minus_sqrt_N"], r["N"]))
            s["min_h_minus_sqrt_N_ge_2"] = {"value": mn["h_minus_sqrt_N"], "N": mn["N"], "h": mn["h"]}
        m = max(rs, key=lambda r: (r["excess_over_N_quarter"], -r["N"]))
        s["max_ratio"] = {"value": m["excess_over_N_quarter"], "N": m["N"], "h": m["h"]}
        mn = min(rs, key=lambda r: (r["excess_over_N_quarter"], r["N"]))
        s["min_ratio"] = {"value": mn["excess_over_N_quarter"], "N": mn["N"], "h": mn["h"]}
        li = min(rs, key=lambda r: (r["lindstrom_margin"], r["N"]))
        s["min_lindstrom_margin"] = {"value": li["lindstrom_margin"], "N": li["N"], "h": li["h"]}
        s["lindstrom_holds_all"] = all(r["h"] <= r["lindstrom_bound"] for r in rs)
        cm = min(rs, key=lambda r: (r["counting_margin"], r["N"]))
        s["min_counting_margin"] = {"value": cm["counting_margin"], "N": cm["N"], "h": cm["h"]}
        s["counting_holds_all"] = all(r["counting_margin"] >= 0 for r in rs)
        s["counting_equality_N"] = [r["N"] for r in rs if r["counting_margin"] == 0]
        # relative Lindstrom margin: (bound - h)/ (N^(1/4)+1): how much of the slack is left
        rl = min(rs, key=lambda r: ((r["lindstrom_bound"] - r["h"]) / (r["lindstrom_bound"] - r["sqrt_N"]), r["N"]))
        s["min_lindstrom_margin_relative_to_allowed_excess"] = {
            "value": (rl["lindstrom_bound"] - rl["h"]) / (rl["lindstrom_bound"] - rl["sqrt_N"]),
            "N": rl["N"], "h": rl["h"]}
        return s

    own_rows = [r for r in rows if r["N"] <= N_own_exact]
    ref_rows = [r for r in rows if r["N"] > N_own_exact]
    out["stats_own"] = stats(own_rows, "N covered by own exhaustive search")
    out["stats_ref"] = stats(ref_rows, "N beyond own search, from the published A003022 table (unverified by me)") if ref_rows else None
    out["stats_all"] = stats(rows, "all N = 1..N_ref_max")

    # ---------------- per-k table (peak excess is at N = G(k)+1) ----------------
    per_k = []
    for k in sorted(G_union):
        if k < 2 or k > K_ref:
            continue
        N0 = G_union[k] + 1                              # first N with h(N) = k
        N1 = (G_union[k + 1] if (k + 1) in G_union else None)   # last N with h(N) = k
        e0 = k - math.sqrt(N0)
        e1 = (k - math.sqrt(N1)) if N1 else None
        per_k.append({
            "k": k, "G_k": G_union[k], "N_first": N0, "N_last": N1,
            "peak_excess": e0, "peak_ratio": e0 / N0 ** 0.25,
            "trough_excess": e1,
            "k2_minus_Gk_over_k": (k * k - G_union[k]) / k,
            "G_over_k2": G_union[k] / (k * k),
            "source": "own_search" if k in G_own else "OEIS_A003022_reference"})
    out["per_k"] = per_k

    # least-squares fit of peak excess against k, k^(1/2) and log k (descriptive only)
    pk = [(p["k"], p["peak_excess"]) for p in per_k if p["k"] >= 5]

    def linfit(xs, ys):
        n = len(xs)
        mx, my = sum(xs) / n, sum(ys) / n
        sxx = sum((x - mx) ** 2 for x in xs)
        b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
        a = my - b * mx
        sse = sum((y - (a + b * x)) ** 2 for x, y in zip(xs, ys))
        return a, b, sse

    fits = {}
    for name, tf in (("k", lambda k: k), ("sqrt_k", math.sqrt), ("log_k", math.log)):
        a, b, sse = linfit([tf(k) for k, _ in pk], [e for _, e in pk])
        fits[name] = {"a": a, "b": b, "sse": sse}
    # constant model: mean
    mean_e = sum(e for _, e in pk) / len(pk)
    fits["constant"] = {"a": mean_e, "b": 0.0, "sse": sum((e - mean_e) ** 2 for _, e in pk)}
    out["peak_excess_fits_k_ge_5"] = {"n_points": len(pk), "fits": fits}
    out["peak_excess_first_last"] = {"k5": dict(pk)[5], f"k{K_ref}": dict(pk)[K_ref]}

    # ---------------- tables.md ----------------
    with open(os.path.join(args.outdir, "tables.md"), "w", encoding="utf-8") as f:
        f.write("# Per-k table\n\n")
        f.write("h(N) = k exactly for G(k)+1 <= N <= G(k+1).  Peak excess = k - sqrt(G(k)+1) "
                "(largest h - sqrt N on that plateau); trough = k - sqrt(G(k+1)) (smallest).\n"
                "Source: own = my exhaustive search; ref = OEIS A003022 as published, NOT verified by me.\n\n")
        f.write("| k | G(k) | h=k for N in | peak h-sqrtN | peak/N^(1/4) | trough h-sqrtN | (k^2-G)/k | source |\n")
        f.write("|---|---|---|---|---|---|---|---|\n")
        for p in per_k:
            rng = f"{p['N_first']}..{p['N_last']}" if p["N_last"] else f"{p['N_first']}.."
            tr = f"{p['trough_excess']:.3f}" if p["trough_excess"] is not None else ""
            f.write(f"| {p['k']} | {p['G_k']} | {rng} | {p['peak_excess']:.3f} | {p['peak_ratio']:.3f} | "
                    f"{tr} | {p['k2_minus_Gk_over_k']:.2f} | {'own' if p['source'] == 'own_search' else 'ref'} |\n")

    with open(os.path.join(args.outdir, "analysis.json"), "w") as f:
        json.dump(out, f, indent=1, sort_keys=True, default=str)

    # ---------------- console report ----------------
    print("own search covers k <= %d, exact h(N) for N <= %d" % (K_own, N_own_exact))
    print("reference A003022: k = 2..%d (%d terms), h exact for N <= %d" % (K_ref, len(A3022), N_ref_max))
    print("mismatches:", mism, "| h(A003022) vs A143824:", bad_h, "| h(own) vs A143824:", bad_h2)
    print("determinism controls:", json.dumps(ctrl))
    print("brute force check:", json.dumps(out.get("check_own_vs_bruteforce")))
    for key in ("stats_own", "stats_ref", "stats_all"):
        s = out[key]
        if not s:
            continue
        print("\n" + key, s["label"], s["N_range"])
        for kk in ("max_h_minus_sqrt", "min_h_minus_sqrt", "min_h_minus_sqrt_N_ge_2",
                   "max_ratio", "min_ratio",
                   "min_lindstrom_margin", "min_counting_margin",
                   "min_lindstrom_margin_relative_to_allowed_excess"):
            print("  ", kk, s[kk])
        print("   lindstrom_holds_all", s["lindstrom_holds_all"], "counting_holds_all",
              s["counting_holds_all"], "counting equality at N =", s["counting_equality_N"])
    print("\nfits of peak excess (k>=5):", json.dumps(fits, indent=0))


if __name__ == "__main__":
    main()
