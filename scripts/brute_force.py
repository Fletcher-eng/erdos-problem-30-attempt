#!/usr/bin/env python3
"""
brute_force.py -- deliberately naive, independent oracle for optimal Golomb rulers.

Run as:  python -I brute_force.py --k-max 9 --out brute_force_results.json

No bitsets, no remaining-length bound, no reflection symmetry: it just places marks
left to right with a set of used differences and counts EVERY k-mark Golomb ruler
whose first mark is 0 and last mark is exactly L (so each ruler is counted together
with its mirror image).  G(k) is the least L with a non-zero count.  Used only to
cross-check the fast search in ogr_search.py (G(k) and the number of optimal rulers:
brute count / 2 must equal the fast search's count up to reflection, since a Golomb
ruler with >= 3 marks is never its own mirror image).

Only the following (exact) feasibility prune is used: after choosing a mark at x with
r marks still to place, x + r <= L.
"""
import argparse
import json
import sys
import time


def count_rulers(k, L):
    """Number of k-mark Golomb rulers with marks 0 = m_0 < ... < m_{k-1} = L."""
    marks = [0]
    used = set()
    nodes = 0

    def rec(n):
        # n marks placed so far
        nonlocal nodes
        if n == k - 1:
            # last mark forced at L
            new = [L - m for m in marks]
            for d in new:
                if d in used:
                    return 0
            return 1
        total = 0
        last = marks[-1]
        r = k - n - 1                      # marks still to place after this one
        for x in range(last + 1, L - r + 1):
            new = [x - m for m in marks]
            ok = True
            for d in new:
                if d in used:
                    ok = False
                    break
            if not ok:
                continue
            nodes += 1
            marks.append(x)
            used.update(new)
            total += rec(n + 1)
            used.difference_update(new)
            marks.pop()
        return total

    c = rec(1)
    return c, nodes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k-max", type=int, default=9)
    ap.add_argument("--out", default="brute_force_results.json")
    ap.add_argument("--deadline-seconds", type=float, default=900.0)
    args = ap.parse_args()
    t0 = time.time()
    out = {"G": {"1": 0, "2": 1}, "n_optimal_up_to_reflection": {}, "nodes": {}, "seconds": {}}
    for k in range(3, args.k_max + 1):
        tk = time.time()
        L = k * (k - 1) // 2 if False else k - 1          # start low: no assumption
        nodes_k = 0
        while True:
            c, nodes = count_rulers(k, L)
            nodes_k += nodes
            if c:
                break
            L += 1
            if time.time() - t0 > args.deadline_seconds:
                break
        if not c:
            print(f"k={k}: deadline, lengths < {L} ruled out", flush=True)
            out["incomplete"] = {"k": k, "ruled_out_below": L}
            break
        assert c % 2 == 0
        out["G"][str(k)] = L
        out["n_optimal_up_to_reflection"][str(k)] = c // 2
        out["nodes"][str(k)] = nodes_k
        out["seconds"][str(k)] = round(time.time() - tk, 2)
        print(f"k={k}: G={L}  optimal rulers (up to reflection)={c // 2}  "
              f"nodes={nodes_k:,d}  {time.time() - tk:.1f}s", flush=True)
        with open(args.out, "w") as f:
            json.dump(out, f, indent=1, sort_keys=True)
    out["total_seconds"] = round(time.time() - t0, 2)
    with open(args.out, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
