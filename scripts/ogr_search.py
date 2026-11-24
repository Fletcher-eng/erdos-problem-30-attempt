#!/usr/bin/env python3
"""
ogr_search.py -- exhaustive search for optimal Golomb rulers (pure stdlib).

Run as:   python -I ogr_search.py --k-max 12 --workers 14 --out ogr_results.json

WHAT IT COMPUTES
    G(k) = length of the shortest Golomb ruler with k marks (OEIS A003022 up to
    an index shift: G(1)=0, G(2)=1, G(3)=3, ...).  A Golomb ruler is a set of
    integers {0 = a_0 < a_1 < ... < a_{k-1} = L} whose pairwise positive
    differences are all distinct (equivalently a Sidon set).

METHOD (depth-first, marks added in increasing order, bitset pruning)
    Iterative deepening on the length L = G(k-1)+1, G(k-1)+2, ...  For each L
    the search looks for rulers whose last mark is *exactly* L.  The first L
    that has a ruler is G(k) (all smaller L were searched exhaustively and are
    empty, so this is a proof of optimality, relative to the correctness of
    the code, which is cross-checked in brute_force.py and in analyse.py).

    State (all Python ints used as bitsets, bit i <-> distance i):
        lst   bit l set  <=> there is a mark exactly l to the left of the
                             newest mark (bit 0 = the newest mark itself)
        dist  bit d set  <=> difference d is already used
        comp  bit s set  <=> placing the next mark s to the right of the
                             newest mark would repeat a used difference,
                             i.e. s in  union over l in lst of (dist - l)
    Placing the next mark at gap s (allowed iff bit s of comp is 0):
        sh   = lst << s                 # new differences l+s
        dist'= dist | sh
        lst' = sh | 1
        comp'= (comp >> s) | dist'      # derivation in summary.md / comments
    Why comp' = (comp >> s) | dist':  comp' = union over l' in lst' of
    (dist' - l').  The term l'=0 is dist'.  For l' = l+s (l an old entry of
    lst) we get (dist' - l - s).  The new part of dist', N = {l2+s : l2 in lst},
    contributes N - l - s = {l2 - l}: a difference of two old marks, which is
    already inside dist (or non-positive, hence irrelevant), so it is covered
    by the l'=0 term.  The old part of dist contributes (dist - l) >> s,
    and the union over l is (comp >> s).

    Bounds used (all exact, no heuristics):
      * remaining-length bound: let m = number of marks still to place
        (including the one being chosen now) and pos = position of the newest
        mark.  If the next mark goes at pos+s, then it and the m-1 marks after
        it form an m-mark ruler, which has length >= G(m).  The last mark is at
        L, so pos + s + G(m) <= L, i.e. s <= L - pos - G[m] (code: smax).
        The G values used are for m < k, i.e. the values this very program
        proved in earlier iterations (nothing is assumed from the literature).
      * mirror symmetry: a ruler and its reflection are the same ruler, so we
        only keep those with first gap g1 < last gap (k >= 3: g1 = last gap
        would repeat a difference).  Used to cap the second-to-last gap.
      * the last mark is placed at exactly L, so its gap is forced and only
        one bit has to be tested (the final level is inlined).

PARALLELISM
    The tree is cut at a fixed depth into independent subtrees (tasks); a
    multiprocessing Pool searches them.  Results are sums / sorted unions, so
    node counts and ruler lists do not depend on scheduling (deterministic).
    A wall-clock deadline can stop a search part-way: then only the lengths
    that were *completely* searched are claimed as ruled out.

NODE COUNT
    "nodes" = number of valid partial rulers generated, counting the
    placement of every mark after the mark at 0, including the final marks.
"""
import argparse
import json
import multiprocessing as mp
import os
import sys
import time


# ----------------------------------------------------------------------------
# core depth-first search
# ----------------------------------------------------------------------------
def build_dfs(L, G):
    """Return (dfs, sols, cnt, tasks, split) for searching rulers of length L.

    G[m] must hold the optimal length for m marks (G[1]=0, G[2]=1, ...) for
    every m that can be indexed (m up to k-1 where k = number of marks).
    sols  : list of mark tuples found (reflection-canonical: g1 < last gap)
    cnt   : one-element list, number of nodes
    tasks : list of states collected when split[0] == m (for parallel runs)
    """
    sols = []
    cnt = [0]
    tasks = []
    split = [-1]

    def dfs(pos, lst, dist, comp, m, g1):
        # m = number of marks still to place (>= 2 at every call, see root)
        if m == split[0]:
            tasks.append((pos, lst, dist, comp, m, g1))
            return
        if m == 2:
            # place the second-to-last mark, then the last at exactly L.
            # last gap t = L - pos - s must exceed g1 (mirror canonical form)
            smax = L - pos - g1 - 1
            if smax < 1:
                return
            free = ~comp & ((1 << (smax + 1)) - 2)      # bits 1..smax not in comp
            cnt[0] += free.bit_count()
            while free:
                low = free & -free
                free ^= low
                s = low.bit_length() - 1
                sh = lst << s
                d2 = dist | sh
                t = L - pos - s
                if not (((comp >> s) | d2) >> t) & 1:   # last gap legal?
                    cnt[0] += 1
                    full = ((sh | 1) << t) | 1          # lst after the last mark
                    marks = []
                    b = full
                    while b:
                        lo = b & -b
                        b ^= lo
                        marks.append(L - (lo.bit_length() - 1))
                    sols.append(tuple(sorted(marks)))
            return
        smax = L - pos - G[m]
        if smax < 1:
            return
        free = ~comp & ((1 << (smax + 1)) - 2)
        cnt[0] += free.bit_count()
        m1 = m - 1
        while free:
            low = free & -free
            free ^= low
            s = low.bit_length() - 1
            sh = lst << s
            d2 = dist | sh
            dfs(pos + s, sh | 1, d2, (comp >> s) | d2, m1, g1 or s)

    return dfs, sols, cnt, tasks, split


def search_serial(k, L, G):
    """All reflection-canonical k-mark rulers of length exactly L (k >= 4)."""
    dfs, sols, cnt, _, _ = build_dfs(L, G)
    dfs(0, 1, 0, 0, k - 1, 0)
    return cnt[0], sorted(sols)


def _worker_init():
    """Lower the priority of worker processes (Windows only, best effort)."""
    if sys.platform == "win32":
        try:
            import ctypes
            k32 = ctypes.windll.kernel32
            k32.SetPriorityClass(k32.GetCurrentProcess(), 0x00004000)  # BELOW_NORMAL
        except Exception:
            pass


def _run_task(args):
    L, G, state = args
    dfs, sols, cnt, _, _ = build_dfs(L, G)
    dfs(*state)
    return cnt[0], sols


def search_parallel(k, L, G, pool, depth, deadline):
    """Same result as search_serial but split into subtrees over a Pool.

    depth    : number of marks (after mark 0) fixed before splitting
    deadline : absolute time.time() value; if passed, the search is abandoned
    Returns (nodes, sols, completed_flag, tasks_done, tasks_total).
    """
    dfs, sols0, cnt0, tasks, split = build_dfs(L, G)
    split[0] = k - 1 - depth
    dfs(0, 1, 0, 0, k - 1, 0)
    total = cnt0[0]
    sols = list(sols0)
    n_tasks = len(tasks)
    done = 0
    it = pool.imap_unordered(_run_task, [(L, G, st) for st in tasks], chunksize=1)
    while done < n_tasks:
        remaining = deadline - time.time()
        if remaining <= 0:
            return total, sorted(sols), False, done, n_tasks
        try:
            c, s = it.next(timeout=min(remaining, 5.0))
        except mp.TimeoutError:
            continue
        total += c
        sols.extend(s)
        done += 1
    return total, sorted(sols), True, done, n_tasks


# ----------------------------------------------------------------------------
# independent checker
# ----------------------------------------------------------------------------
def is_golomb(marks):
    """True iff all positive pairwise differences are distinct."""
    seen = set()
    for i in range(len(marks)):
        for j in range(i):
            d = marks[i] - marks[j]
            if d <= 0 or d in seen:
                return False
            seen.add(d)
    return True


# ----------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k-max", type=int, default=11)
    ap.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    ap.add_argument("--out", default="ogr_results.json")
    ap.add_argument("--deadline-seconds", type=float, default=1700.0,
                    help="total wall-clock budget; a part-way search is reported honestly")
    ap.add_argument("--parallel-from-k", type=int, default=9,
                    help="use the process pool for k >= this (smaller k run serially)")
    ap.add_argument("--split-depth", type=int, default=3)
    args = ap.parse_args()

    t_start = time.time()
    deadline = t_start + args.deadline_seconds

    # trivial values, proved by hand: {0} and {0,1}; k = 3 -> {0,1,3} (length 3:
    # length 2 only has {0,1,2} which repeats difference 1)
    G = [0, 0, 1, 3]
    results = {
        "meta": {
            "python": sys.version.split()[0],
            "workers": args.workers,
            "deadline_seconds": args.deadline_seconds,
            "note": "k=1,2,3 are trivial and set by hand; k>=4 searched.",
        },
        "G": {"1": 0, "2": 1, "3": 3},
        "per_k": {},
        "incomplete": None,
    }
    pool = None
    if args.k_max >= args.parallel_from_k and args.workers > 1:
        pool = mp.Pool(args.workers, initializer=_worker_init)

    def save():
        with open(args.out, "w") as f:
            json.dump(results, f, indent=1, sort_keys=True)

    for k in range(4, args.k_max + 1):
        tk = time.time()
        L = G[k - 1] + 1                    # G strictly increasing => G(k) > G(k-1)
        nodes_total = 0
        per_length = []
        found = None
        while True:
            t0 = time.time()
            if pool is not None and k >= args.parallel_from_k:
                nodes, sols, ok, d_done, d_tot = search_parallel(
                    k, L, tuple(G), pool, args.split_depth, deadline)
                if not ok:
                    # deadline hit: lengths < L are fully ruled out, L is not
                    results["incomplete"] = {
                        "k": k,
                        "lengths_fully_ruled_out_below": L,
                        "meaning": f"no {k}-mark Golomb ruler has length < {L}; "
                                   f"length {L} only {d_done}/{d_tot} tasks done",
                        "tasks_done": d_done, "tasks_total": d_tot,
                    }
                    print(f"[k={k}] DEADLINE during L={L} ({d_done}/{d_tot} tasks); "
                          f"G({k}) >= {L} proved", flush=True)
                    break
            else:
                nodes, sols = search_serial(k, L, tuple(G))
            dt = time.time() - t0
            nodes_total += nodes
            per_length.append({"L": L, "nodes": nodes, "n_rulers": len(sols),
                               "seconds": round(dt, 3)})
            print(f"[k={k}] L={L:4d} nodes={nodes:>14,d} rulers={len(sols)} "
                  f"({dt:.1f}s)", flush=True)
            if sols:
                found = sols
                break
            L += 1
        if found is None:
            save()
            break
        for r in found:                      # independent re-check of every ruler
            assert len(r) == k and r[0] == 0 and r[-1] == L and is_golomb(r), r
        G.append(L)
        results["G"][str(k)] = L
        results["per_k"][str(k)] = {
            "G": L,
            "optimal_rulers_up_to_reflection": [list(r) for r in found],
            "n_optimal_up_to_reflection": len(found),
            "nodes_total_all_lengths": nodes_total,
            "seconds": round(time.time() - tk, 2),
            "per_length": per_length,
        }
        print(f"== G({k}) = {L}  optimal rulers (up to reflection): {len(found)}  "
              f"first: {found[0]}  total nodes {nodes_total:,d}  "
              f"{time.time() - tk:.1f}s", flush=True)
        save()
        if time.time() > deadline:
            print("deadline reached after finishing k =", k, flush=True)
            break

    results["meta"]["total_seconds"] = round(time.time() - t_start, 2)
    save()
    if pool is not None:
        pool.terminate()
        pool.join()


if __name__ == "__main__":
    main()
