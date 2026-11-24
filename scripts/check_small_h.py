"""Independent small-N check of h(N), the largest Sidon subset of {1..N}.

Plain depth-first search over subsets, written separately from ogr_search.py. It is
meant to agree with results/h_N_data.csv and with the `decide` examples in
Formalization/ProofAttempt.lean. Run: python -I scripts/check_small_h.py
"""
import csv
import os

def h(n):
    best = 0
    def extend(chosen, sums, start):
        nonlocal best
        best = max(best, len(chosen))
        for x in range(start, n + 1):
            new = [x + c for c in chosen] + [2 * x]
            if len(set(new)) == len(new) and not (set(new) & sums):
                extend(chosen + [x], sums | set(new), x + 1)
    extend([], set(), 1)
    return best

here = os.path.dirname(os.path.abspath(__file__))
csv_path = os.path.join(here, "..", "results", "h_N_data.csv")
with open(csv_path, newline="") as f:
    rows = {int(r["N"]): int(r["h"]) for r in csv.DictReader(f)}

bad = 0
for n in range(1, 41):
    mine = h(n)
    if mine != rows[n]:
        bad += 1
        print("MISMATCH at N =", n, "search =", mine, "csv =", rows[n])
print("checked N = 1..40, mismatches:", bad)
print("h(1..20) =", [h(n) for n in range(1, 21)])
