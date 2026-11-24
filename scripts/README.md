# Python scripts

All scripts use only the Python 3 standard library. Run them with `python -I` from inside this
folder, so that nothing is imported from the current directory.

| Script | What it does |
| --- | --- |
| `ogr_search.py` | Exhaustive search for the length G(k) of the shortest Golomb ruler with k marks (equivalently, the smallest N for which a Sidon set of size k fits in {0,…,N}). Bitset depth-first search with iterative deepening and a worker pool. |
| `brute_force.py` | A second, naive implementation (sets of differences, no bitsets, no length bound, no symmetry). Used as a cross-check for k up to 10. |
| `analyse.py` | Turns the lengths G(k) into the exact table h(N) = max{k : G(k) + 1 ≤ N} and tests the counting bound and the Lindström bound at every N. Needs the OEIS JSON files for A003022, A143824 and A227590 in a folder given by `--oeis-dir`; they are not copied into this repository (download them from <https://oeis.org>). |
| `finalize_stopped_run.py` | Records how far a k = 14 run got when it was stopped by hand. |
| `check_small_h.py` | Independent subset search for h(N) with N up to 40, compared with `results/h_N_data.csv`. |

The outputs are in `../results/`.

## What was established

- G(k) for every k up to 13, by exhaustive search: 6, 11, 17, 25, 34, 44, 55, 72, 85, 106 for
  k = 4 to 13. These agree with OEIS A003022. The naive implementation agrees for k up to 10,
  including the number of optimal rulers.
- For k = 14 the search ruled out lengths 107 to 114, so G(14) ≥ 115. The published value is 127.
  The run was stopped by hand, and nothing from the unfinished length 115 is used.
- The table of exact values of h(N) that this repository computed itself therefore covers
  N = 1 to 115. In `results/h_N_data.csv` the rows for N = 116 to 586 come from the published
  A003022 (k up to 28, G(28) = 585) and are marked in the `source` column. They were not
  verified here.
- The counting bound k(k − 1) ≤ 2(N − 1) and the Lindström bound h(N) ≤ √N + N^{1/4} + 1 hold at
  every N from 1 to 586. The smallest Lindström margin is 1.2189, at N = 56.

## What the numbers say about the problem

Write e(N) = h(N) − √N. At the first N of each plateau, e is 1.54 for k = 5, about 2.7 for k = 12
to 16, and about 3.8 for k = 26 and 28. The largest value of e(N) / N^{1/4} is 0.92, at N = 56, and
it drifts down slowly. A constant fits these plateau values worse than slowly growing curves such
as a line in k or in log k, but the growing curves cannot be told apart from each other. Data up
to 28 marks cannot decide whether h(N) = √N + O(1), and they say nothing about the exponent
question that the prize problem asks.

## Caveats

- The search code is not formally verified. Its correctness rests on agreement with A003022 for
  k = 2 to 13, with the naive implementation for k up to 10, and on a separate re-check of every
  ruler found.
- Each k uses the lengths G(m), m < k, proved earlier by the same program, so an error would
  propagate upward. Agreement with the published values at every k makes a hidden error unlikely
  but is not a proof.
- Run times were measured on a shared machine and are not benchmark quality.

## Reproducing

```text
python -I ogr_search.py --k-max 16 --workers 14 --out ogr_results.json --deadline-seconds 1700 > ogr_search.log
python -I brute_force.py --k-max 11 --out brute_force_results.json --deadline-seconds 900 > brute_force.log
python -I finalize_stopped_run.py ogr_search.log ogr_results.json
python -I analyse.py --own ogr_results.json --brute brute_force_results.json --oeis-dir <folder with the OEIS JSON files> --outdir . --controls ogr_results_control_serial_k11.json ogr_results_control_parallel_k12.json
python -I check_small_h.py
```

These are the commands that produced the files in `../results/`. Change the paths if you run them
from another folder.
