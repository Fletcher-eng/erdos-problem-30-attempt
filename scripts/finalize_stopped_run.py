#!/usr/bin/env python3
"""
finalize_stopped_run.py -- record the partial k=14 result of a run that was stopped by hand.

The main run (ogr_search.py --k-max 16 ...) was killed at the coordinator's request while it
was inside k = 14 (to free the CPUs).  ogr_search.py only writes its JSON after finishing a
whole k, so the lengths already ruled out for k = 14 exist only as log lines.  A log line
"[k=14] L=... rulers=0" is printed only after that length has been searched COMPLETELY, so
the lengths listed with rulers=0 are really ruled out.  This script copies them into
ogr_results.json as the "incomplete" record (same fields ogr_search.py writes on a deadline),
so analyse.py can use them.

Run as:  python -I finalize_stopped_run.py ogr_search.log ogr_results.json
"""
import json
import re
import sys

log_path, json_path = sys.argv[1], sys.argv[2]
res = json.load(open(json_path))
k_done = max(int(k) for k in res["G"])
k_next = k_done + 1
pat = re.compile(r"^\[k=%d\] L=\s*(\d+) nodes=\s*([\d,]+) rulers=(\d+)" % k_next)
done = []
for line in open(log_path):
    m = pat.match(line)
    if m:
        done.append((int(m.group(1)), int(m.group(2).replace(",", "")), int(m.group(3))))
assert done, "no k=%d lines in log" % k_next
assert all(r == 0 for _, _, r in done), "a ruler was found - not a pure lower-bound record"
Ls = [L for L, _, _ in done]
assert Ls == list(range(Ls[0], Ls[-1] + 1)) and Ls[0] == res["G"][str(k_done)] + 1
ruled_out_below = Ls[-1] + 1            # every length <= Ls[-1] is empty
res["incomplete"] = {
    "k": k_next,
    "lengths_fully_ruled_out_below": ruled_out_below,
    "meaning": "no %d-mark Golomb ruler has length < %d (lengths %d..%d each searched "
               "exhaustively, 0 rulers).  Run stopped by hand during length %d; "
               "G(%d) is NOT determined." % (k_next, ruled_out_below, Ls[0], Ls[-1],
                                              ruled_out_below, k_next),
    "stopped_by_hand": True,
    "nodes_in_completed_lengths": sum(n for _, n, _ in done),
}
res["meta"]["stopped_by_hand"] = (
    "Run killed during k=%d at the coordinator's request; total_seconds not recorded by the "
    "program (see ogr_search.log for per-length timings)." % k_next)
with open(json_path, "w") as f:
    json.dump(res, f, indent=1, sort_keys=True)
print(res["incomplete"])
