# Erdős Problem #30: an attempt, with Lean 4 partial results

This repository records an attempt on [Erdős Problem #30](https://www.erdosproblems.com/30), a
$1000 prize problem about the largest Sidon set in {1, …, N}.

**The problem is not solved here.** Nothing in this repository proves or disproves it, and nothing
here is a new mathematical result. What the repository holds is a set of known results written out
in Lean 4 and checked by the kernel, exact computer searches for small N, and a written account of
why the problem looks out of reach. The sections "Status" and "What is not done" give the exact
state.

## The problem

Let h(N) be the maximum size of a Sidon set in {1, …, N}. Is it true that, for every ε > 0,

$$h(N) = N^{1/2} + O_\epsilon(N^{\epsilon})\ ?$$

In plain English: a Sidon set is a set of whole numbers in which every sum a + b of two members
(with a ≤ b) is different from every other such sum. Equivalently, all differences between members
are different. h(N) is the size of the biggest Sidon set that fits inside 1 to N. Counting
differences shows h(N) is close to √N. The question is whether the gap between h(N) and √N is
smaller than every positive power of N. Erdős remarked that h(N) = √N + O(1) might even hold, but
thought that perhaps too optimistic.

- Prize: $1000, offered by Erdős. The site's FAQ says prizes are paid only after publication in a
  reputable journal.
- Status on erdosproblems.com: open (page last edited 6 April 2026, read on 24 November 2026).
- The Lean statement in `Formalization/Problem.lean` restates `erdos_30` from the Google DeepMind
  `formal-conjectures` repository, with the same definitions. It is a `def`, not a theorem,
  because the problem is open.

## Why this problem

It was open, carried a verified cash prize, had a Lean statement, and was not already claimed.
Problem #3 ($5000) was rejected because its page already links an AI-generated Lean proof
from October 2026 that no human has yet digested. A scouting pass over the other open prize
problems found none with a realistic chance of a prize-level result in a few hours, so #30 was
kept.

## What is known

- **Upper bound.** h(N) ≤ √N + N^{1/4} + 1 (Erdős–Turán 1941, Lindström 1969). Later work lowered
  only the constant in front of N^{1/4}: 0.998 (Balogh–Füredi–Roy), 0.99703 (O'Bryant), 0.98183
  (Carter–Hunter–O'Bryant, the record on the problem page), 0.9435 (Hou–Zhao, 2026) and about
  0.945 (Carter–O'Bryant–Tao, 2026). The last paper proves that its own method cannot give
  o(N^{1/4}).
- **Lower bound.** Singer (1938) gives h(N) ≥ (1 − o(1))√N. The size of the error depends on gaps
  between prime powers just below √N. With Baker–Harman–Pintz the error is N^{21/80} ≈ N^{0.2625}.
  If the Riemann hypothesis holds, the same argument gives N^{1/4} log N. Getting N^ε would need
  prime gaps smaller than x^ε, which is a Cramér-type statement that is not known, even under the
  Riemann hypothesis.

So each half of the problem is stuck at exponent about 1/4, for separate reasons. Reaching "every
ε > 0" would need two independent breakthroughs. The sources, and how each was read, are in
`REFERENCES.md`.

## Status

| Item | Status |
| --- | --- |
| Erdős Problem #30 (the prize question) | Open. Not solved, not advanced. |
| h(N) ≤ √N + N^{1/4} + 1 for every N (Lindström) | Proved in Lean, no `sorry`. A known result, and already in an open formal-conjectures pull request, so this is an independent write-up. |
| h(N) ≤ √N + C N^{1/4} for large N (Erdős–Turán) | Proved in Lean, as a corollary of the line above. Known. |
| √N ≤ 3 h(N) for every N | Proved in Lean (Erdős–Turán construction with Bertrand's postulate). Known; the constant 3 is not optimal. |
| #30 is equivalent to an upper half and a lower half | Proved in Lean (`conjecture_iff`). |
| h(N) = √N + O(1) would imply #30 | Proved in Lean (`strong_implies_conjecture`). Trivial. |
| Lower half from Singer's theorem and prime gaps | Proved in Lean as a conditional theorem (`lower_bound_of_gaps`). Singer's theorem and the gap bounds are hypotheses, not formalised. |
| Exact h(N) | Computed by exhaustive search for N = 1 to 115. Table to 586 uses published OEIS data. |

The exact Lean state is given under "Checking the Lean files" below. The audit in
`RESEARCH_LOG.md` (section 8) lists every Lean name next to what it does and does not prove.

## What is not done

- No improvement to any bound, in the exponent or in a constant.
- Singer's and Bose's constructions are not formalised, so the lower bound with constant 1 − o(1)
  is not proved in Lean. The lower bound proved here has constant 1/3.
- The Balogh–Füredi–Roy, O'Bryant, Carter–Hunter–O'Bryant, Hou–Zhao and Carter–O'Bryant–Tao
  constants are not formalised.
- No Lean proof of anything about N^ε.
- The Lean proof of Lindström's bound is not the first one. Pull request 6778 on
  `google-deepmind/formal-conjectures` (open, awaiting review) already contains one. The two
  proofs were not compared.
- The Python search for k = 14 marks was stopped before it finished, so the exact table of h(N)
  computed here stops at N = 115.

## Approach

1. Check the statement against the problem page, quantifier by quantifier, and against
   formal-conjectures.
2. Collect the literature and check what is already formalised. In the local copy of the
   formal-conjectures file for #30 the upper bounds and Singer's bound are all `sorry`.
3. Compute. Exhaustive search for optimal Golomb rulers gives h(N) exactly for small N (see
   `scripts/` and `results/`). The data stay below the Lindström bound everywhere, and the excess
   h(N) − √N grows slowly. Finite data cannot settle h(N) = √N + O(1).
4. Prove in Lean the parts that are elementary and well known, using the window-counting argument
   for the upper bound and the Erdős–Turán construction for the lower bound.
5. Write down, in Lean, exactly what the open problem splits into, so that a future attempt can
   see which half it is aiming at.

The proof of Lindström's bound counts, for a Sidon set A in {1, …, N} with |A| = k and a window
length u, how many elements of A lie in each of the N + u − 1 windows of u consecutive integers.
Distinct differences limit how many pairs share a window, and the Cauchy–Schwarz inequality then
gives k²u ≤ (k + u − 1)(N + u − 1). Choosing u close to N^{3/4} gives k ≤ √N + N^{1/4} + 1.

## Layout

| Path | Contents |
| --- | --- |
| `Formalization/Problem.lean` | The exact statement of #30, its negation, the strong form, and the known bounds as `Prop` definitions |
| `Formalization/ProofAttempt.lean` | The Lean proofs listed under "Status" |
| `scripts/` | Python scripts for the exact computations, with their own `README.md` |
| `results/` | Output of those scripts, including `h_N_data.csv` |
| `RESEARCH_LOG.md` | Timestamped hypotheses, dead ends, Python checks and Lean feedback |
| `REFERENCES.md` | Sources, and how each was read |

## Building

The Lean files need the toolchain named in `lean-toolchain` (Lean 4.33.1) and Mathlib at tag
`v4.33.1`. With [elan](https://github.com/leanprover/elan) installed:

```text
lake build
```

On a machine where Mathlib's prebuilt cache can be unpacked, run `lake exe cache get` first and
the build takes a few minutes. This repository was built on a Windows machine whose Application
Control policy blocked the cache unpacker, so Mathlib was built from source, which took roughly
35 to 40 minutes. The Lean files import only the Mathlib modules they use (about 2,000 modules
including dependencies instead of the 8,500 that `import Mathlib` needs), which keeps that build
short. A change that adds a Mathlib import may need the cache or a longer build.

The Python scripts need Python 3 and nothing else. See `scripts/README.md`.

## Checking the Lean files

`lake build` must finish with no errors and no warnings. The continuous-integration job in
`.github/workflows/lean_action_ci.yml` builds with `--wfail`, so a `sorry` or any warning fails
the job. `Formalization/ProofAttempt.lean` ends with `#print axioms` lines for the main theorems;
they must list only `propext`, `Classical.choice` and `Quot.sound`.

Result on 24 November 2026, Lean 4.33.1 with Mathlib `v4.33.1`, on the author's machine:
`lake build --wfail` exits with code 0, there are no warnings, the files contain no `sorry`,
`admit` or `native_decide`, and each `#print axioms` line lists only those three axioms. The
GitHub job has not been looked at yet, so the first CI run on the hosted runner is unchecked.

## Licence

No licence file has been added yet. `Formalization/Problem.lean` restates definitions from
`google-deepmind/formal-conjectures`, which is licensed under Apache-2.0, so Apache-2.0 is the
natural choice for this repository.
