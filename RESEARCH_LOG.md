# Research log

Erdős Problem #30. All times are local (UTC+8) on Tuesday 24 November 2026 and are taken from file
timestamps and the session record, so they are accurate to a few minutes. Hypotheses, dead ends
and results are listed in the order they happened. Labels: **H** hypothesis, **X** dead end,
**P** Python check, **L** Lean feedback, **R** result.

## 1. Setting up (16:18 to 16:45)

- **16:18** The task was to choose one open Erdős problem with a verified cash prize and a
  Lean 4 statement, attempt it, and publish an honest record.
- **16:20** `git` and `gh` were present and `gh` was logged in. `lean` and `lake` were not
  installed. The user chose a portable install, so elan 4.4.0 went into `Maths problems/.elan`
  with the toolchain `leanprover/lean4:v4.33.1`. Nothing was added to the system `PATH` or the
  registry (checked by taking a before and after snapshot).
- **16:21** Three Lean skills were installed at project scope after the repositories had been
  scanned for lifecycle hooks, remote execution, obfuscation and credential access: `lean4`
  (from `cameronfreer/lean4-skills`), `writing-lean-proofs` (from `trailofbits/skills`) and
  `mathlib-quality` (from `CBirkbeck/mathlib-quality`). A second skill in the last repository,
  `voyager`, posts to a Zulip chat with stored credentials and was not installed. The
  `/lean4:draft`, `/lean4:prove` and `/lean4:review` plugin commands were not installed, since
  they need the plugin form; their markdown was read from the scanned clone and followed by hand:
  state the declaration, prove it, then review it for axioms and style.
- **16:22 to 16:25** Downloaded, for reading only: the community database
  (`teorth/erdosproblems`, `data/problems.yaml`), the problem page and forum thread for #30, the
  OEIS entries A003022, A143824 and A227590, and the formal-conjectures files `30.lean` and
  `Basic.lean`.

## 2. Choosing the problem (16:25 to 16:35)

- **R** The database lists 1221 problems, 109 with a dollar prize, 46 of them informally open.
- **H** #3 ($5000) looked best on prize alone. **X** Its problem page already links an OpenAI
  Lean proof from the October 2026 release, so it is not a clean "open" problem and a second
  attempt would add nothing.
- **R** #30 was chosen. Checked live against the page: open, $1000, "Formalised statement?
  Yes", last edited 6 April 2026. The Lean statement in formal-conjectures reads the question as
  "for every ε > 0, `h N - √N` is `O(N^ε)`", which matches the page.
- **H** Realistic outcome: the prize question is out of reach in a session. A transparent set of
  verified partial results is the honest target. This was decided before any proof attempt.

## 3. Toolchain trouble (16:30 to 17:05)

- **L** `lake` fetched Mathlib and tried to download its pre-built cache. Unpacking the cache
  needs `leantar.exe`, which Windows Application Control blocked (error 4551). It was not worked
  around. The cache process was stopped, the 8,690 `.ltar` files it had already written to
  the user-level cache folder `~/.cache/mathlib` (all created in this session, nothing else in that folder) were
  deleted, `MATHLIB_CACHE_DIR` and `MATHLIB_NO_CACHE_ON_UPDATE` were set for the session, and
  Mathlib is built from source. Running `lake update` again would start the cache download again.
- **L** A full `import Mathlib` needs 8,504 modules built from source. **X** That was started
  and stopped about 16:47 after roughly 330 modules, because the source build was too slow on a
  shared machine. The Lean files now import only the Mathlib modules they use (about 2,000
  modules including dependencies). The first probe was also killed by piping `lake build` into
  `Select-Object -First`, which closes the pipe and stops the build.
- Mathlib is pinned to tag `v4.33.1` (revision `0df444a360ea`), the same revision that
  formal-conjectures uses, so the restated definitions elaborate identically.
- The linter options in `lakefile.toml` were checked against the pinned Mathlib source:
  `linter.style.multiGoal`, `linter.style.show`, `linter.style.setOption` and
  `linter.style.maxHeartbeats` all exist.

## 4. Literature and status research (16:30 to 17:00)

Five subagents ran in parallel. Their notes are summarised here; the sources and the way each was
read are in `REFERENCES.md`.

- **R, upper bound.** `h(N) ≤ √N + N^{1/4} + 1` (Erdős–Turán 1941, Lindström 1969). The error
  coefficient has been lowered only: 0.998 (Balogh–Füredi–Roy), 0.99703 (O'Bryant), 0.98183
  (Carter–Hunter–O'Bryant, the record on the problem page), 0.9435 (Hou–Zhao, arXiv:2607.01169)
  and about 0.945 (Carter–O'Bryant–Tao, arXiv:2610.36207). The last paper proves that its own
  framework cannot give `o(N^{1/4})`. A forum post (unrefereed, not checked) puts the floor of
  these methods at 2√2/3 ≈ 0.9428.
- **R, lower bound.** Singer's and Bose's constructions need a prime power near `√N`, so the
  error in `h(N) ≥ √N - error` is the gap between consecutive prime powers below `√N`, halved in
  the exponent. Baker–Harman–Pintz (gaps `x^{0.525}`) gives error `N^{21/80} = N^{0.2625}`,
  published. Under the Riemann hypothesis gaps are `O(√x log x)` and the error is
  `O(N^{1/4} log N)`. Neither gives `N^ε`; that needs prime gaps below `x^ε`, which is
  Cramér-type and unproved. The deduction that RH gives `N^{1/4} log N` unconditionally for the
  lower half is the research subagent's own, not stated in a source.
- **H** "The Riemann hypothesis helps with #30." **X** Only for the lower half and only down to
  exponent 1/4. The upper half has no known link to zeta zeros. The analogy "main term plus an
  error of size `x^ε`" is loose.
- **Unverified report.** The research subagent reported news and blog pages describing a claimed
  Lean proof of the Riemann hypothesis (20 November 2026). It read these through a
  summarising tool and the primary sources were not opened by anyone. Nothing in this repository
  uses it.
- **R, how AI systems have fared.** Recorded successes are counterexamples built by amplifying a
  small gain (#90, #1), short elementary arguments (#548, #74, #126), syntheses of known methods
  (#571, #1196), literature search, and constant optimisation with exact certificates. Recorded
  failures are rediscovered literature (#333, #481, #707), answers to a vacuous or easier
  question (#124, and 50 of 63 technically correct answers in the Gemini study), and mismatched
  formalisations. Epoch's FrontierMath Erdős list (68 hard open problems) includes #30 and six
  other Sidon problems, and none is reported solved. The best model solved 2 of 68 under the
  protocol and 5 of 68 after about $220,000 of extra compute.
- **R, scouting.** Another prize problem was looked for in case one was easier. None offered a
  realistic prize shot in a few hours (each under 0.1%). The best candidates for a verified
  partial result were #708, #86 and #241, none of which touches a prize question. The decision
  was to stay on #30.
- **Lean status of the known bounds.** In the local copy of `30.lean` the Erdős–Turán,
  Lindström, Balogh–Füredi–Roy, O'Bryant and Carter–Hunter–O'Bryant bounds and Singer's lower
  bound are all `sorry`. The live repository may differ: an open pull request there already
  proves Lindström's bound (see section 7).

## 5. Python checks (16:34 to 17:05)

- **P** `scripts/ogr_search.py`: exhaustive search for G(k), the shortest Golomb ruler with k
  marks, for k up to 13. Values for k = 4 to 13: 6, 11, 17, 25, 34, 44, 55, 72, 85, 106. All agree
  with OEIS A003022. `scripts/brute_force.py`, a second naive implementation, agrees for k up to
  10 including the number of optimal rulers.
- **P** For k = 14 lengths 107 to 114 were ruled out (G(14) ≥ 115; the published value is 127).
  The run was stopped by hand to free the processors for the Mathlib build.
- **P** Exact table of `h(N)`: own search for N = 1 to 115, published A003022 for 116 to 586
  (marked in `results/h_N_data.csv`, not verified here).
- **P** The counting bound `k(k - 1) ≤ 2(N - 1)` and the Lindström bound hold at every N up to
  586. The smallest Lindström margin is 1.2189 at N = 56. The largest `(h - √N) / N^{1/4}` is 0.92
  at N = 56.
- **H** "The data show `h(N) = √N + O(1)`." **X** They do not decide it. The excess `h - √N` at the
  start of each plateau grows slowly (1.54 at k = 5, about 2.7 for k from 12 to 16, about 3.8 at
  k = 26 and 28). Constant, linear-in-k, square-root-in-k and logarithmic fits cannot be
  separated reliably on 24 correlated points.
- **P** `scripts/check_small_h.py`, a separate depth-first subset search, agrees with the CSV for
  every N from 1 to 40. It gives h(1..20) = 1, 2, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 6,
  6, 6.

## 6. Lean feedback (17:09 to 17:42)

Both Lean files were written and read through several times before the first compile, because
Mathlib was still building. The compiler was the first real check.

- **L, 17:24** `Formalization/Problem.lean` built with no errors and no warnings. About 2,000 Mathlib
  modules had been built from source first (roughly 35 to 40 minutes on a shared machine).
- **L, 17:34** First compile of `Formalization/ProofAttempt.lean` (about 610 lines): four errors
  and nine warnings. None of the errors was a flaw in the mathematics: all four came from the
  Lean setup or from how a tactic behaved. They were these.
  1. `omega` failed in `sum_win_card` and `card_pair_win`. `simp only [mem_filter, mem_range,
     mem_Ico, inWin]` unfolded `inWin` inside the filter predicate first, which changed the
     decidability instance, so `mem_filter` then no longer fired and `omega` saw a goal it could
     not read. Fix: rewrite membership first, then `unfold inWin`, then `omega`.
  2. `NoZeroDivisors (ZMod p)` could not be found in `et_core`, although `Fact p.Prime` was in
     scope. The field instance for `ZMod p` lives in `Mathlib.Algebra.Field.ZMod`, which the
     narrowed imports did not reach. Fix: import that module.
  3. `tendsto_rpow_atTop` was unknown: it lives in `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.
     Fix: import that module.
  4. `Asymptotics.isLittleO_one_left_iff` takes the type of the constant as an explicit
     argument. Fix: `(Asymptotics.isLittleO_one_left_iff ℝ).2 hn`.
- **L** The warnings were an unused simp argument, `show` where `change` is meant, three uses of the
  deprecated `push_neg`, and `haveI` where `have` is enough. All were fixed, and an unused
  hypothesis `b < p` was removed from `et_core`.
- **L, 17:40** Clean build of both files. `#print axioms` for `lindstrom_upper`, `erdos_turan_upper`,
  `sqrt_le_three_mul_h`, `conjecture_iff`, `strong_implies_conjecture` and `lower_bound_of_gaps` lists
  `propext`, `Classical.choice` and `Quot.sound` only.
- **L, 17:42** `lake build --wfail` (the command the CI job uses) exits with code 0. A search of
  `Formalization/` finds no `sorry`, `admit`, `native_decide` or extra axiom. The single match for
  the word `sorry` is a sentence in the header comment.
- **L** The seven `example` lines such as `h 4 = 3` are decided by the kernel from the definition of
  `h`, and they agree with the exact Python table.

## 7. Duplication check and the conditional theorem (17:20 to 17:45)

- **R** A subagent searched public repositories for existing Lean work. Pull request 6778 on
  `google-deepmind/formal-conjectures` (opened 1 October 2026, open, awaiting review) already
  proves Lindström's bound with a different, differences-based argument. This was confirmed with
  `gh pr view`; the two proofs were not compared. The Lean proof here is therefore an independent
  write-up of a known result and is not new work.
- **R** `TomasOrtega/Sidon` (Apache-2.0) was reported to prove the Bose–Chowla construction. Only
  its licence and description were checked. Two GPL-3.0 repositories on Singer's theorem were
  reported by the subagent and not checked.
- **H** "Singer's theorem can be added to this repository." **X** Not attempted. The construction
  needs a finite-field argument that is a project of its own, and a Lean proof would copy or
  duplicate work that others have already published.
- **R** `lower_bound_of_gaps` records the exact dependence of the lower half on prime gaps. If
  every `x ≥ 1` has a prime power in `[x - C x^θ, x]` and Singer's theorem holds, then
  `h N ≥ √N - C' N^(θ/2)` for `N ≥ 4`. The two hypotheses are definitions in the file
  (`SingerConstruction`, `PrimePowerGaps`), not axioms, so nothing unproved is assumed.

## 8. Audit

What is proved, with the Lean name, and what is not.

| Claim | Lean name | Status |
| --- | --- | --- |
| `h N ≤ √N + N^(1/4) + 1` for every `N` | `lindstrom_upper` | Proved. Known result, also in an open pull request elsewhere |
| `h N ≤ √N + 2 N^(1/4)` for `N ≥ 1` | `erdos_turan_upper` | Proved, follows from the line above. Known |
| `N ≤ (3 h N)²` for every `N` | `sqrt_le_three_mul_h` | Proved. Known; the constant is not optimal |
| `h N ≤ 3 √N` for `N ≥ 1` | `h_le_three_sqrt` | Proved, a corollary |
| Problem #30 ↔ upper half ∧ lower half | `conjecture_iff` | Proved. Only a restatement |
| `h N = √N + O(1)` implies Problem #30 | `strong_implies_conjecture` | Proved. Trivial |
| Singer's theorem and prime gaps give `√N - C N^(θ/2) ≤ h N` | `lower_bound_of_gaps` | Proved as a conditional theorem. The hypotheses are not proved |
| The upper half, the lower half, or Problem #30 itself | `UpperHalf`, `LowerHalf`, `Conjecture` | **Not proved.** Defined, not asserted |
| Singer's or Bose's construction | none | Not formalised here |
| Any improvement of a known bound | none | None |

Nothing here advances the prize question. The only new thing is the combination: a self-contained,
warning-free Lean file that proves the upper bound at the `N^{1/4}` scale and records which two
open statements the problem splits into.

## 9. Publishing (17:45 onwards)

- **R** Secret scan of the repository (access tokens, key blocks, the owner's name, address and
  local paths): no matches. The commit identity is the GitHub no-reply address, set for this
  repository only.
- The scratch Lean files and the subagents' notes were moved out of the repository into the
  author's working folder and are not published.
- **L, about 17:50** The repository was created as public and the first commit pushed. The GitHub
  job (`lean-action` with `--wfail`, hosted Ubuntu runner, Mathlib cache) finished with success.
