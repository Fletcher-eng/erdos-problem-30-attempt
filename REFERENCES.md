# References

Every source used for this repository, with how it was read. The column "How read" matters: a
result that was only seen in an abstract or through a summarising fetch tool has not been checked
by the author of this repository.

Labels: **full text** means the PDF or page was downloaded and read. **Abstract or summary** means
only the abstract page, or a summary produced by a fetch tool, was seen. **Cited, not opened** means
the problem page or another source cites the work and nothing more was read.

## The problem

| Source | What it gives | How read |
| --- | --- | --- |
| T. F. Bloom, *Erdős Problem #30*, <https://www.erdosproblems.com/30>, accessed 24 November 2026 (page last edited 6 April 2026) | Statement, prize ($1000), status (open), list of known bounds, links to OEIS A143824, A227590, A003022 | Full text (raw HTML) |
| Forum thread for #30 on erdosproblems.com | Unrefereed comments on the current constant (0.9428 to 0.9433) and exact values of h(N) | Full text, treated as unrefereed |
| Community database `teorth/erdosproblems`, `data/problems.yaml` | Status and prize fields for all 1221 problems | Full text, used to confirm that #30 is open with a $1000 prize |
| `google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/30.lean` and `FormalConjecturesForMathlib/Combinatorics/Basic.lean` (Apache-2.0) | The Lean statement `erdos_30`, the definitions `IsSidon` and `maxSidonSubsetCard`, which `Formalization/Problem.lean` restates | Full text (local copy) |
| OEIS [A003022](https://oeis.org/A003022), [A143824](https://oeis.org/A143824), [A227590](https://oeis.org/A227590) | Optimal Golomb ruler lengths, and the exact maximum size of a Sidon set in {1,…,n} | JSON downloaded, used to cross-check `scripts/` |

## Upper bounds on h(N)

| Source | Result | How read |
| --- | --- | --- |
| P. Erdős and P. Turán, "On a problem of Sidon in additive number theory and on some related problems", J. London Math. Soc. 16 (1941), 212–215 | h(N) ≤ N^{1/2} + O(N^{1/4}) | Cited on the problem page, not opened |
| B. Lindström, "An inequality for B₂-sequences", J. Combin. Theory 6 (1969), 211–212 | Alternative proof, h(N) ≤ N^{1/2} + N^{1/4} + 1 | Cited on the problem page, not opened. The proof formalised in this repository is the standard window-counting argument, written out again by the author and not copied from this paper |
| J. Balogh, Z. Füredi and S. Roy, "An upper bound on the size of Sidon sets", arXiv:2103.15850 | Error term 0.998 N^{1/4} | Full text |
| K. O'Bryant, "On the size of finite Sidon sets", arXiv:2207.07800 | Error term 0.99703 N^{1/4} | Abstract or summary |
| T. Carter, Z. Hunter and K. O'Bryant, "On the diameter of finite Sidon sets", arXiv:2310.20032 | Error term 0.98183 N^{1/4} + O(1), the record shown on the problem page | Full text |
| Hou and Zhao, arXiv:2607.01169 (v3) | Error term 0.9435 N^{1/4}, exact rational certificate | Full text |
| Carter, O'Bryant and Tao, arXiv:2610.36207 | Error term about 0.945 N^{1/4} and a proof that the method cannot give o(N^{1/4}) | Full text |

The two newest papers are more recent than the problem page, which still shows 0.98183.

## Lower bounds on h(N) and prime gaps

| Source | Result | How read |
| --- | --- | --- |
| J. Singer, "A theorem in finite projective geometry and some applications to number theory", Trans. Amer. Math. Soc. 43 (1938), 377–385 | For a prime power q there is a Sidon set of q + 1 elements below q² + q + 1 | Cited on the problem page, not opened |
| R. C. Bose, 1942, and S. Chowla, 1944 | Affine analogue of Singer's theorem, and the link between prime gaps and the error term in the lower bound | Seen only as described in the O'Bryant survey |
| K. O'Bryant, "A complete annotated bibliography of work related to Sidon sequences", arXiv:math/0407117, Electron. J. Combin. Dynamic Survey DS11 (2004 version) | Survey of the field, including the Erdős–Turán construction `{2pk + (k² mod p)}` and the dependence of the lower-bound error on prime gaps | Full text |
| R. C. Baker, G. Harman and J. Pintz, Proc. London Math. Soc. 83 (2001), 532–562 | A prime in [x − x^{0.525}, x] for large x, so the lower-bound error is O(N^{21/80}) | Journal reference confirmed from the introduction of Hou and Zhao. Proof not opened |
| H. Cramér, Acta Arith. 2 (1936), 23–46 | Under the Riemann hypothesis prime gaps near x are O(√x log x) | Cited by Wikipedia, not opened |
| R. Li, arXiv:2308.04458 | Prime gap exponent 0.52, so error N^{0.26} | Abstract or summary. Unrefereed, proof not checked |

## Existing Lean work found by the duplication search

| Source | What it holds | How read |
| --- | --- | --- |
| Pull request 6778 on `google-deepmind/formal-conjectures`, "prove Lindström's bound for Sidon sets and record it on `erdos_30.variants.lindstrom`" (opened 1 October 2026, still open and awaiting review on 24 November 2026) | A Lean proof of `h N ≤ √N + N^{1/4} + 1`, using a differences-based argument. It changes `30.lean` and adds `FormalConjecturesForMathlib/Combinatorics/Sidon/Lindstrom.lean` | Title, state and file list read with `gh pr view`. The proof itself was not opened, so the two proofs have not been compared |
| `TomasOrtega/Sidon` (Apache-2.0, last updated 29 October 2026) | A Lean project on Sidon sets. A research subagent reported that it proves the Bose–Chowla construction for every prime `p` | Licence and description confirmed with `gh repo view`. The content of the proof was not opened |
| Two further public Lean repositories on Singer's theorem (GPL-3.0), and a Mathlib change that adds a prime-in-an-interval lemma (reported as merged 11 November 2026) | Singer's theorem in Lean is not in the pinned Mathlib | Reported by a subagent. Not checked |

So the Lean proof of Lindström's bound in this repository repeats work that already exists in an
open pull request. It is an independent write-up of a known result and makes no claim to be the
first.

## Mathlib results used in the Lean files

Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), Cauchy–Schwarz for finite sums
(`sq_sum_le_card_mul_sum_sq`), the integer square root lemmas `Nat.sqrt_le'` and
`Nat.lt_succ_sqrt'`, and the field structure of `ZMod p`. Mathlib revision `0df444a360ea` (tag
`v4.33.1`).

## How AI systems have been used on Erdős problems

These were read to decide what kind of contribution is realistic. None of them is used in the
mathematics.

| Source | How read |
| --- | --- |
| Epoch AI, "FrontierMath: Erdős", arXiv:2609.25050 | Full text. Lists #30 among 68 hard open problems and reports no Sidon-set problem solved |
| Gemini case study on about 700 open problems, arXiv:2601.22401 | Abstract or summary |
| Barreto, "Problem 728 and the use of AI on Erdős problems", erdosproblems.com blog | Full text |
| Bloom, "Sum-product, unit distances, and number fields", erdosproblems.com blog | Full text, first 120 lines |
| `teorth/erdosproblems` wiki pages on AI contributions | Abstract or summary |

Fuller notes, with the status of each claim, are in the author's working folder under
`research-notes/` and are summarised in `RESEARCH_LOG.md`.

## Claims that were reported to the author and not verified

- A report that a Lean proof of the Riemann hypothesis was announced on 20 November 2026. It came
  from a research subagent reading news and blog pages through a summarising tool. The author did
  not open the primary sources and does not rely on it anywhere in this repository.
- An unrefereed forum post that the method behind the current N^{1/4} records has a floor at
  2√2/3 ≈ 0.9428. Hou–Zhao and Carter–O'Bryant–Tao do not state this.
- A forum claim of exact values of h(N) for N up to 586.
