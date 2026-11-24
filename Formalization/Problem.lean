/-
Erdős Problem #30: the formal statement.

The definitions below are re-stated, with the same bodies, from the Google DeepMind
`formal-conjectures` repository (Apache-2.0):
  * `FormalConjecturesForMathlib/Combinatorics/Basic.lean`  (`IsSidon`, `maxSidonSubsetCard`)
  * `FormalConjectures/ErdosProblems/30.lean`               (`h`, `erdos_30` and its variants)
They are copied rather than imported so that this repository builds on Mathlib alone. Only the
Mathlib modules this file needs are imported, which keeps a from-source build short.
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset

open Filter
open scoped Asymptotics

namespace Erdos30

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set: all pairwise sums are distinct, apart from the coincidences forced by
commutativity of addition. -/
def IsSidon (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The maximum size of a Sidon set contained in the finset `A`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

/-- `h N` is the maximum size of a Sidon set contained in `{1, …, N}`. -/
abbrev h (N : ℕ) : ℕ := maxSidonSubsetCard (Finset.Icc 1 N)

/-- **Erdős Problem #30** (prize: $1000), as a proposition.

Source wording (erdosproblems.com/30, accessed 2026-11-24): "Let $h(N)$ be the maximum size of a
Sidon set in $\{1,\ldots,N\}$. Is it true that, for every $\epsilon>0$,
$h(N) = N^{1/2}+O_\epsilon(N^\epsilon)$?"

Reading of the quantifiers: for every real `ε > 0` there are constants `C` and `N₀` with
`|h N - √N| ≤ C * N ^ ε` for all `N ≥ N₀`. This is the `=O[atTop]` statement below, and it matches
`Erdos30.erdos_30` in `formal-conjectures`.

This is a `def`, not a `theorem`: the problem is open, and nothing in this repository claims a
proof or a disproof of it. -/
def Conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ ↦ (h N : ℝ) - Real.sqrt N) =O[atTop] fun N : ℕ ↦ (N : ℝ) ^ ε

/-- The negation of `Conjecture`, i.e. what a disproof would have to establish: some `ε > 0` for
which the error `h N - √N` is not `O(N ^ ε)`. -/
def NegatedConjecture : Prop := ¬ Conjecture

/-- Erdős considered this stronger form "perhaps too optimistic": `h N = √N + O(1)`. -/
def StrongConjecture : Prop :=
  (fun N : ℕ ↦ (h N : ℝ) - Real.sqrt N) =O[atTop] fun _ ↦ (1 : ℝ)

/-- Upper bound of Erdős and Turán (1941): `h N ≤ √N + C * N ^ (1/4)` for large `N`. -/
def ErdosTuranUpper : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (h N : ℝ) ≤ Real.sqrt N + C * (N : ℝ) ^ (4⁻¹ : ℝ)

/-- Lindström's form (1969): `h N ≤ √N + N ^ (1/4) + 1` for every `N`. -/
def LindstromUpper : Prop :=
  ∀ N : ℕ, (h N : ℝ) ≤ Real.sqrt N + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

/-- Singer (1938): `h N ≥ (1 - o(1)) √N`. -/
def SingerLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 - ε) * Real.sqrt N ≤ h N

end Erdos30
