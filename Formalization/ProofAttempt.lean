/-
Erdős Problem #30: what is proved here.

Nothing in this file proves or disproves Erdős Problem #30. The file contains Lean proofs of
known results about `h N`, the largest size of a Sidon set in `{1, …, N}`, together with a
precise split of the problem into two halves. Every theorem is proved with no `sorry`, and each
`#print axioms` line at the end shows only `propext`, `Classical.choice` and `Quot.sound`.

Contents
* `lindstrom_upper`        : `h N ≤ √N + N^(1/4) + 1` for every `N` (Lindström 1969).
* `erdos_turan_upper`      : the Erdős–Turán form `h N ≤ √N + C N^(1/4)` (1941).
* `sqrt_le_three_mul_h`    : `√N ≤ 3 h N` for every `N`, via the Erdős–Turán construction
                              `k ↦ 2pk + (k² mod p)` and Bertrand's postulate. (The constant 3 is
                              not optimal; Singer's construction gives `1 - o(1)`, not formalised.)
* `conjecture_iff`         : Problem #30 is the conjunction of an upper half and a lower half.
* `strong_implies_conjecture` : `h N = √N + O(1)` would imply Problem #30.
* `lower_bound_of_gaps`     : conditional on Singer's theorem (a hypothesis, not proved here) and
                              a prime-power gap bound, `h N ≥ √N - C N^(θ/2)`.
-/
import Formalization.Problem
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.IsPrimePow

open Finset

namespace Erdos30


/-! ### Extremal sets -/

lemma card_le_h {N : ℕ} {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 N) (hS : IsSidon (B : Set ℕ)) :
    B.card ≤ h N :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hB, hS⟩)

lemma exists_extremal (N : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 N ∧ IsSidon (B : Set ℕ) ∧ B.card = h N := by
  have hne : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by intro i hi; simp at hi⟩⟩
  obtain ⟨B, hB, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, hsup.symm⟩

lemma h_mono {N M : ℕ} (hNM : N ≤ M) : h N ≤ h M := by
  obtain ⟨B, hB, hS, hc⟩ := exists_extremal N
  rw [← hc]
  exact card_le_h (hB.trans (Finset.Icc_subset_Icc_right hNM)) hS

lemma h_zero : h 0 = 0 := by
  obtain ⟨B, hB, -, hc⟩ := exists_extremal 0
  have hE : B = ∅ := by simpa using hB
  rw [hE, Finset.card_empty] at hc
  exact hc.symm

/-! ### Window counting -/

/-- Window `s` (a block of `u` consecutive integers) contains `a` iff `s - u + 2 ≤ a ≤ s + 1`. -/
def inWin (u s a : ℕ) : Prop := a ≤ s + 1 ∧ s + 2 ≤ a + u

instance (u s a : ℕ) : Decidable (inWin u s a) := by unfold inWin; infer_instance

/-- Number of windows containing both `a` and `b`, in closed form. -/
def pairW (u a b : ℕ) : ℕ := (min a b + u - 1) - (max a b - 1)

lemma pairW_comm (u a b : ℕ) : pairW u a b = pairW u b a := by
  simp [pairW, min_comm, max_comm]

lemma sum_win_card {A : Finset ℕ} {N u : ℕ} (hA : A ⊆ Finset.Icc 1 N) (hu : 1 ≤ u) :
    ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card = A.card * u := by
  have key : ∀ a ∈ A, ((range (N + u - 1)).filter (fun s => inWin u s a)).card = u := by
    intro a ha
    have h1 := Finset.mem_Icc.1 (hA ha)
    have : (range (N + u - 1)).filter (fun s => inWin u s a) = Ico (a - 1) (a + u - 1) := by
      ext s
      simp only [mem_filter, mem_range, mem_Ico]
      unfold inWin
      omega
    rw [this, Nat.card_Ico]
    omega
  calc ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card
      = ∑ s ∈ range (N + u - 1), ∑ a ∈ A, if inWin u s a then 1 else 0 := by
        apply sum_congr rfl
        intro s _
        rw [card_filter]
    _ = ∑ a ∈ A, ∑ s ∈ range (N + u - 1), if inWin u s a then 1 else 0 := sum_comm
    _ = ∑ a ∈ A, u := by
        apply sum_congr rfl
        intro a ha
        have := key a ha
        rw [card_filter] at this
        exact this
    _ = A.card * u := by simp

lemma card_sq_win (A : Finset ℕ) (u s : ℕ) :
    (A.filter (inWin u s)).card ^ 2
      = ∑ a ∈ A, ∑ b ∈ A, if inWin u s a ∧ inWin u s b then 1 else 0 := by
  rw [sq, card_filter, sum_mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases ha : inWin u s a <;> by_cases hb : inWin u s b <;> simp [ha, hb]

lemma card_pair_win {A : Finset ℕ} {N u : ℕ} (hA : A ⊆ Finset.Icc 1 N) (hu : 1 ≤ u)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    ((range (N + u - 1)).filter (fun s => inWin u s a ∧ inWin u s b)).card = pairW u a b := by
  have h1 := Finset.mem_Icc.1 (hA ha)
  have h2 := Finset.mem_Icc.1 (hA hb)
  have : (range (N + u - 1)).filter (fun s => inWin u s a ∧ inWin u s b)
      = Ico (max a b - 1) (min a b + u - 1) := by
    ext s
    simp only [mem_filter, mem_range, mem_Ico]
    unfold inWin
    omega
  rw [this, Nat.card_Ico, pairW]

/-- A symmetric double sum splits into the diagonal and twice the strict upper triangle. -/
lemma sum_sym_split (A : Finset ℕ) (w : ℕ → ℕ → ℕ) (hw : ∀ a b, w a b = w b a) :
    ∑ a ∈ A, ∑ b ∈ A, w a b
      = ∑ a ∈ A, w a a + 2 * ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), w a b := by
  have key : ∀ a b, w a b = (if a < b then w a b else 0) + (if b < a then w a b else 0)
      + (if a = b then w a b else 0) := by
    intro a b
    split_ifs <;> omega
  have e2 : (∑ a ∈ A, ∑ b ∈ A, if b < a then w a b else 0)
      = ∑ a ∈ A, ∑ b ∈ A, if a < b then w a b else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [hw a b]
  have e3 : (∑ a ∈ A, ∑ b ∈ A, if a = b then w a b else 0) = ∑ a ∈ A, w a a := by
    apply sum_congr rfl
    intro a ha
    rw [sum_ite_eq A a (fun b => w a b)]
    simp [ha]
  have e4 : (∑ a ∈ A, ∑ b ∈ A, if a < b then w a b else 0)
      = ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), w a b := by
    apply sum_congr rfl
    intro a _
    rw [sum_filter]
  calc ∑ a ∈ A, ∑ b ∈ A, w a b
      = ∑ a ∈ A, ∑ b ∈ A, ((if a < b then w a b else 0) + (if b < a then w a b else 0)
          + (if a = b then w a b else 0)) :=
        sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => key a b))
    _ = (∑ a ∈ A, ∑ b ∈ A, if a < b then w a b else 0)
        + (∑ a ∈ A, ∑ b ∈ A, if b < a then w a b else 0)
        + ∑ a ∈ A, ∑ b ∈ A, if a = b then w a b else 0 := by
        simp only [sum_add_distrib]
    _ = ∑ a ∈ A, w a a + 2 * ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), w a b := by
        rw [e2, e3, e4]
        ring

/-- Gauss: `2 * (1 + 2 + ... + (u - 1)) = u * (u - 1)`, written as a sum of `u - d`. -/
lemma gauss (u : ℕ) : 2 * ∑ d ∈ Ico 1 u, (u - d) = u * (u - 1) := by
  induction u with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [sum_Ico_succ_top hn]
      have e : ∑ d ∈ Ico 1 n, (n + 1 - d) = ∑ d ∈ Ico 1 n, (n - d) + (n - 1) := by
        have : ∀ d ∈ Ico 1 n, n + 1 - d = (n - d) + 1 := by
          intro d hd
          rw [mem_Ico] at hd
          omega
        rw [sum_congr rfl this, sum_add_distrib]
        simp
      rw [e]
      have e2 : n + 1 - n = 1 := by omega
      rw [e2]
      have e3 : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [e3, ← ih]
      have e4 : n - 1 + 1 = n := by omega
      omega

/-- Each difference occurs at most once in a Sidon set (as `b - a` with `a < b`). -/
lemma diff_inj {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) {a b c d : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (h : b - a = d - c) : a = c ∧ b = d := by
  have hsum : b + c = d + a := by omega
  have := hA b (Finset.mem_coe.2 hb) d (Finset.mem_coe.2 hd) c (Finset.mem_coe.2 hc)
    a (Finset.mem_coe.2 ha) hsum
  omega

lemma sum_upper_le {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (u : ℕ) :
    ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), (u - (b - a)) ≤ ∑ d ∈ Ico 1 u, (u - d) := by
  obtain ⟨P, hP⟩ : ∃ P : Finset (ℕ × ℕ), P = (A ×ˢ A).filter (fun p => p.1 < p.2) := ⟨_, rfl⟩
  have e1 : ∑ p ∈ P, (u - (p.2 - p.1)) = ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), (u - (b - a)) := by
    rw [hP, sum_filter, sum_product]
    apply sum_congr rfl
    intro a _
    simp only [sum_filter]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, hP, mem_filter, mem_product] at hp hq
    have := diff_inj hA hp.1.1 hp.1.2 hq.1.1 hq.1.2 hp.2 hq.2 hpq
    exact Prod.ext this.1 this.2
  have e2 : ∑ p ∈ P, (u - (p.2 - p.1)) = ∑ d ∈ P.image (fun p => p.2 - p.1), (u - d) :=
    (sum_image (f := fun d => u - d) hinj).symm
  calc ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), (u - (b - a))
      = ∑ p ∈ P, (u - (p.2 - p.1)) := e1.symm
    _ = ∑ d ∈ P.image (fun p => p.2 - p.1), (u - d) := e2
    _ ≤ ∑ d ∈ Ico 1 u, (u - d) := by
        apply sum_le_sum_of_ne_zero
        intro d hd hne
        rw [mem_image] at hd
        obtain ⟨p, hp, rfl⟩ := hd
        rw [hP, mem_filter, mem_product] at hp
        have hne' : u - (p.2 - p.1) ≠ 0 := hne
        have hlt := hp.2
        rw [mem_Ico]
        change 1 ≤ p.2 - p.1 ∧ p.2 - p.1 < u
        omega

lemma sum_pairW_le {A : Finset ℕ} {N u : ℕ} (hA : IsSidon (A : Set ℕ))
    (hAN : A ⊆ Finset.Icc 1 N) (hu : 1 ≤ u) :
    ∑ a ∈ A, ∑ b ∈ A, pairW u a b ≤ A.card * u + u * (u - 1) := by
  rw [sum_sym_split A (pairW u) (pairW_comm u)]
  have hdiag : ∑ a ∈ A, pairW u a a = A.card * u := by
    have : ∀ a ∈ A, pairW u a a = u := by
      intro a ha
      have := Finset.mem_Icc.1 (hAN ha)
      simp only [pairW, min_self, max_self]
      omega
    rw [sum_congr rfl this]
    simp
  have htri : ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), pairW u a b
      ≤ ∑ d ∈ Ico 1 u, (u - d) := by
    have : ∀ a ∈ A, ∀ b ∈ A.filter (a < ·), pairW u a b = u - (b - a) := by
      intro a ha b hb
      have h1 := Finset.mem_Icc.1 (hAN ha)
      have h2 := Finset.mem_Icc.1 (hAN (mem_filter.1 hb).1)
      have h3 := (mem_filter.1 hb).2
      simp only [pairW]
      rw [min_eq_left h3.le, max_eq_right h3.le]
      omega
    calc ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), pairW u a b
        = ∑ a ∈ A, ∑ b ∈ A.filter (a < ·), (u - (b - a)) := by
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          exact this a ha b hb
      _ ≤ ∑ d ∈ Ico 1 u, (u - d) := sum_upper_le hA u
  have hg := gauss u
  omega

/-- The window inequality for Sidon sets: `k² u ≤ (k + u - 1)(N + u - 1)`. -/
theorem window_inequality {A : Finset ℕ} {N u : ℕ} (hA : IsSidon (A : Set ℕ))
    (hAN : A ⊆ Finset.Icc 1 N) (hu : 1 ≤ u) :
    A.card ^ 2 * u ≤ (A.card + u - 1) * (N + u - 1) := by
  have h1 : ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card = A.card * u :=
    sum_win_card hAN hu
  have h2 : ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card ^ 2
      = ∑ a ∈ A, ∑ b ∈ A, pairW u a b := by
    calc ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card ^ 2
        = ∑ s ∈ range (N + u - 1), ∑ a ∈ A, ∑ b ∈ A,
            (if inWin u s a ∧ inWin u s b then 1 else 0) :=
          sum_congr rfl (fun s _ => card_sq_win A u s)
      _ = ∑ a ∈ A, ∑ s ∈ range (N + u - 1), ∑ b ∈ A,
            (if inWin u s a ∧ inWin u s b then 1 else 0) := sum_comm
      _ = ∑ a ∈ A, ∑ b ∈ A, ∑ s ∈ range (N + u - 1),
            (if inWin u s a ∧ inWin u s b then 1 else 0) :=
          sum_congr rfl (fun a _ => sum_comm)
      _ = ∑ a ∈ A, ∑ b ∈ A, pairW u a b := by
          apply sum_congr rfl
          intro a ha
          apply sum_congr rfl
          intro b hb
          have := card_pair_win hAN hu ha hb
          rw [card_filter] at this
          exact this
  have h3 := sum_pairW_le hA hAN hu
  have hcs : (∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card) ^ 2
      ≤ (range (N + u - 1)).card * ∑ s ∈ range (N + u - 1), (A.filter (inWin u s)).card ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [h1, h2, card_range] at hcs
  have h4 : (A.card * u) ^ 2 ≤ (N + u - 1) * (A.card * u + u * (u - 1)) :=
    hcs.trans (Nat.mul_le_mul_left _ h3)
  have h5 : A.card * u + u * (u - 1) = u * (A.card + u - 1) := by
    have e : A.card + u - 1 = A.card + (u - 1) := by omega
    rw [e, Nat.mul_add, Nat.mul_comm A.card u]
  rw [h5] at h4
  have h6 : A.card ^ 2 * u * u ≤ (A.card + u - 1) * (N + u - 1) * u := by
    calc A.card ^ 2 * u * u = (A.card * u) ^ 2 := by ring
      _ ≤ (N + u - 1) * (u * (A.card + u - 1)) := h4
      _ = (A.card + u - 1) * (N + u - 1) * u := by ring
  exact Nat.le_of_mul_le_mul_right h6 (by omega)

/-! ### From the window inequality to the Lindström bound -/

/-- Weak form of the window inequality, without truncated subtraction. -/
theorem window_inequality_weak {A : Finset ℕ} {N u : ℕ} (hA : IsSidon (A : Set ℕ))
    (hAN : A ⊆ Finset.Icc 1 N) (hu : 1 ≤ u) :
    A.card ^ 2 * u ≤ (A.card + u) * (N + u) :=
  (window_inequality hA hAN hu).trans
    (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))

/-- The real-number step: if `K² u ≤ (K + u)(s⁴ + u)` with `s³ ≤ u < s³ + 1` and `1 ≤ s`, then
`K ≤ s² + s + 1`. -/
lemma real_step {K s u : ℝ} (hs : 1 ≤ s) (hu1 : s ^ 3 ≤ u) (hu2 : u < s ^ 3 + 1) (hK : 0 ≤ K)
    (h : K ^ 2 * u ≤ (K + u) * (s ^ 4 + u)) : K ≤ s ^ 2 + s + 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hs0 : 0 < s := by linarith
  have hu0 : 0 < u := by
    have : 0 < s ^ 3 := by positivity
    linarith
  have hN : s ^ 4 ≤ s * u := by
    calc s ^ 4 = s * s ^ 3 := by ring
      _ ≤ s * u := mul_le_mul_of_nonneg_left hu1 hs0.le
  have h1 : K * s ^ 4 ≤ K * (s * u) := mul_le_mul_of_nonneg_left hN hK
  have h2 : K ^ 2 * u ≤ (K * s + K + s ^ 4 + u) * u := by nlinarith [h, h1]
  have h3 : K ^ 2 ≤ K * s + K + s ^ 4 + u := le_of_mul_le_mul_right h2 hu0
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hm : s ^ 2 < K - s - 1 := by linarith
  have h4 : (s ^ 2 + s + 1) * s ^ 2 < K * (K - s - 1) :=
    mul_lt_mul'' hcon hm (by positivity) (by positivity)
  nlinarith [h3, h4, hu2, hs2]

lemma rpow_quarter_pow_four (N : ℕ) : ((N : ℝ) ^ (4⁻¹ : ℝ)) ^ 4 = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

lemma sqrt_eq_quarter_sq (N : ℕ) : Real.sqrt N = ((N : ℝ) ^ (4⁻¹ : ℝ)) ^ 2 := by
  have hs4 := rpow_quarter_pow_four N
  rw [Real.sqrt_eq_iff_mul_self_eq (Nat.cast_nonneg N) (sq_nonneg _)]
  linarith [hs4]

/-- **Lindström's bound** (1969): `h N ≤ √N + N^(1/4) + 1` for every `N`. -/
theorem lindstrom_upper : LindstromUpper := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [h_zero, Nat.cast_zero]
    positivity
  · obtain ⟨B, hB, hS, hc⟩ := exists_extremal N
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (N : ℝ) ^ (4⁻¹ : ℝ) := ⟨_, rfl⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow hN1 (by norm_num)
    have hs4 : s ^ 4 = N := by rw [hs]; exact rpow_quarter_pow_four N
    have hsq : Real.sqrt N = s ^ 2 := by rw [hs]; exact sqrt_eq_quarter_sq N
    obtain ⟨u, hu⟩ : ∃ u : ℕ, u = ⌈s ^ 3⌉₊ := ⟨_, rfl⟩
    have hu_ge : s ^ 3 ≤ u := by rw [hu]; exact Nat.le_ceil _
    have hu_lt : (u : ℝ) < s ^ 3 + 1 := by rw [hu]; exact Nat.ceil_lt_add_one (by positivity)
    have hu1 : 1 ≤ u := by
      have : (0 : ℝ) < u := by
        have : 0 < s ^ 3 := by positivity
        linarith
      exact_mod_cast this
    have hwin := window_inequality_weak hS hB hu1
    have hwin' : ((B.card : ℝ)) ^ 2 * u ≤ ((B.card : ℝ) + u) * (s ^ 4 + u) := by
      rw [hs4]
      exact_mod_cast hwin
    have hfin := real_step hs1 hu_ge hu_lt (Nat.cast_nonneg _) hwin'
    rw [← hc, hsq, ← hs]
    exact hfin



/-- Division with remainder is unique. -/
lemma split_eq {M q1 q2 R R' : ℕ} (hM : 0 < M) (hR : R < M) (hR' : R' < M)
    (h : M * q1 + R = M * q2 + R') : q1 = q2 ∧ R = R' := by
  have hmod : R = R' := by
    have := congrArg (· % M) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hR'] using this
  subst hmod
  exact ⟨Nat.eq_of_mul_eq_mul_left hM (by omega), rfl⟩

/-- The Erdős–Turán point `k ↦ 2pk + (k² mod p) + 1`. -/
def etPoint (p k : ℕ) : ℕ := 2 * p * k + k ^ 2 % p + 1

lemma etPoint_inj {p a b : ℕ} (hp : 0 < p) (h : etPoint p a = etPoint p b) : a = b := by
  unfold etPoint at h
  have h1 : 2 * p * a + a ^ 2 % p = 2 * p * b + b ^ 2 % p := by omega
  exact (split_eq (by omega) (by have := Nat.mod_lt (a ^ 2) hp; omega)
    (by have := Nat.mod_lt (b ^ 2) hp; omega) h1).1

lemma eq_of_cast_eq {p a c : ℕ} (ha : a < p) (hc : c < p) (h : (a : ZMod p) = c) : a = c := by
  have := (ZMod.natCast_eq_natCast_iff' a c p).1 h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this

/-- The algebra: for an odd prime `p`, `a + b = c + d` and `a² + b² ≡ c² + d² (mod p)` force
`{a, b} = {c, d}`. -/
lemma et_core {p a b c d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : a < p) (hc : c < p) (hd : d < p)
    (hs : a + b = c + d) (hq : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hq' : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hq
    simpa [ZMod.natCast_mod] using this
  have hs' : (a : ZMod p) + b = c + d := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hs
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hb' : (b : ZMod p) = c + d - a := by linear_combination hs'
  have key : (2 : ZMod p) * ((a : ZMod p) - c) * ((a : ZMod p) - d) = 0 := by
    rw [hb'] at hq'
    linear_combination hq'
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h h2
    · have : a = c := eq_of_cast_eq ha hc (sub_eq_zero.1 h)
      left
      exact ⟨this, by omega⟩
  · have : a = d := eq_of_cast_eq ha hd (sub_eq_zero.1 h)
    right
    exact ⟨this, by omega⟩

lemma etSet_sidon {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsSidon (((range p).image (etPoint p) : Finset ℕ) : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Finset.mem_coe, mem_image, mem_range] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have hp0 : 0 < p := hp.pos
  unfold etPoint at hsum
  have hra := Nat.mod_lt (a ^ 2) hp0
  have hrb := Nat.mod_lt (b ^ 2) hp0
  have hrc := Nat.mod_lt (c ^ 2) hp0
  have hrd := Nat.mod_lt (d ^ 2) hp0
  have h1 : 2 * p * (a + b) + (a ^ 2 % p + b ^ 2 % p)
      = 2 * p * (c + d) + (c ^ 2 % p + d ^ 2 % p) := by
    linarith [hsum]
  obtain ⟨hs, hq⟩ := split_eq (by omega) (by omega) (by omega) h1
  have hcore := et_core hp hp2 ha hc hd hs hq
  rcases hcore with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · right; subst h1; subst h2; exact ⟨rfl, rfl⟩

lemma etSet_card {p : ℕ} (hp : 0 < p) : ((range p).image (etPoint p)).card = p := by
  rw [card_image_of_injective _ (fun a b hab => etPoint_inj hp hab), card_range]

lemma etSet_subset {p : ℕ} (hp : 0 < p) : (range p).image (etPoint p) ⊆ Finset.Icc 1 (2 * p ^ 2) := by
  intro x hx
  rw [mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [mem_range] at hk
  have hr := Nat.mod_lt (k ^ 2) hp
  rw [Finset.mem_Icc]
  unfold etPoint
  refine ⟨by omega, ?_⟩
  have := Nat.mul_le_mul_left (2 * p) (Nat.succ_le_of_lt hk)
  nlinarith [this]

/-- The Erdős–Turán lower bound at the special values: `h (2 p²) ≥ p` for an odd prime `p`. -/
theorem h_two_mul_sq_ge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ≤ h (2 * p ^ 2) := by
  have := card_le_h (etSet_subset hp.pos) (etSet_sidon hp hp2)
  rwa [etSet_card hp.pos] at this

lemma h_ge_one {N : ℕ} (hN : 1 ≤ N) : 1 ≤ h N := by
  have hsub : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N :=
    Finset.singleton_subset_iff.2 (Finset.mem_Icc.2 ⟨le_refl 1, hN⟩)
  have hS : IsSidon (({1} : Finset ℕ) : Set ℕ) := by decide
  have := card_le_h hsub hS
  rwa [Finset.card_singleton] at this

lemma h_ge_two {N : ℕ} (hN : 2 ≤ N) : 2 ≤ h N := by
  have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.Icc 1 N := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    omega
  have hS : IsSidon (({1, 2} : Finset ℕ) : Set ℕ) := by decide
  have hc : ({1, 2} : Finset ℕ).card = 2 := by decide
  have := card_le_h hsub hS
  rwa [hc] at this

/-- **Erdős–Turán-type lower bound.** `√N ≤ 3 h(N)` for every `N`. -/
theorem sqrt_le_three_mul_h (N : ℕ) : N ≤ (3 * h N) ^ 2 := by
  by_cases hN : N < 32
  · rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    · by_cases h9 : N ≤ 9
      · have h1 := h_ge_one hpos
        nlinarith [Nat.mul_le_mul h1 h1]
      · have h2 := h_ge_two (by omega : 2 ≤ N)
        nlinarith [Nat.mul_le_mul h2 h2]
  · rw [not_lt] at hN
    set n := Nat.sqrt (N / 2) with hn
    have hn1 : n ^ 2 ≤ N / 2 := Nat.sqrt_le' _
    have hn2 : N / 2 < (n + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hn4 : 4 ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      have h16 : (n + 1) ^ 2 ≤ 16 := by
        have h4 : n + 1 ≤ 4 := by omega
        calc (n + 1) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left h4 2
          _ = 16 := by norm_num
      omega
    obtain ⟨p, hp, hlow, hhigh⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    have hp3 : p ≠ 2 := by omega
    have hpn : p ≤ n := by omega
    have h2p : n + 1 ≤ 2 * p := by omega
    have hsub : 2 * p ^ 2 ≤ N := by
      have : p ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hpn 2
      omega
    have hhp : p ≤ h N := (h_two_mul_sq_ge hp hp3).trans (h_mono hsub)
    have hN8 : N < 8 * p ^ 2 := by
      have : (n + 1) ^ 2 ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left h2p 2
      have : (2 * p) ^ 2 = 4 * p ^ 2 := by ring
      omega
    have : p ^ 2 ≤ (h N) ^ 2 := Nat.pow_le_pow_left hhp 2
    nlinarith


/-! ### Corollaries -/

/-- The Erdős–Turán upper bound (1941), as a corollary of Lindström's form. -/
theorem erdos_turan_upper : ErdosTuranUpper := by
  refine ⟨2, Filter.eventually_atTop.2 ⟨1, fun N hN => ?_⟩⟩
  have h1 := lindstrom_upper N
  have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (4⁻¹ : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  linarith

/-- `√N ≤ 3 h(N)`, in real form. -/
theorem sqrt_le_three_mul_h_real (N : ℕ) : Real.sqrt N ≤ 3 * h N := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  exact_mod_cast sqrt_le_three_mul_h N

/-- `h(N) ≤ 3 √N` for `N ≥ 1`, from Lindström's bound. -/
theorem h_le_three_sqrt {N : ℕ} (hN : 1 ≤ N) : (h N : ℝ) ≤ 3 * Real.sqrt N := by
  have h1 := lindstrom_upper N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (N : ℝ) ^ (4⁻¹ : ℝ) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow hN1 (by norm_num)
  have hsq : Real.sqrt N = s ^ 2 := by rw [hs]; exact sqrt_eq_quarter_sq N
  rw [← hs, hsq] at h1
  rw [hsq]
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs3 : 1 ≤ s ^ 2 := by nlinarith
  linarith

/-! ### The two halves of the conjecture -/

/-- Upper half of Erdős Problem #30: for every `ε > 0`, `h N ≤ √N + O(N ^ ε)`.

**Open.** What is proved above is only the case `ε = 1/4` (`erdos_turan_upper`). Nothing smaller
is known; the best published results improve the constant in front of `N ^ (1/4)` and no more. -/
def UpperHalf : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop, (h N : ℝ) - Real.sqrt N ≤ C * (N : ℝ) ^ ε

/-- Lower half of Erdős Problem #30: for every `ε > 0`, `h N ≥ √N - O(N ^ ε)`.

**Open.** The Singer and Bose–Chowla constructions give `h N ≥ √N - (gap between prime powers
below √N)`, so the error term is controlled by prime gaps. The best published gap bound
(Baker–Harman–Pintz) gives `N ^ (21/80)`. Neither the constructions nor the gap bounds are
formalised here. -/
def LowerHalf : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop, Real.sqrt N - (h N : ℝ) ≤ C * (N : ℝ) ^ ε

/-- Problem #30 is exactly the conjunction of its two halves. -/
theorem conjecture_iff : Conjecture ↔ UpperHalf ∧ LowerHalf := by
  constructor
  · intro hC
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨C, hCε⟩ := Asymptotics.isBigO_iff.1 (hC ε hε)
      refine ⟨C, hCε.mono fun N hN => ?_⟩
      have hpos : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
      rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos] at hN
      exact (abs_le.1 hN).2
    · obtain ⟨C, hCε⟩ := Asymptotics.isBigO_iff.1 (hC ε hε)
      refine ⟨C, hCε.mono fun N hN => ?_⟩
      have hpos : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
      rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos] at hN
      have := (abs_le.1 hN).1
      linarith
  · rintro ⟨hU, hL⟩ ε hε
    obtain ⟨C₁, h₁⟩ := hU ε hε
    obtain ⟨C₂, h₂⟩ := hL ε hε
    refine Asymptotics.isBigO_iff.2 ⟨max C₁ C₂, ?_⟩
    filter_upwards [h₁, h₂] with N hN₁ hN₂
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg N) ε
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hpos]
    have e1 : C₁ * (N : ℝ) ^ ε ≤ max C₁ C₂ * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    have e2 : C₂ * (N : ℝ) ^ ε ≤ max C₁ C₂ * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpos
    rw [abs_le]
    constructor <;> linarith

/-- The strong form `h N = √N + O(1)` implies the conjecture. -/
theorem strong_implies_conjecture : StrongConjecture → Conjecture := by
  intro hS ε hε
  have hg : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ ε) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hn : Filter.Tendsto (fun N : ℕ => ‖(N : ℝ) ^ ε‖) Filter.atTop Filter.atTop :=
    hg.congr (fun N => (Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ε)).symm)
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[Filter.atTop] fun N : ℕ => (N : ℝ) ^ ε :=
    (Asymptotics.isLittleO_one_left_iff ℝ).2 hn
  exact hS.trans h1.isBigO

/-! ### The lower half and prime gaps (conditional)

Singer's theorem is **not** formalised here, so the next result is conditional on it. It states
precisely how the error term in the lower half of Problem #30 is controlled by gaps between prime
powers. -/

/-- Singer's theorem (1938) as a hypothesis: for every prime power `q` there is a Sidon set with
`q + 1` elements inside `{1, …, q² + q + 1}`. **Not proved in this repository.** -/
def SingerConstruction : Prop :=
  ∀ q : ℕ, IsPrimePow q → q + 1 ≤ h (q ^ 2 + q + 1)

/-- Hypothesis on gaps between prime powers: some constant `C` such that every `x ≥ 1` has a prime
power `q` with `x - C x^θ ≤ q ≤ x`. **Not proved in this repository.** Baker–Harman–Pintz give
`θ = 0.525`. The Riemann hypothesis gives `θ = 1/2` up to a logarithm, which this form does not
capture. Cramér's conjecture would give every `θ > 0`. -/
def PrimePowerGaps (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → ∃ q : ℕ, IsPrimePow q ∧ (q : ℝ) ≤ x ∧ x - C * x ^ θ ≤ q

/-- Singer's construction and prime power gaps with exponent `θ` give
`h N ≥ √N - C N^(θ/2)`. -/
theorem lower_bound_of_gaps {θ : ℝ} (hθ : 0 ≤ θ) (hS : SingerConstruction)
    (hG : PrimePowerGaps θ) :
    ∃ C : ℝ, ∀ N : ℕ, 4 ≤ N → Real.sqrt N - C * (N : ℝ) ^ (θ / 2) ≤ h N := by
  obtain ⟨C, hC⟩ := hG
  refine ⟨max C 0, fun N hN => ?_⟩
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq4 : (2 : ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  obtain ⟨q, hq, hqx, hqlow⟩ := hC (Real.sqrt N - 1) (by linarith)
  have hq1 : ((q : ℝ) + 1) ≤ Real.sqrt N := by linarith
  have hq2 : ((q : ℝ) + 1) ^ 2 ≤ N := (Real.le_sqrt' (by positivity)).1 hq1
  have hq3 : q ^ 2 + q + 1 ≤ N := by
    have : (q + 1) ^ 2 ≤ N := by exact_mod_cast hq2
    nlinarith
  have hh : q + 1 ≤ h N := (hS q hq).trans (h_mono hq3)
  have hhR : (q : ℝ) + 1 ≤ h N := by exact_mod_cast hh
  have hx0 : (0 : ℝ) ≤ Real.sqrt N - 1 := by linarith
  have hpow : (Real.sqrt N - 1) ^ θ ≤ (N : ℝ) ^ (θ / 2) := by
    calc (Real.sqrt N - 1) ^ θ ≤ (Real.sqrt N) ^ θ :=
          Real.rpow_le_rpow hx0 (by linarith) hθ
      _ = (N : ℝ) ^ (θ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]
          congr 1
          ring
  have hpos : (0 : ℝ) ≤ (Real.sqrt N - 1) ^ θ := Real.rpow_nonneg hx0 θ
  have h1 : C * (Real.sqrt N - 1) ^ θ ≤ max C 0 * (N : ℝ) ^ (θ / 2) := by
    calc C * (Real.sqrt N - 1) ^ θ ≤ max C 0 * (Real.sqrt N - 1) ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ max C 0 * (N : ℝ) ^ (θ / 2) :=
          mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  linarith

/-! ### Fidelity of the formal definition of `h`

Small values, computed by the kernel from the definition of `h`, compared with the exact values
from the independent Python search (`scripts/`, `results/h_N_data.csv`) and OEIS A143824. -/

example : h 1 = 1 := by decide +kernel
example : h 2 = 2 := by decide +kernel
example : h 3 = 2 := by decide +kernel
example : h 4 = 3 := by decide +kernel
example : h 6 = 3 := by decide +kernel
example : h 7 = 4 := by decide +kernel
example : h 8 = 4 := by decide +kernel

/-! ### Axioms -/

#print axioms lindstrom_upper
#print axioms erdos_turan_upper
#print axioms sqrt_le_three_mul_h
#print axioms conjecture_iff
#print axioms strong_implies_conjecture
#print axioms lower_bound_of_gaps

end Erdos30
