/- Adapted within this LOT tree from o250, session x0879, commit
c77c1a90bc277c8885ed3af05e20668071ee3318,
`Submission/Obl/k4_horizontal_wide_interval_return/Native/Blocks.lean` (as inlined on o274 by
x0969 into `Inherited/Native/Blocks.lean`), restated for the accepted
`k4_critical_conditional_row_preparation.Data`. -/
import Mathlib
import Submission.Obl.k4_critical_conditional_row_preparation.Model

set_option linter.unusedVariables false

/-!
# The prepared true blocks at one index and depth

`BlocksAt cfg k s R` is the frozen atlas premise at index `k` and depth `s`, with
`q = 2^-T`, `a = N^-s`, `g = N^-κs` substituted and split into named fields.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The horizontal affine form of a block polynomial. -/
def HorizontalForm (F : MvPolynomial (Fin 4) ℝ) (L : Fin 4 → ℝ) : Prop :=
  F = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) *
    MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) +
    MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4))

theorem eval_horizontalForm {F : MvPolynomial (Fin 4) ℝ} {L : Fin 4 → ℝ}
    (hF : HorizontalForm F L) (x : Fin 4 → ℝ) :
    MvPolynomial.eval x F = x 3 - (L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2) := by
  rw [hF]
  simp

/-- The prepared blocks of depth `s` at index `k`. -/
structure BlocksAt (cfg : Data α) (k : ℕ) (s R : ℝ) : Prop where
  T_lo : cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s
  T_hi : (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s)
  sets : ∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧
    cfg.B k s i ⊆ cfg.A k s i
  disj : ∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')
  nu_lo : ∀ i, ENNReal.ofReal ((cfg.N k ^ (-s)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 *
    cfg.N k ^ (-cfg.κ * s) / cfg.K k) ≤ cfg.ν k (cfg.A k s i)
  nu_hi : ∀ i, cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d *
    (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2 * cfg.N k ^ (-cfg.κ * s))
  mu_lo : ∀ i, ENNReal.ofReal (((2 : ℝ) ^ cfg.T k s)⁻¹ / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
    cfg.μ k (cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i))
  c_bd : ∀ i e, |cfg.c k s i e| ≤ cfg.K k
  geom : ∀ i, ∀ l ∈ cfg.A k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
    |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ ∧
    |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤
      cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.κ * s) ∧
    |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * cfg.N k ^ (-cfg.κ * s)
  fit : ∀ i, ∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (cfg.N k ^ (-s)) (cfg.F k s i) l
    (Data.I (cfg.T k s) (cfg.j k s i))
  horiz_ae : ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)
  center : ∀ i, |cfg.c k s i 3 + cfg.c k s i 0 +
      ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.c k s i 1| +
    |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * ((2 : ℝ) ^ cfg.T k s)⁻¹| ≤
      cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹
  affine : ∀ i, ∃ L : Fin 4 → ℝ, HorizontalForm (cfg.F k s i) L ∧
    |L 3| ≤ cfg.K k * (1 + cfg.N k ^ (-s) / (((2 : ℝ) ^ cfg.T k s)⁻¹) ^ 2) ∧
    ∀ l ∈ cfg.B k s i, ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s i),
      |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤
        cfg.K k * (1 + cfg.N k ^ (-s) / ((2 : ℝ) ^ cfg.T k s)⁻¹)
  cover : ∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)
  palette : ∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧
      ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹) * cfg.ν k (cfg.A k s i) *
        cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀}

theorem blocksAt_eventually {cfg : Data α} (hatlas : cfg.Atlas) (hℓ : cfg.ℓ = cfg.κ)
    {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → BlocksAt cfg k s R := by
  filter_upwards [hatlas R hR] with k hk
  intro s hs1 hs2
  have hp := hk s hs1 hs2
  simp only [zpow_neg, zpow_natCast, hℓ] at hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  refine ⟨h1, h2, h3, h4, fun i => (h5 i).1, fun i => (h5 i).2.1, fun i => (h5 i).2.2.1,
    fun i => (h5 i).2.2.2.1, fun i => (h5 i).2.2.2.2.2.1, fun i => (h5 i).2.2.2.2.2.2.1, ?_,
    fun i => ((h5 i).2.2.2.2.2.2.2.2 trivial).2.2.1, fun i => ((h5 i).2.2.2.2.2.2.2.2 trivial).2.2.2,
    h6, h7⟩
  by_cases hn : ∃ i : Fin (cfg.n k s), True
  · obtain ⟨i, -⟩ := hn
    exact ((h5 i).2.2.2.2.2.2.2.2 trivial).2.1
  · push Not at hn
    have hzero : cfg.μ k univ = 0 := by
      have := h6
      rw [Filter.eventually_iff, mem_ae_iff] at this
      have hempty : {p : α × ℝ | ∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)}ᶜ = univ := by
        ext p
        simp only [mem_compl_iff, mem_ofPred_eq, mem_univ, iff_true, not_exists, not_and]
        intro i
        exact (hn i).elim
      rw [hempty] at this
      exact this
    rw [Measure.measure_univ_eq_zero.mp hzero, ae_zero]
    exact Filter.eventually_bot

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
