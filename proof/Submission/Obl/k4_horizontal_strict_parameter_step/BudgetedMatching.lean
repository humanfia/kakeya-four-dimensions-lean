/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/BudgetedMatching.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DyadicMatching
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingScales

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

def budgetMatchingConstant {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData) : ℝ :=
  8 * (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) / (1 - p.decay)

/-- The accepted discrepancy bound only needs a summed original density budget.
A uniform auxiliary mass `1/(number of indices+1)` makes every light threshold positive,
including zero-palette colours, while its total cost stays at most one. -/
theorem budgeted_matching {ι Λ Ω : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq Λ] [MeasurableSpace Ω]
    {d₀ ε₀ R₀ : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData) (S : DiscSetup ι Λ Ω)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    {X C Y d : ℝ} (hX : 4 ≤ X) (hXR : R₀ ≤ X) (hXJ : 3 * J.C₂ ≤ X)
    (hXB : budgetMatchingConstant p J ≤ X)
    (hC : 0 ≤ C) (hCX : C ≤ X) (hY : 0 ≤ Y) (hYX : Y ≤ X ^ (p.size + 3))
    (hd : 0 ≤ d) (hdd : d ≤ d₀) (hbudget : (∑ i, S.ρ (S.lab i)) ≤ X ^ 2)
    (hband : ∀ i k, S.Pm {v | S.lab (S.src v) = S.lab i ∧
      ‖S.φ i (emb (S.x v)) - (S.w v : ℂ)‖ ≤ 2 * ((2 * S.Δ * X ^ p.size) * 2 ^ k)} ≤
        ENNReal.ofReal ((C * S.ρ (S.lab i) * Y ^ d) * ((2 : ℝ) ^ d) ^ k)) :
    S.Pm {v | ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 ∧
      2 * S.Δ * X ^ p.size ≤ ‖S.φ (S.src v) (emb z) - S.φ (S.wit v) (emb z)‖} ≤
        ENNReal.ofReal (X ^ (-5 : ℝ)) := by
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  let M := 2 * S.Δ * X ^ p.size
  let τ : ℝ := ((Fintype.card ι : ℝ) + 1)⁻¹
  let θ : Λ → ℝ := fun l => (S.ρ l + τ) * X ^ (-8 : ℝ)
  let G : Λ → ℝ := fun l => C * S.ρ l * Y ^ d
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hθ : ∀ l, 0 < θ l := by
    intro l
    exact mul_pos (add_pos_of_nonneg_of_pos (S.ρ_nonneg l) hτ) (Real.rpow_pos_of_pos hXp _)
  have hG : ∀ l, 0 ≤ G l := by
    intro l
    exact mul_nonneg (mul_nonneg hC (S.ρ_nonneg l)) (Real.rpow_nonneg hY _)
  have hMp : 0 < M := by dsimp [M]; have := S.Δ_pos; positivity
  have hratio : M / (2 * S.Δ) = X ^ p.size := by
    dsimp [M]
    field_simp [S.Δ_pos.ne']
  have hXsize : X ≤ X ^ p.size := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1 p.size_one
  have hR : R₀ * (2 * S.Δ) ≤ M := by
    have hh := mul_le_mul_of_nonneg_right (hXR.trans hXsize) (by have := S.Δ_pos; positivity : 0 ≤ 2 * S.Δ)
    dsimp [M]
    nlinarith
  have hJ : 3 * J.C₂ ≤ (M / (2 * S.Δ)) ^ p.slack := by
    rw [hratio, ← Real.rpow_mul hXp.le]
    apply hXJ.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (by have := p.density_gap; linarith : (1 : ℝ) ≤ p.size * p.slack)
  have hρ : ∀ l, S.ρ l * (M / (2 * S.Δ)) ^ (-p.slack) ≤ θ l / 2 := by
    intro l
    rw [hratio]
    exact p.density_base hX (S.ρ_nonneg l) hτ
  have hΓ : ∀ l, G l / θ l ≤ (M / (2 * S.Δ)) ^ (p.middle + p.slack) := by
    intro l
    rw [hratio]
    exact p.band_base hX (S.ρ_nonneg l) hτ hC hCX hY hYX hd hdd
  have hb := discrepancy_mass_le_from_base J S M θ G hmb hR₀ p.slack_pos p.slack_le hMp
    p.decay_pos p.decay_lt_one hθ hG hR hJ hρ p.density_growth hΓ (p.band_growth hdd) hband
  have hτsum : (Fintype.card ι : ℝ) * τ ≤ 1 := by
    dsimp [τ]
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  have hpow : X ^ 2 * X ^ (-8 : ℝ) = X ^ (-6 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hXp]
    norm_num
  have hθbudget : (∑ i, θ (S.lab i)) ≤ 2 * X ^ (-6 : ℝ) := by
    change (∑ i, (S.ρ (S.lab i) + τ) * X ^ (-8 : ℝ)) ≤ _
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ (X ^ 2 + 1) * X ^ (-8 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (add_le_add hbudget hτsum) (Real.rpow_nonneg hXp.le _)
      _ ≤ (2 * X ^ 2) * X ^ (-8 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXp.le _)
        nlinarith
      _ = _ := by rw [mul_assoc, hpow]
  have hconst : 0 ≤ 4 *
      (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) / (1 - p.decay) :=
    div_nonneg (by positivity) (sub_nonneg.mpr p.decay_lt_one.le)
  calc
    _ ≤ ENNReal.ofReal (4 *
        (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
        (1 - p.decay) * ∑ i, θ (S.lab i)) := hb
    _ ≤ ENNReal.ofReal (budgetMatchingConstant p J * X ^ (-6 : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_left hθbudget hconst).trans_eq (by
        dsimp [budgetMatchingConstant]
        ring)
    _ ≤ ENNReal.ofReal (X * X ^ (-6 : ℝ)) := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hXB (Real.rpow_nonneg hXp.le _))
    _ = _ := by
      congr 1
      calc
        X * X ^ (-6 : ℝ) = X ^ (1 : ℝ) * X ^ (-6 : ℝ) := by rw [Real.rpow_one]
        _ = X ^ ((1 : ℝ) + -6) := (Real.rpow_add hXp _ _).symm
        _ = _ := by norm_num

end

end Submission.Obl.k4_horizontal_strict_parameter_step
