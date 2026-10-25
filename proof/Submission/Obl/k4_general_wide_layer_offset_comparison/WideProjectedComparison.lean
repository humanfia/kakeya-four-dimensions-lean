import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonDecay
import Submission.Obl.k4_general_wide_layer_offset_comparison.WideComparisonNumerics

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WideProjectedComparison.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

def comparisonJetConstant (J : JetData) (ε : ℝ) : ℝ :=
  8 * (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
    (1 - (2 : ℝ) ^ (-ε / 2)) * 25000000000

theorem comparisonJetConstant_nonneg (J : JetData) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ comparisonJetConstant J ε := by
  have hχ : (2 : ℝ) ^ (-ε / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold comparisonJetConstant
  positivity

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

/-- The two original reference totals and density factors cost only six
powers of the common subpower parameter. -/
theorem bad_mass_le_budget (hp : p.Valid) (hKH : p.K k ≤ H) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (J : JetData) {M₀ R d₀ ε₀ R₀ ε : ℝ}
    (hmb : MatchBound d₀ ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hM₀ : 0 < M₀)
    (hmin : H * p.N k ^ (-sf) ≤ M₀)
    (hReq : R = M₀ / (4 * H * p.N k ^ (-sc))) (hR : R₀ ≤ R)
    (hC : 3 * J.C₂ ≤ R ^ ε)
    (hAR : (M₀ / p.N k ^ (-sf)) ^ p.d ≤ 2 * R ^ d₀) (hdd : p.d ≤ d₀) :
    σ (f.bad M₀) ≤ ENNReal.ofReal (comparisonJetConstant J ε * H ^ 6 * R ^ (-ε)) := by
  have hb := f.bad_mass_le hp Q hcover J hmb hR₀ hε hεε₀ hM₀ hmin hReq hR hC hAR hdd
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hRp : 0 < R := by linarith
  have hχ : (2 : ℝ) ^ (-ε / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let c := 8 * (((2 * cubeRadius J + 1) ^ Fintype.card (↥J.V × Fin J.q) : ℕ) : ℝ) /
    (1 - (2 : ℝ) ^ (-ε / 2))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd := comparison_density_budget (zero_le_one.trans (hp.subpower.1 k)) hKH f.loss_one
    hp.dimension_lt_one.le
  change c * p.projectedComparisonDensity k H * R ^ (-ε) * (3 * (1 + 240 * H ^ 3)) ≤ _
  calc
    _ = (c * R ^ (-ε)) * (p.projectedComparisonDensity k H * (3 * (1 + 240 * H ^ 3))) := by ring
    _ ≤ (c * R ^ (-ε)) * (25000000000 * H ^ 6) :=
      mul_le_mul_of_nonneg_left hd (mul_nonneg hc (Real.rpow_nonneg hRp.le _))
    _ = _ := by dsimp [comparisonJetConstant, c]; ring

/-- The explicit wide threshold absorbs the fine/coarse native thickness
ratio, for any fine depth increment at most `u`. -/
theorem wide_bad_mass_le (hp : p.Valid) (hKH : p.K k ≤ H) {u R ε₀ R₀ ε : ℝ}
    (hu : 0 < u) (hgap : sf - sc ≤ u) (hsmall : 4 * H ≤ p.N k ^ u)
    (hwide : p.N k ^ (10 / (1 - p.d) * u) ≤ R)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (J : JetData) (hmb : MatchBound ((1 + p.d) / 2) ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) (hR : R₀ ≤ R) (hC : 3 * J.C₂ ≤ R ^ ε) :
    σ (f.bad (4 * H * p.N k ^ (-sc) * R)) ≤
      ENNReal.ofReal (comparisonJetConstant J ε * H ^ 6 * R ^ (-ε)) := by
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.scale k]
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := zero_lt_one.trans_le f.loss_one
  have hac : 0 < H * p.N k ^ (-sc) := by positivity
  have haf : H * p.N k ^ (-sf) ≤ H * p.N k ^ (-sc) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg f.coarse_le_fine)) hHp.le
  have hmin : H * p.N k ^ (-sf) ≤ 4 * H * p.N k ^ (-sc) * R := by
    calc
      _ ≤ H * p.N k ^ (-sc) := haf
      _ ≤ (H * p.N k ^ (-sc)) * (4 * R) :=
        le_mul_of_one_le_right hac.le (by linarith)
      _ = _ := by ring
  have hratio := wide_comparison_prior_factor (sc := sc) hN1 f.loss_one hp.dimension_nonneg
    hp.dimension_lt_one hu hgap hsmall hwide
  have hAR : (4 * H * p.N k ^ (-sc) * R / p.N k ^ (-sf)) ^ p.d ≤
      2 * R ^ ((1 + p.d) / 2) := by
    simpa only [show -sc - (sf - sc) = -sf by ring] using hratio
  apply f.bad_mass_le_budget hp hKH Q hcover J hmb hR₀ hε hεε₀
    (by positivity : 0 < 4 * H * p.N k ^ (-sc) * R) hmin
    (by field_simp) hR hC hAR
  linarith [hp.dimension_lt_one]

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
