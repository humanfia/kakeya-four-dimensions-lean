/- Adapted from this LOT tree, obligation o245, session x0854,
branch x0854 at ba3817bb17b771a5ddd349237fa63f3fef2ba670, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeMatching.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMatchingBands
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeDensityBudget

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The actual marked matching input has the original old/native prior budget. -/
theorem density_budget (lev : cfg.AssignmentLevel k s) (hbasic : cfg.Basic)
    (hℓ : cfg.ℓ = cfg.κ) (ha : c.a = cfg.N k ^ (-s))
    (hDq : c.D ≤ cfg.timeLength k s ^ 2)
    (hχq : cfg.N k ^ (-cfg.e₀) ≤ cfg.timeLength k s ^ 2) :
    (∑ i : c.Index, c.comparison.density (c.comparison.colour i)) ≤
      (28672 * cfg.K k * (c.A / cfg.N k ^ (-s)) ^ cfg.d) *
        (cfg.N k ^ c.ε * cfg.K k + 128 * cfg.K k ^ 5) := by
  have hH : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k c.ε σ c.D (cfg.N k ^ (-s))
      c.m c.AH c.group c.hH := by simpa only [ha] using c.layer
  calc
    _ = ∑ i : c.Index,
        (7 * (cfg.K k * c.A ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
          ((c.support.table.colour c.group (cfg.j k s) i).1 0))) *
        (4096 * cfg.timeLength k s * c.D ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [c.comparison_density]
      change 28672 * cfg.K k * c.A ^ cfg.d * cfg.timeLength k s * c.D ^ 2 *
        binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
          ((c.support.table.colour c.group (cfg.j k s) i).1 0) = _
      ring
    _ ≤ _ := cfg.observed_matching_density_budget lev hbasic c.N_pos c.K_one hℓ
      c.D_pos hDq hχq ((Real.rpow_pos_of_pos c.N_pos _).trans_le c.width_lower).le
      σ c.dominated hH c.support.table c.support.contact

def badMarks (M : ℝ) : Set (Fin c.support.table.count) :=
  {j | ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 2 ∧
    M ≤ |predictor (c.comparison.coefficients (c.comparison.source j)) (z 0) (z 1) (z 2) -
      predictor (c.comparison.coefficients (c.comparison.witness j)) (z 0) (z 1) (z 2)|}

def badOriginal (M : ℝ) : Set (α × ℝ) := {p | c.comparison.mark p ∈ c.badMarks M}

theorem measurable_badOriginal (M : ℝ) : MeasurableSet (c.badOriginal M) :=
  c.comparison.mark_measurable (Set.to_countable (c.badMarks M)).measurableSet

/-- The discrepancy theorem applies to the actual native comparison. Its bad
mark event returns with EXACT original incidence mass. No pair-fibre floors,
normalization of the original law or discarded zero-palette colours enter. -/
theorem matching_bad_mass {d₀ ε₀ R₀ X : ℝ} (p : MatchingScales d₀ ε₀) (J : JetData)
    (hmb : MatchBound p.middle ε₀ R₀) (hR₀ : 2 ≤ R₀)
    (hX : 4 ≤ X) (hXR : R₀ ≤ X) (hXJ : 3 * J.C₂ ≤ X)
    (hXB : budgetMatchingConstant p J ≤ X) (hKX : 16 * cfg.K k ≤ X)
    (hd : 0 ≤ cfg.d) (hd1 : cfg.d ≤ 1) (hdd : cfg.d ≤ d₀)
    (hbudget : (∑ i : c.Index, c.comparison.density (c.comparison.colour i)) ≤ X ^ 2) :
    σ (c.badOriginal (2 * c.comparison.error * X ^ p.size)) ≤
      ENNReal.ofReal (X ^ (-5 : ℝ)) := by
  let M := 2 * c.comparison.error * X ^ p.size
  let Y := M / c.A
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA : 0 < c.A := (Real.rpow_pos_of_pos c.N_pos _).trans_le c.width_lower
  have hXsize : 1 ≤ X ^ p.size := Real.one_le_rpow hX1 (by have := p.size_one; linarith)
  have hMexpr : M = 8 * c.A * X ^ p.size := by change 2 * (4 * c.A) * X ^ p.size = _; ring
  have hMp : 0 < M := by rw [hMexpr]; positivity
  have hAM : 2 * c.A ≤ M := by
    rw [hMexpr]
    nlinarith [mul_le_mul_of_nonneg_left hXsize (by positivity : 0 ≤ 8 * c.A)]
  have hY : 0 ≤ Y := (div_pos hMp hA).le
  have hYeq : Y = 8 * X ^ p.size := by
    dsimp [Y]
    rw [hMexpr]
    field_simp
  have hX3 : (8 : ℝ) ≤ X ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hX 3
    norm_num at hh
    linarith
  have hYX : Y ≤ X ^ (p.size + 3) := by
    calc
      Y = 8 * X ^ p.size := hYeq
      _ ≤ X ^ 3 * X ^ p.size := mul_le_mul_of_nonneg_right hX3 (Real.rpow_nonneg hXp.le _)
      _ = _ := by rw [Real.rpow_add hXp, Real.rpow_ofNat]; ring
  have hb := c.comparison.predictorPair.budget_comparison p J hmb hR₀ hX hXR hXJ hXB
    (by have := c.K_one; linarith : 0 ≤ 16 * cfg.K k) hKX hY hYX hd hdd hbudget (by
      intro i n
      change c.comparison.law (c.band i (2 * (M * (2 : ℝ) ^ n))) ≤
        ENNReal.ofReal ((16 * cfg.K k * c.comparison.density (c.comparison.colour i) * Y ^ cfg.d) *
          ((2 : ℝ) ^ cfg.d) ^ n)
      have htwo : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hAV : 2 * c.A ≤ M * (2 : ℝ) ^ n := hAM.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo hMp.le)
      apply (c.band_cap hd hd1 i hAV).trans_eq
      congr 1
      have htwopow : ((2 : ℝ) ^ n) ^ cfg.d = ((2 : ℝ) ^ cfg.d) ^ n := by
        calc
          _ = ((2 : ℝ) ^ (n : ℝ)) ^ cfg.d := by rw [Real.rpow_natCast]
          _ = (2 : ℝ) ^ ((n : ℝ) * cfg.d) := (Real.rpow_mul (by norm_num) _ _).symm
          _ = (2 : ℝ) ^ (cfg.d * (n : ℝ)) := by congr 1; ring
          _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      rw [show (M * (2 : ℝ) ^ n) / c.A = Y * (2 : ℝ) ^ n by dsimp [Y]; ring,
        Real.mul_rpow hY (pow_nonneg (by norm_num) n), htwopow]
      ring)
  have hm : c.comparison.law {v | v.1 ∈ c.badMarks M} = σ (c.badOriginal M) :=
    c.comparison.original_mark_mass (fun j => j ∈ c.badMarks M)
  rw [← hm]
  exact hb

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
