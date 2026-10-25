/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, CoefficientSubbinLists.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`CoefficientSubbinLists.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Stored coefficient/time-subbin floors bound the list seen in a scalar bin. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal Classical
open Submission.Obl.k4_scalar_coefficient_clustering

theorem old_cell_count_in_container {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset I) (cells : I → Set Ω)
    (U : Set Ω) (hdisj : (↑S : Set I).PairwiseDisjoint cells)
    (hmeas : ∀ i ∈ S, MeasurableSet (cells i)) (hsub : ∀ i ∈ S, cells i ⊆ U)
    (θ : ℝ) (hθ : 0 < θ) (hfloor : ∀ i ∈ S, θ ≤ μ.real (cells i)) :
    (S.card : ℝ) ≤ μ.real U / θ := by
  have hbound := Submission.Lib.K4FinitePlankAtlases.old_cell_count (μ.restrict U) S cells
    hdisj hmeas hθ (by
      intro i hi
      rw [measureReal_restrict_apply (hmeas i hi), Set.inter_eq_left.mpr (hsub i hi)]
      exact hfloor i hi)
  simpa only [measureReal_restrict_apply_univ] using hbound

/-- A full coefficient cell predicts all its occurrences in a short subbin,
using the original coefficients instead of a posterior representative. -/
theorem coefficient_bin_subbin_scalar_gap {p B η : ℝ} (hp : 0 < p)
    (a b : Coeff) (t s : ℝ) (hb : ‖b‖ ≤ B)
    (hcode : coefficientCode p a = coefficientCode p b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hη : |t - s| ≤ η) :
    |quadratic a t - quadratic b s| ≤ 9 * p + 3 * B * η := by
  have hB : 0 ≤ B := (norm_nonneg b).trans hb
  have hcoeff := (quadratic_difference_le (a := a) (b := b) ht).trans
    (mul_le_mul_of_nonneg_left (coefficient_dist_of_code_eq hp hcode) (by norm_num : (0 : ℝ) ≤ 3))
  have htime := (quadratic_time_lipschitz hb ht hs).trans
    (mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ 3 * B))
  have htriangle := abs_sub_le (quadratic a t) (quadratic b t) (quadratic b s)
  nlinarith only [hcoeff, htime, htriangle]

/-- Every compatible coefficient entry contributes its ENTIRE stored subbin
mass to one enlarged scalar band; hence the list uses only the band budget. -/
theorem coefficient_subbin_list_card {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset (Fin 3 → ℤ))
    (cells : (Fin 3 → ℤ) → Set Ω) (a : Ω → Coeff) (time : Ω → ℝ)
    (p B η θ M : ℝ) (j : ℤ) (hp : 0 < p) (hθ : 0 < θ)
    (hmeas : ∀ i ∈ S, MeasurableSet (cells i))
    (hcode : ∀ i ∈ S, ∀ e ∈ cells i, coefficientCode p (a e) = i)
    (hB : ∀ i ∈ S, ∀ e ∈ cells i, ‖a e‖ ≤ B)
    (hunit : ∀ i ∈ S, ∀ e ∈ cells i, time e ∈ Set.Icc (0 : ℝ) 1)
    (htime : ∀ i ∈ S, ∀ e ∈ cells i, ∀ e' ∈ cells i, |time e - time e'| ≤ η)
    (hfloor : ∀ i ∈ S, θ ≤ μ.real (cells i))
    (hwitness : ∀ i ∈ S, ∃ e ∈ cells i, ⌊quadratic (a e) (time e) / p⌋ = j)
    (hband : μ.real {e | |quadratic (a e) (time e) - p * (j : ℝ)| ≤ 10 * p + 3 * B * η} ≤ M) :
    (S.card : ℝ) ≤ M / θ := by
  have hdisj : (↑S : Set (Fin 3 → ℤ)).PairwiseDisjoint cells := by
    intro i hi i' hi' hii'
    exact Set.disjoint_left.mpr fun e he he' =>
      hii' ((hcode i hi e he).symm.trans (hcode i' hi' e he'))
  have hsub : ∀ i ∈ S, cells i ⊆
      {e | |quadratic (a e) (time e) - p * (j : ℝ)| ≤ 10 * p + 3 * B * η} := by
    intro i hi e he
    rcases hwitness i hi with ⟨e₀, he₀, hj⟩
    have hgap := coefficient_bin_subbin_scalar_gap hp (a e) (a e₀) (time e) (time e₀)
      (hB i hi e₀ he₀) ((hcode i hi e he).trans (hcode i hi e₀ he₀).symm)
      (hunit i hi e he) (hunit i hi e₀ he₀) (htime i hi e he e₀ he₀)
    have hround : |quadratic (a e₀) (time e₀) - p * (j : ℝ)| ≤ p := by
      simpa only [hj] using floor_scaled_error hp (quadratic (a e₀) (time e₀))
    have htriangle := abs_sub_le (quadratic (a e) (time e)) (quadratic (a e₀) (time e₀)) (p * (j : ℝ))
    exact (htriangle.trans (add_le_add hgap hround)).trans_eq (by ring)
  have hcount := old_cell_count_in_container μ S cells _ hdisj hmeas hsub θ hθ hfloor
  exact hcount.trans (div_le_div_of_nonneg_right hband hθ.le)

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
