-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Lib.K4AngularCharge.ChartCells

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4AngularCharge

noncomputable section

/-- A native major-velocity bin in an arbitrarily oriented thin parent
meets only polynomially many original planar velocity bins. The center
is an actual velocity, so no bound on its absolute size is needed. -/
theorem linear_velocity_bin_menu {Ω : Type*}
    (velocity : Ω → EuclideanSpace ℝ (Fin 2)) (b : Ω → Fin 2 → ℝ)
    (U : Set Ω) (offset : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (H a fine : ℝ) (j : ℤ) (hH : 0 ≤ H) (ha : 0 < a) (hf : 0 < fine)
    (haf : a ≤ fine) (hmajor : ∀ e, |M e 0| ≤ H) (hminor : ∀ e, |M e 1| ≤ a)
    (hcoord : ∀ z ∈ U, ∀ e, velocity z e = offset e + ∑ i, M e i * b z i)
    (hbin : ∀ z ∈ U, ⌊b z 0 / a⌋ = j) (hbound : ∀ z ∈ U, |b z 1| ≤ H) :
    ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ (6 * H + 2) ^ 2 ∧
      ∀ z ∈ U, (fun e => ⌊velocity z e / fine⌋) ∈ V := by
  classical
  by_cases hU : U.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hU
    have hfirst (z : Ω) (hz : z ∈ U) : |b z 0 - b z₀ 0| ≤ a := by
      have hlo := Int.floor_le (b z 0 / a)
      have hhi := Int.lt_floor_add_one (b z 0 / a)
      have hlo₀ := Int.floor_le (b z₀ 0 / a)
      have hhi₀ := Int.lt_floor_add_one (b z₀ 0 / a)
      rw [hbin z hz] at hlo hhi
      rw [hbin z₀ hz₀] at hlo₀ hhi₀
      have hl := (le_div_iff₀ ha).mp hlo
      have hh := (div_lt_iff₀ ha).mp hhi
      have hl₀ := (le_div_iff₀ ha).mp hlo₀
      have hh₀ := (div_lt_iff₀ ha).mp hhi₀
      rw [abs_le]
      constructor <;> linarith
    have hsecond (z : Ω) (hz : z ∈ U) : |b z 1 - b z₀ 1| ≤ 2 * H := by
      exact (abs_sub _ _).trans (by linarith [hbound z hz, hbound z₀ hz₀])
    have hdiam (z : Ω) (hz : z ∈ U) (e : Fin 2) :
        |velocity z e - velocity z₀ e| ≤ 3 * H * a := by
      have heq : velocity z e - velocity z₀ e =
          M e 0 * (b z 0 - b z₀ 0) + M e 1 * (b z 1 - b z₀ 1) := by
        rw [hcoord z hz e, hcoord z₀ hz₀ e]
        simp only [Fin.sum_univ_two]
        ring
      rw [heq]
      calc
        _ ≤ |M e 0 * (b z 0 - b z₀ 0)| + |M e 1 * (b z 1 - b z₀ 1)| :=
          abs_add_le _ _
        _ = |M e 0| * |b z 0 - b z₀ 0| + |M e 1| * |b z 1 - b z₀ 1| := by
          rw [abs_mul, abs_mul]
        _ ≤ H * a + a * (2 * H) := add_le_add
          (mul_le_mul (hmajor e) (hfirst z hz) (abs_nonneg _) hH)
          (mul_le_mul (hminor e) (hsecond z hz) (abs_nonneg _) ha.le)
        _ = _ := by ring
    have hR : 0 ≤ 3 * H * a := by positivity
    obtain ⟨V, hV, hmem⟩ := exists_cells_tilted (velocity z₀ 0) (velocity z₀ 1)
      0 (3 * H * a) (3 * H * a) fine hf hR hR
    refine ⟨V, ?_, ?_⟩
    · simp only [abs_zero, mul_zero, add_zero] at hV
      have hratio : 2 * (3 * H * a) / fine + 2 ≤ 6 * H + 2 := by
        have hnum : 2 * (3 * H * a) ≤ 6 * H * fine := by
          nlinarith [mul_le_mul_of_nonneg_left haf (by positivity : 0 ≤ 6 * H)]
        linarith [(div_le_iff₀ hf).mpr hnum]
      exact hV.trans (by
        simpa only [pow_two] using mul_le_mul hratio hratio (by positivity) (by positivity))
    · intro z hz
      have hh := hmem (velocity z 0) (velocity z 1) (hdiam z hz 0)
        (by simpa only [zero_mul, sub_zero] using hdiam z hz 1)
      convert hh using 1
      ext e
      fin_cases e <;> rfl
  · refine ⟨∅, by simp; positivity, ?_⟩
    intro z hz
    exact (hU ⟨z, hz⟩).elim

end
end Submission.Obl.k4_finite_affine_parent_sources
