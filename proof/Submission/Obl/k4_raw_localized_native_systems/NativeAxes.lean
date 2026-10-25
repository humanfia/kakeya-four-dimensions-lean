/- Adapted from this LOT tree, o197, session x0690, NativeAxes.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.ScalarCoefficients
import Submission.Obl.k4_raw_localized_native_systems.Pairing.ChartStrips
import Submission.Lib.K4FinitePlankAtlases.PlankFrame

namespace Submission.Obl.k4_raw_localized_native_systems

open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def tangentOfNormal (n : Plane) : Plane := -Pairing.rot90 n

theorem tangentOfNormal_norm (n : Plane) : ‖tangentOfNormal n‖ = ‖n‖ := by
  simp only [tangentOfNormal, norm_neg, Pairing.norm_rot90]

theorem tangentOfNormal_orthogonal (n : Plane) : inner ℝ (tangentOfNormal n) n = 0 := by
  simp only [tangentOfNormal, inner_neg_left, Pairing.inner_rot90_self, neg_zero]

theorem unit_tangent_components {e : Plane} (he : ‖e‖ = 1) :
    (planarTangent e) 0 = 0 ∧ (planarTangent e 1) ^ 2 + (planarTangent e 2) ^ 2 = 1 := by
  have h := Pairing.norm_sq_fin2' e
  simp only [he, one_pow] at h
  exact ⟨rfl, h.symm⟩

theorem unit_tangent_bound {e : Plane} (he : ‖e‖ = 1) (i : Fin 3) :
    |planarTangent e i| ≤ 1 := by
  have hc (j : Fin 2) : |e j| ≤ 1 := by
    simpa only [Real.norm_eq_abs, he] using PiLp.norm_apply_le e j
  fin_cases i
  · norm_num [planarTangent]
  · exact hc 0
  · exact hc 1

theorem tangentOfNormal_frame (n : Plane) (g : ℝ) :
    Submission.Lib.K4FinitePlankAtlases.plankFrame 1 g (tangentOfNormal n) n =
      ![![(planarTangent (tangentOfNormal n)) 1,
          -g * (planarTangent (tangentOfNormal n)) 2],
        ![(planarTangent (tangentOfNormal n)) 2,
          g * (planarTangent (tangentOfNormal n)) 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.Lib.K4FinitePlankAtlases.plankFrame, planarTangent,
      tangentOfNormal, Pairing.rot90]

end
end Submission.Obl.k4_raw_localized_native_systems
