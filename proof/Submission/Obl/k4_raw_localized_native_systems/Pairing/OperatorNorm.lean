import Submission.Obl.k4_raw_localized_native_systems.Pairing.ChartStrips

/- Adapted from this LOT tree, o197, session x0690, Pairing/ShortLabels.lean,
   snapshot 9f1b6476, adapted there from o178/x0596 at aff0309c. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

theorem norm_toEuclideanLin_le_longCol (Q : Matrix (Fin 2) (Fin 2) ℝ) (w : Plane) :
    ‖Matrix.toEuclideanLin Q w‖ ≤ 2 * ‖longCol Q‖ * ‖w‖ := by
  rw [toEuclideanLin_fin2_eq]
  obtain ⟨h0, h1⟩ := longCol_norm_ge Q
  have hw0 := abs_coord_le_norm_fin2 w 0
  have hw1 := abs_coord_le_norm_fin2 w 1
  calc ‖w 0 • col0 Q + w 1 • col1 Q‖ ≤ ‖w 0 • col0 Q‖ + ‖w 1 • col1 Q‖ := norm_add_le _ _
    _ = |w 0| * ‖col0 Q‖ + |w 1| * ‖col1 Q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖w‖ * ‖longCol Q‖ + ‖w‖ * ‖longCol Q‖ := by
        gcongr
    _ = 2 * ‖longCol Q‖ * ‖w‖ := by ring


end
end Submission.Obl.k4_raw_localized_native_systems.Pairing
