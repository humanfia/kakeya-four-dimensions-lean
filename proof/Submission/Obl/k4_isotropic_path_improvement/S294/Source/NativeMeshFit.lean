-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeMeshFit, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldSupportDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.Qualification.Jets2

noncomputable section

/-- Native MK4 accuracy also resolves the graph mesh itself. -/
theorem native_mesh_le_fit {b Kg d theta : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hKg : 1 ≤ Kg) (hd : 0 ≤ d)
    (hfit : 80*Kg^7*b^((1-d)/24) ≤ theta) : b ≤ theta := by
  have hp : b ≤ b^((1-d)/24) :=
    Real.self_le_rpow_of_le_one hb.le hb1 (by linarith)
  have hK : (1:ℝ) ≤ Kg^7 := one_le_pow₀ hKg
  have hpow : 0 ≤ b^((1-d)/24) := Real.rpow_nonneg hb.le _
  calc
    b ≤ b^((1-d)/24) := hp
    _ ≤ 80*Kg^7*b^((1-d)/24) := by nlinarith only [hK,hpow]
    _ ≤ theta := hfit

/-- The exact dyadic coefficient width of the MK4 graph has native accuracy. -/
theorem native_dyadic_width_le_fit (n : ℕ) {Kg d theta : ℝ}
    (hKg : 1 ≤ Kg) (hd : 0 ≤ d)
    (hfit : 80*Kg^7*Submission.Lib.K4DyadicRowScales.mesh n^((1-d)/24) ≤ theta) :
    dyadicParameterWidth (3*n) ≤ theta := by
  rw [← mk4_mesh_dyadic]
  apply native_mesh_le_fit (Submission.Lib.K4DyadicRowScales.mesh_pos n) _ hKg hd hfit
  unfold Submission.Lib.K4DyadicRowScales.mesh
  exact pow_le_one₀ (Submission.Lib.K4DyadicRowScales.unit_pos n).le
    (Submission.Lib.K4DyadicRowScales.unit_le_one n)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
