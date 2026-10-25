import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom

/-! Reuse the accepted affine parent zoom and its exact polynomial transport. -/

namespace Submission.Obl.k4_row_parent_contact_candidates

noncomputable section

abbrev Zoom := Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom

namespace Zoom

abbrev time (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time Z
abbrev untime (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.untime Z
abbrev pos (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pos Z
abbrev unpos (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.unpos Z
abbrev coeff (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff Z
abbrev Ok (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.Ok Z
abbrev untime_time {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.untime_time Z
abbrev time_untime {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.time_untime Z
abbrev unpos_pos {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.unpos_pos Z
abbrev pos_unpos {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pos_unpos Z
abbrev pos_point {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pos_point Z
abbrev point_untime {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.point_untime Z
abbrev coeff_three {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff_three Z
abbrev coeff_four {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff_four Z
abbrev coeff_zero {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff_zero Z
abbrev coeff_one {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff_one Z
abbrev measurable_coeff {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.measurable_coeff Z
abbrev subst (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.subst Z
abbrev unsubst (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.unsubst Z
abbrev lift (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.lift Z
abbrev push (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.push Z
abbrev eval_subst {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_subst Z
abbrev eval_unsubst {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_unsubst Z
abbrev subst_degree {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.subst_degree Z
abbrev unsubst_degree {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.unsubst_degree Z
abbrev lift_degree {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.lift_degree Z
abbrev push_degree {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.push_degree Z
abbrev eval_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_lift Z
abbrev eval_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_push Z
abbrev pderiv_subst {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_subst Z
abbrev pderiv_unsubst {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_unsubst Z
abbrev pderiv_bind₁_hidden := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_bind₁_hidden
abbrev pderiv_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_lift Z
abbrev pderiv_pderiv_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_pderiv_lift Z
abbrev pderiv_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_push Z
abbrev pderiv_pderiv_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pderiv_pderiv_push Z
abbrev eval_pderiv_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_pderiv_lift Z
abbrev eval_pderiv_pderiv_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_pderiv_pderiv_lift Z
abbrev eval_pderiv_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_pderiv_push Z
abbrev eval_pderiv_pderiv_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.eval_pderiv_pderiv_push Z
abbrev lift_push {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.lift_push Z
abbrev push_lift {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.push_lift Z
abbrev Fits := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.Fits
abbrev lift_fits {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.lift_fits Z
abbrev push_fits {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.push_fits Z
abbrev liftBudget (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.liftBudget Z
abbrev one_le_liftBudget {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.one_le_liftBudget Z
abbrev coeffL1_C_mul_sub_C := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeffL1_C_mul_sub_C
abbrev coeffL1_subst_le {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeffL1_subst_le Z
abbrev coeff_lift_le {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeff_lift_le Z
abbrev pushBudget (Z : Zoom) := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.pushBudget Z
abbrev one_le_pushBudget {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.one_le_pushBudget Z
abbrev coeffL1_C_add_C_mul_X := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeffL1_C_add_C_mul_X
abbrev coeffL1_unsubst_le {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeffL1_unsubst_le Z
abbrev coeffL1_push_le {Z : Zoom} := @Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom.coeffL1_push_le Z

end Zoom

end

end Submission.Obl.k4_row_parent_contact_candidates
