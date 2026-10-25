import Submission.Obl.k4_scalar_normalized_exact_refinement.Interfaces
import Submission.Obl.k4_scalar_normalized_exact_refinement.Angular

/-!
# The angular-transfer stage

`Stages.AngularTransfer` from `joint_density_exists` and `Analysis.RefData.angular_cap`.
-/

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

theorem angularTransfer_stage : Stages.AngularTransfer := by
  intro p q r b h hp hqraw hqpure hr hrL _hrb hbL hLq hS hU href
  obtain ⟨R⟩ := RefData.nonempty (p := p) (q := q) (r := r) (b := b) (h := h) href
  obtain ⟨a, ha⟩ := joint_density_exists (q := q) hqraw hqpure
  have hUle : Code.U q ≤ Code.U p := by
    have hLp : 0 < Code.L p := RawScalar.L_pos (Exact.raw hp)
    have hUp : 0 < Code.U p := RawScalar.U_pos (Exact.raw hp)
    have hU' : Code.U q = Code.U p * (Code.L p - r) / Code.L p := hU
    rw [hU', mul_div_assoc]
    have h1 : (Code.L p - r) / Code.L p ≤ 1 := by
      rw [div_le_one hLp]
      linarith
    nlinarith
  refine ⟨a, ?_, ?_⟩
  · intro k γ u _ _
    exact ha k γ u
  · intro u τ hu huU hτ
    exact R.angular_cap hp hqraw hqpure hr hbL hLq hS hUle a (fun k i u _ _ => ha k i u)
      u τ hu huU hτ

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
