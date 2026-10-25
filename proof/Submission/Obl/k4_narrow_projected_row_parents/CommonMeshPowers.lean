import Submission.Obl.k4_narrow_projected_row_parents.ModelBridge
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter
open Submission.Obl.k4_general_parent_projected_layers

/-- Any common-frame width in a fixed power band admits one finer physical
mesh. This is uniform in the actual width and in the zoom mesh. -/
theorem eventually_common_mesh_resolution (p : Parameters) (hp : p.Valid) (E T : ℝ) :
    ∀ᶠ k in atTop, ∀ w σ : ℝ, p.N k ^ (-E) ≤ w → p.N k ^ (-T) ≤ σ →
      (2 * p.K k + 1) * p.N k ^ (-(E + T + 1)) ≤ 100 * w * σ := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.2.1 hp.2.2.1.1 hp.2.2.1.2 1
    (a := -(E + T + 1)) (b := -(E + T)) (by linarith)
    (A := 3) (by norm_num)
  filter_upwards [hsmall] with k hk
  intro w σ hw hσ
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hw0 : 0 ≤ w := (Real.rpow_pos_of_pos hN0 _).le.trans hw
  have hσ0 : 0 ≤ σ := (Real.rpow_pos_of_pos hN0 _).le.trans hσ
  calc (2 * p.K k + 1) * p.N k ^ (-(E + T + 1))
      ≤ 3 * p.K k * p.N k ^ (-(E + T + 1)) := by
          gcongr
          linarith [hp.2.2.1.1 k]
    _ ≤ p.N k ^ (-(E + T)) := by simpa only [pow_one] using hk.le
    _ = p.N k ^ (-E) * p.N k ^ (-T) := by
          rw [← Real.rpow_add hN0]
          congr 1
          ring
    _ ≤ w * σ := mul_le_mul hw hσ (Real.rpow_nonneg hN0.le _) hw0
    _ ≤ 100 * w * σ := by nlinarith [mul_nonneg hw0 hσ0]

end Submission.Obl.k4_narrow_projected_row_parents
