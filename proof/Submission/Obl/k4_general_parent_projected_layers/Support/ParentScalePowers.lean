/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ParentScalePowers.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Fixed-power bounds for the parent filling constant, uniform in depth. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Filter

theorem eventually_parentFilling_le (p : Parameters) (hp : p.Valid) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, ∀ s : ℝ,
      parentFilling (p.K k) (PreparedModel.width p k s) ≤ p.N k ^ (s + eps) := by
  have hN (k : ℕ) : 1 ≤ p.N k := by linarith [hp.1 k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hp.2.1 hp.2.2.1.1 hp.2.2.1.2 20 (a := 0) (b := eps) heps
    (A := 3000000) (by norm_num)
  filter_upwards [hsmall] with k hk
  intro s
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hbound : 3000000 * p.K k ^ 20 ≤ p.N k ^ eps := by simpa only [Real.rpow_zero, mul_one] using hk.le
  calc
    _ = (3000000 * p.K k ^ 20) * p.N k ^ s := by
      simp only [parentFilling, PreparedModel.width, Real.rpow_neg hN0.le, div_inv_eq_mul]
    _ ≤ p.N k ^ eps * p.N k ^ s :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN0.le _)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

theorem rpow_depth_le_parentFilling (p : Parameters) (hp : p.Valid) (k : ℕ) (s : ℝ) :
    p.N k ^ s ≤ parentFilling (p.K k) (PreparedModel.width p k s) := by
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hKpow : 1 ≤ p.K k ^ 20 := one_le_pow₀ (hp.2.2.1.1 k)
  have hfactor : 1 ≤ 3000000 * p.K k ^ 20 := by linarith
  calc
    _ = 1 * p.N k ^ s := (one_mul _).symm
    _ ≤ (3000000 * p.K k ^ 20) * p.N k ^ s :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hN0.le _)
    _ = _ := by
      simp only [parentFilling, PreparedModel.width, Real.rpow_neg hN0.le, div_inv_eq_mul]

end Submission.Obl.k4_general_parent_projected_layers
