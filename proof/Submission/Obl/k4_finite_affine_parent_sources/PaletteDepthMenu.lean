-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_homogeneous_native_pair_preparation.DepthGrid
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_finite_affine_parent_sources.Original

namespace Submission.Obl.k4_finite_affine_parent_sources

open Set

/-- A finite menu for angular tests never uses depth zero. Every tested
positive depth has a coarser menu point, within the fixed mesh. -/
theorem exists_positive_angular_depth_menu {a b mesh : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hmesh : 0 < mesh) (hma : mesh < a) :
    ∃ Q : Finset ℝ, (∀ r ∈ Q, 0 < r ∧ r ≤ b) ∧
      ∀ t ∈ Icc a b, ∃ r ∈ Q, t - mesh ≤ r ∧ r ≤ t := by
  classical
  obtain ⟨Q, -, -, hQ, hcover⟩ :=
    Submission.Obl.k4_homogeneous_native_pair_preparation.exists_depth_grid
      (ha.le.trans hab) hmesh
  refine ⟨Q.filter (fun r => 0 < r), ?_, ?_⟩
  · intro r hr
    exact ⟨(Finset.mem_filter.mp hr).2, (hQ r (Finset.mem_filter.mp hr).1).2⟩
  · intro t ht
    obtain ⟨r, hr, hrt, htr⟩ := hcover t ⟨ha.le.trans ht.1, ht.2⟩
    have hr0 : 0 < r := by linarith [ht.1]
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, hr0⟩, by linarith, hrt⟩

/-- Rounding angular depth down makes the original planar bin at least
as wide as the tested native bin. This is the orientation-cover premise. -/
theorem native_velocity_width_le_original {N unit L v r : ℝ}
    (hN : 1 ≤ N) (hr : r ≤ unit * L * v) :
    (N ^ (unit * L)) ^ (-v) ≤ δ N r := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  rw [← Real.rpow_mul hN0.le]
  calc
    _ ≤ N ^ (-r) := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
    _ ≤ _ := (Submission.Obl.k4_profile_density_bounds.width_bounds hN0 r).1

end Submission.Obl.k4_finite_affine_parent_sources
