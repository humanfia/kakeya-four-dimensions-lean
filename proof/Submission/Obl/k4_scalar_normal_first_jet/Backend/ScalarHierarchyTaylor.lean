/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyTaylor.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyTaylor.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyComparison
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyPowers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicTimeGrid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFiniteSlopeChain

/-! Taylor estimates from the stored original affine hierarchy. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarGridHierarchy

theorem taylor_of_slope_comparison {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {J : Fin n → ℕ}
    {hJ : ∀ i, 0 < J i} {p : Fin n → ℝ} {B C : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (i j : Fin n)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hreading : p i ≤ 2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
    {u v : ℝ} (hu : u ∈ G.times) (hv : v ∈ G.times)
    (hcode : scalarTimeBlockCode (J i) (hJ i) u = scalarTimeBlockCode (J i) (hJ i) v)
    (hslope : |G.slope i u - G.slope j u| ≤ C * (1 / (J i : ℝ)) ^ (7 / 32 : ℝ)) :
    |F v - F u - (v - u) * G.slope j u| ≤ (4 * B + C) * (1 / (J i : ℝ)) ^ (11 / 10 : ℝ) := by
  let H : ℝ := 1 / (J i : ℝ)
  have hJpos : (0 : ℝ) < J i := Nat.cast_pos.mpr (hJ i)
  have hH : 0 < H := by dsimp [H]; positivity
  have hH1 : H ≤ 1 := by
    apply (div_le_iff₀ hJpos).mpr
    simpa using (show (1 : ℝ) ≤ J i from by exact_mod_cast (Nat.succ_le_iff.mpr (hJ i) : 1 ≤ J i))
  have herror : B * H * p i ≤ (2 * B) * H ^ (5 / 4 : ℝ) := by
    calc
      _ ≤ B * H * (2 * H ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hreading (mul_nonneg hB hH.le)
      _ = (2 * B) * (H ^ (1 : ℝ) * H ^ (1 / 4 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hH]; norm_num
  have huFit := (G.time_fit i hu).trans herror
  have hrows := G.constant_on_grid i v hv u hu hcode.symm
  have hvFit : |F v - (G.intercept i u + G.slope i u * v)| ≤ (2 * B) * H ^ (5 / 4 : ℝ) := by
    simpa only [hrows.1, hrows.2] using (G.time_fit i hv).trans herror
  have htaylor := taylor_error_of_affine_fit huFit hvFit hslope
  have hdistance : |v - u| ≤ H := scalarTimeBlockCode_time_close (hJ i)
    (G.unit_time hv) (G.unit_time hu) hcode.symm
  have hnumeric := scalar_hierarchy_taylor_bound hH hH1
    (show 0 ≤ 2 * B by positivity) hC hdistance
  exact htaylor.trans (by convert hnumeric using 1 <;> ring)

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
