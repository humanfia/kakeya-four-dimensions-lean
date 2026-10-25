/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGraphCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGraphCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlaneRotation
import Submission.WZ.Obl.wz_slab_local_linearity.CellDichotomy

/-! Uniform plane covering bounds for all rotations, translations and
scalar dilations of a Lipschitz graph. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

theorem scalarPlane_coordinate_dist_le (p q : ScalarPlane) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  have h := PiLp.norm_apply_le (p - q) i
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using h

/-- The AD constant of a scalar graph is unchanged by a common similarity.
The inverse isometry's first coordinate supplies the parameter in the
prebuilt bi-Lipschitz covering theorem. -/
theorem similarity_graph_planeAD {p K a : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (E : ScalarPlane ≃ₗᵢ[ℝ] ScalarPlane) (b : ScalarPlane) (S : Set ℝ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * |x - y|) :
    PlaneAD p (4 * (K + 1) + 3) ((fun x => a • E (graphPoint f x) + b) '' S) := by
  let γ : ℝ → ScalarPlane := fun x => a • E (graphPoint f x) + b
  let u : ScalarPlane → ℝ := fun q => (E.symm (q - b)) 0
  have hu x : u (γ x) = a * x := by
    dsimp [u, γ]
    rw [add_sub_cancel_right, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hd x y : dist (γ x) (γ y) = |a| * dist (graphPoint f x) (graphPoint f y) := by
    dsimp [γ]
    rw [dist_add_right, dist_smul₀, LinearIsometryEquiv.dist_map, Real.norm_eq_abs]
  have h₁ : ∀ q ∈ γ '' S, ∀ q' ∈ γ '' S, |u q - u q'| ≤ 1 * dist q q' := by
    intro q hq q' hq'
    have h := scalarPlane_coordinate_dist_le (E.symm (q - b)) (E.symm (q' - b)) 0
    rw [LinearIsometryEquiv.dist_map, dist_sub_right] at h
    simpa only [one_mul] using h
  have h₂ : ∀ q ∈ γ '' S, ∀ q' ∈ γ '' S, dist q q' ≤ (K + 1) * |u q - u q'| := by
    rintro q ⟨x, hx, rfl⟩ q' ⟨y, hy, rfl⟩
    have hgraph : dist (graphPoint f x) (graphPoint f y) ≤ (K + 1) * |x - y| := by
      have h := CellProofs.dist_pt_le x (f x) y (f y)
      have hxy := hf x hx y hy
      change dist (graphPoint f x) (graphPoint f y) ≤ |x - y| + |f x - f y| at h
      nlinarith only [h, hxy]
    rw [hd, hu, hu, ← mul_sub, abs_mul]
    calc
      |a| * dist (graphPoint f x) (graphPoint f y) ≤ |a| * ((K + 1) * |x - y|) :=
        mul_le_mul_of_nonneg_left hgraph (abs_nonneg _)
      _ = (K + 1) * (|a| * |x - y|) := by ring
  have h := CellProofs.adset_of_biLipschitz hp (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 < K + 1) h₁ h₂
  simpa only [one_mul, mul_one] using h.planeAD

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
