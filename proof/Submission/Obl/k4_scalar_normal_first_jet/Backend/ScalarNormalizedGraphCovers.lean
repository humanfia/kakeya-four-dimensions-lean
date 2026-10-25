/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalizedGraphCovers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalizedGraphCovers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGraphCovers

/-! The two normalized collision graphs inherit their exact covering
constants from the original scalar Lipschitz comparisons. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable def swapScalarPlane : ScalarPlane ≃ₗᵢ[ℝ] ScalarPlane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

theorem swapScalarPlane_apply (x y : ℝ) :
    swapScalarPlane !₂[x, y] = !₂[y, x] := by
  ext i
  fin_cases i <;> simp [swapScalarPlane, Equiv.piCongrLeft'_apply]

theorem diagonal_graph_planeAD {p K e : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (he : e ^ 2 = 1) (S : Set ℝ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * |x - y|) :
    PlaneAD p (4 * (K + 1) + 3) ((fun x => diagonalPoint e x (f x)) '' S) := by
  have h := similarity_graph_planeAD (a := (Real.sqrt 2)⁻¹) hp hK
    (signedPlaneRotation e he) 0 S f hf
  simpa only [diagonalPoint_eq_scale e he, add_zero, graphPoint] using h

theorem boxed_graph_planeAD {p K e B : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (he : e ^ 2 = 1) (S : Set ℝ) (f : ℝ → ℝ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ K * |x - y|) :
    PlaneAD p (4 * (K + 1) + 3) ((fun x => boxedDiagonalPoint e B (f x) x) '' S) := by
  have h := similarity_graph_planeAD (a := (2 * B)⁻¹ * (Real.sqrt 2)⁻¹) hp hK
    (swapScalarPlane.trans (signedPlaneRotation e he)) (!₂[1 / 2, 1 / 2]) S f hf
  simpa only [boxedDiagonalPoint, diagonalPoint_eq_scale e he, smul_smul,
    LinearIsometryEquiv.trans_apply, graphPoint, swapScalarPlane_apply] using h

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
