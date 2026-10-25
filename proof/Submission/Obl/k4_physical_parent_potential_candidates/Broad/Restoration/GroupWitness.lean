-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/GroupWitness.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/GroupWitness.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenTests
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.BranchBand

/-!
# Line witnesses from points of the group's native sheet

A producer of the sampled exit knows its group lines and the normalized native polynomials
`S0`, `P0`, but not the branch `f` (built later). It supplies tubes of *normalized group
points*: small native fit, hidden derivative in a window, the branch's sign. The tube estimate
`band_of_native_fit` then puts the line's hidden coordinate within `εfit A₁¹⁹` of `f`, which is
exactly the `NativeLineWitness` consumed by the seven tests.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- A normalized point of the group's native sheet. -/
def NormalizedGroupPoint (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (εfit A₁ σ : ℝ)
    (z : Base) (w : ℝ) : Prop :=
  z ∈ ball (0 : Base) 4 ∧
  |eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0| ≤ εfit ∧
  0 < eval ![z 0, z 1, z 2, w] (pderiv 3 S0) * σ ∧
  A₁⁻¹ ≤ |eval ![z 0, z 1, z 2, w] (pderiv 3 S0)| ∧
  |eval ![z 0, z 1, z 2, w] (pderiv 3 S0)| ≤ A₁

/-- A long tube of normalized group points near the point `u` and direction `p`. -/
def GroupTubeWitness (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (εfit A₁ σ At θ h : ℝ)
    (u p : Base) : Prop :=
  ∃ (y v : Base) (w₀ w₁ : ℝ) (Et : Set ℝ),
    y ∈ closedBall (0 : Base) 1 ∧ ‖v‖ ≤ At ∧ ‖u - y‖ ≤ h ∧ ‖p - v‖ ≤ h ∧
    MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧ ENNReal.ofReal θ ≤ volume Et ∧
    ∀ t ∈ Et, NormalizedGroupPoint S0 P0 εfit A₁ σ (y + t • ((8 * At)⁻¹ • v)) (w₀ + w₁ * t)

/-- A normalized group point is within `εfit A₁¹⁹` of the branch. -/
theorem band_of_normalizedGroupPoint {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ}
    {εfit A₁ σ a : ℝ} {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hε : 0 < εfit) (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {z : Base} {w : ℝ} (hzw : NormalizedGroupPoint S0 P0 εfit A₁ σ z w) :
    |w - f z| ≤ εfit * A₁ ^ 19 := by
  obtain ⟨hz, hfit, hsign, hlo, hhi⟩ := hzw
  obtain ⟨hr, hrs⟩ := hroot z hz
  rw [hSeq] at hfit
  rw [hSd] at hsign hlo hhi
  exact (band_of_native_fit hA₁ hε hr hrs hfit hsign hlo hhi hsmall).1

/-- A tube of normalized group points is a native line witness for the branch. -/
theorem nativeLineWitness_of_groupTube {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ}
    {εfit A₁ σ a At aW b θ h : ℝ} {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hA₁t : A₁ ≤ At) (hε : 0 < εfit) (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hband : εfit * A₁ ^ 19 ≤ At * b)
    (hcurv : ∀ (z : Base) (w : ℝ), |eval ![z 0, z 1, z 2, w] (pderiv 3 (pderiv 3 S0))| ≤ At / aW)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {u p : Base} (hw : GroupTubeWitness S0 P0 εfit A₁ σ At θ h u p) :
    NativeLineWitness f S0 At aW b θ h u p := by
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, hpts⟩ := hw
  refine ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, ?_, ?_, ?_⟩
  · intro t ht
    exact (band_of_normalizedGroupPoint hA₁ hε hsmall hroot hSeq hSd (hpts t ht)).trans hband
  · intro t ht
    exact (hpts t ht).2.2.2.2.trans hA₁t
  · intro t ht
    exact hcurv _ _

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- A normalized group point that also carries the window and value of a second quadratic `Sc`
(the certificate's test, e.g. the capacity packet's native quadratic minus its bin constant).
The branch is defined by `S0 - P0`; the certificate uses `Sc`. -/
def CertifiedGroupPoint (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (Sc : Poly)
    (εfit A₁ σ Vc : ℝ) (z : Base) (w : ℝ) : Prop :=
  NormalizedGroupPoint S0 P0 εfit A₁ σ z w ∧
  A₁⁻¹ ≤ |eval ![z 0, z 1, z 2, w] (pderiv 3 Sc)| ∧
  |eval ![z 0, z 1, z 2, w] (pderiv 3 Sc)| ≤ A₁ ∧
  |eval ![z 0, z 1, z 2, w] Sc| ≤ Vc

/-- A long tube of certified group points near `(u, p)`. -/
def CertifiedTubeWitness (S0 : Poly) (P0 : MvPolynomial (Fin 3) ℝ) (Sc : Poly)
    (εfit A₁ σ Vc At θ h : ℝ) (u p : Base) : Prop :=
  ∃ (y v : Base) (w₀ w₁ : ℝ) (Et : Set ℝ),
    y ∈ closedBall (0 : Base) 1 ∧ ‖v‖ ≤ At ∧ ‖u - y‖ ≤ h ∧ ‖p - v‖ ≤ h ∧
    MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧ ENNReal.ofReal θ ≤ volume Et ∧
    ∀ t ∈ Et, CertifiedGroupPoint S0 P0 Sc εfit A₁ σ Vc (y + t • ((8 * At)⁻¹ • v)) (w₀ + w₁ * t)

/-- A tube of certified group points is a native line witness for the certificate's test. -/
theorem nativeLineWitness_of_certifiedTube {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly}
    {εfit A₁ σ Vc a At aW b θ h : ℝ} {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hA₁t : A₁ ≤ At) (hε : 0 < εfit) (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hband : εfit * A₁ ^ 19 ≤ At * b)
    (hcurv : ∀ (z : Base) (w : ℝ), |eval ![z 0, z 1, z 2, w] (pderiv 3 (pderiv 3 Sc))| ≤ At / aW)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {u p : Base} (hw : CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc At θ h u p) :
    NativeLineWitness f Sc At aW b θ h u p := by
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, hpts⟩ := hw
  refine ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, ?_, ?_, ?_⟩
  · intro t ht
    exact (band_of_normalizedGroupPoint hA₁ hε hsmall hroot hSeq hSd (hpts t ht).1).trans hband
  · intro t ht
    exact (hpts t ht).2.2.1.trans hA₁t
  · intro t ht
    exact hcurv _ _

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
