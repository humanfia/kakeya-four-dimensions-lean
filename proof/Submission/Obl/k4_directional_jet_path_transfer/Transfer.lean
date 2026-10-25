import Submission.Obl.k4_directional_jet_path_transfer.Affine
import Submission.Obl.k4_directional_jet_path_transfer.Powers

open Metric Set

namespace Submission.Obl.k4_directional_jet_path_transfer

/-- The directional propagation hypothesis of the frozen statement. -/
def SliceLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N : ℕ) (K A : ℝ) (H : E → ℂ) (U : Set E) : Prop :=
  ∀ p v : E,
    (∀ t ∈ thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1), p + t • v ∈ U) →
    ∀ V : ℝ, 0 ≤ V →
    (∀ j : ℕ, j ≤ N → ‖iteratedDeriv j (fun t : ℂ => H (p + t • v)) 0‖ ≤ V) →
    ‖H (p + v)‖ ≤ (8 * A) ^ K * V

/-- Conversion of a finite ball bound into a jet bound at its center. -/
lemma jets_of_ball_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {A : ℝ} (hA : 2 ≤ A) {q : ℕ} {J : ℝ}
    (hJ : ∀ j : ℕ, j ≤ q → cauchyConstant j * (8 * A) ^ j ≤ A ^ J)
    {p : E} (hball : closedBall p ((8 * A)⁻¹) ⊆ U)
    {V : ℝ} (hV : 0 ≤ V)
    (hb : ∀ z ∈ closedBall p ((8 * A)⁻¹), ‖H z‖ ≤ V) :
    ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H p‖ ≤ A ^ J * V := by
  intro j hj
  have hR : 0 < (8 * A)⁻¹ := by positivity
  have hc := norm_iteratedFDeriv_le_ball hU hH j hR hball hV hb
  simp only [inv_inv] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right (hJ j hj) hV)

/-- A directional propagation step from Fréchet jets, with the slice norm included in the loss. -/
lemma slice_bound_of_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {A : ℝ} (hA : 2 ≤ A) {N : ℕ} {K D : ℝ}
    (hlaw : SliceLaw N K A H U)
    (hD : (8 * A) ^ K * (3 : ℝ) ^ N ≤ A ^ D)
    {p z : E} (hp : p ∈ U) (hv : ‖z - p‖ ≤ 3)
    (hgeom : ∀ t ∈ thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1),
      p + t • (z - p) ∈ U)
    {V : ℝ} (hV : 0 ≤ V)
    (hjet : ∀ j : ℕ, j ≤ N → ‖iteratedFDeriv ℂ j H p‖ ≤ V) :
    ‖H z‖ ≤ A ^ D * V := by
  have hord (j : ℕ) (hj : j ≤ N) :
      ‖iteratedDeriv j (fun t : ℂ => H (p + t • (z - p))) 0‖ ≤ (3 : ℝ) ^ N * V := by
    calc
      _ ≤ ‖iteratedFDeriv ℂ j H p‖ * ‖z - p‖ ^ j :=
        norm_iteratedDeriv_affine_slice_le hU hH hp (z - p) j
      _ ≤ V * (3 : ℝ) ^ N := mul_le_mul (hjet j hj)
        ((pow_le_pow_left₀ (norm_nonneg _) hv j).trans
          (pow_le_pow_right₀ (by norm_num) hj)) (by positivity) hV
      _ = (3 : ℝ) ^ N * V := mul_comm _ _
  have h := hlaw p (z - p) hgeom ((3 : ℝ) ^ N * V) (by positivity) hord
  simp only [add_sub_cancel] at h
  calc
    ‖H z‖ ≤ (8 * A) ^ K * ((3 : ℝ) ^ N * V) := h
    _ = ((8 * A) ^ K * (3 : ℝ) ^ N) * V := by ring
    _ ≤ A ^ D * V := mul_le_mul_of_nonneg_right hD hV

/-- A directional propagation step from a bound on a ball. -/
lemma slice_bound_of_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {A : ℝ} (hA : 2 ≤ A) {N : ℕ} {K D J : ℝ}
    (hlaw : SliceLaw N K A H U)
    (hD : (8 * A) ^ K * (3 : ℝ) ^ N ≤ A ^ D)
    (hJ : ∀ j : ℕ, j ≤ N → cauchyConstant j * (8 * A) ^ j ≤ A ^ J)
    {p z : E} (hp : p ∈ U)
    (hball : closedBall p ((8 * A)⁻¹) ⊆ U) (hv : ‖z - p‖ ≤ 3)
    (hgeom : ∀ t ∈ thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1),
      p + t • (z - p) ∈ U)
    {V : ℝ} (hV : 0 ≤ V)
    (hb : ∀ w ∈ closedBall p ((8 * A)⁻¹), ‖H w‖ ≤ V) :
    ‖H z‖ ≤ A ^ (D + J) * V := by
  have hjet := jets_of_ball_bound hU hH hA hJ hball hV hb
  have ht := slice_bound_of_jets hU hH hA hlaw hD hp hv hgeom
    (show 0 ≤ A ^ J * V by positivity) hjet
  simpa only [Real.rpow_add (show 0 < A by linarith), mul_assoc] using ht

end Submission.Obl.k4_directional_jet_path_transfer
