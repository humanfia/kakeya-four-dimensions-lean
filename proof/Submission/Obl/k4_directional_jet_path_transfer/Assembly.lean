import Submission.Obl.k4_directional_jet_path_transfer.Transfer

open Metric Set

namespace Submission.Obl.k4_directional_jet_path_transfer

/-- The tube geometry needed for one propagation step. -/
def AdmissibleStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℝ) (U : Set E) (p d : E) : Prop :=
  ∀ z ∈ closedBall d ((8 * A)⁻¹), ‖z - p‖ ≤ 3 ∧
    ∀ t ∈ thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1), p + t • (z - p) ∈ U

/-- Two directional steps and three Cauchy estimates give the forward and reverse comparisons. -/
lemma transfer_along_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {H : E → ℂ}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    {A : ℝ} (hA : 2 ≤ A) {N q : ℕ} (hq : N ≤ q) {K D J : ℝ}
    (hDpos : 0 < D) (hJpos : 0 < J)
    (hlaw : SliceLaw N K A H U)
    (hD : (8 * A) ^ K * (3 : ℝ) ^ N ≤ A ^ D)
    (hJ : ∀ j : ℕ, j ≤ q → cauchyConstant j * (8 * A) ^ j ≤ A ^ J)
    {a b c : E}
    (hballa : closedBall a ((8 * A)⁻¹) ⊆ U)
    (hballb : closedBall b ((8 * A)⁻¹) ⊆ U)
    (hballc : closedBall c ((8 * A)⁻¹) ⊆ U)
    (hab : AdmissibleStep A U a b) (hbc : AdmissibleStep A U b c)
    (hcb : AdmissibleStep A U c b) (hba : AdmissibleStep A U b a)
    {V : ℝ} (hV : 0 ≤ V) :
    (((∀ z ∈ closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ V) →
      (∀ z ∈ closedBall c ((8 * A)⁻¹), ‖H z‖ ≤ A ^ (2 * D + 3 * J) * V) ∧
      ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ (2 * D + 3 * J) * V) ∧
    ((∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j H c‖ ≤ V) →
      ∀ z ∈ closedBall a ((8 * A)⁻¹), ‖H z‖ ≤ A ^ (2 * D + 3 * J) * V)) := by
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have hR : 0 ≤ (8 * A)⁻¹ := by positivity
  have hpa : a ∈ U := hballa (mem_closedBall_self hR)
  have hpb : b ∈ U := hballb (mem_closedBall_self hR)
  have hpc : c ∈ U := hballc (mem_closedBall_self hR)
  have hJN (j : ℕ) (hj : j ≤ N) := hJ j (hj.trans hq)
  constructor
  · intro hbound
    have hbb : ∀ z ∈ closedBall b ((8 * A)⁻¹), ‖H z‖ ≤ A ^ (D + J) * V := by
      intro z hz
      exact slice_bound_of_ball hU hH hA hlaw hD hJN hpa hballa
        (hab z hz).1 (hab z hz).2 hV hbound
    have hcc : ∀ z ∈ closedBall c ((8 * A)⁻¹),
        ‖H z‖ ≤ A ^ (2 * D + 2 * J) * V := by
      intro z hz
      calc
        ‖H z‖ ≤ A ^ (D + J) * (A ^ (D + J) * V) :=
          slice_bound_of_ball hU hH hA hlaw hD hJN hpb hballb
            (hbc z hz).1 (hbc z hz).2 (by positivity) hbb
        _ = A ^ (2 * D + 2 * J) * V := by
          rw [← mul_assoc, ← Real.rpow_add hApos]
          congr 2
          ring
    constructor
    · intro z hz
      exact (hcc z hz).trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hAone (by linarith)) hV)
    · intro j hj
      calc
        ‖iteratedFDeriv ℂ j H c‖ ≤ A ^ J * (A ^ (2 * D + 2 * J) * V) :=
          jets_of_ball_bound hU hH hA hJ hballc (by positivity) hcc j hj
        _ = A ^ (2 * D + 3 * J) * V := by
          rw [← mul_assoc, ← Real.rpow_add hApos]
          congr 2
          ring
  · intro hjet z hz
    have hbb : ∀ w ∈ closedBall b ((8 * A)⁻¹), ‖H w‖ ≤ A ^ D * V := by
      intro w hw
      exact slice_bound_of_jets hU hH hA hlaw hD hpc
        (hcb w hw).1 (hcb w hw).2 hV (fun j hj => hjet j (hj.trans hq))
    calc
      ‖H z‖ ≤ A ^ (D + J) * (A ^ D * V) :=
        slice_bound_of_ball hU hH hA hlaw hD hJN hpb hballb
          (hba z hz).1 (hba z hz).2 (by positivity) hbb
      _ = A ^ ((D + J) + D) * V := by rw [← mul_assoc, ← Real.rpow_add hApos]
      _ ≤ A ^ (2 * D + 3 * J) * V := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hAone (by linarith)) hV

end Submission.Obl.k4_directional_jet_path_transfer
