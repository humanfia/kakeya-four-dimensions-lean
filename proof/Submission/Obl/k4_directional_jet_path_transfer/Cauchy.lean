import Mathlib

open Metric Set

namespace Submission.Obl.k4_directional_jet_path_transfer

/-- Constants for iterated Schwarz estimates on concentric balls. -/
def cauchyConstant : ℕ → ℝ
  | 0 => 1
  | j + 1 => 4 * 2 ^ j * cauchyConstant j

lemma cauchyConstant_pos (j : ℕ) : 0 < cauchyConstant j := by
  induction j with
  | zero => norm_num [cauchyConstant]
  | succ j hj => simpa only [cauchyConstant] using mul_pos (by positivity) hj

/-- A ball bound controls each Fréchet derivative; the constant is independent of dimension. -/
lemma norm_iteratedFDeriv_le_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} (hU : IsOpen U) {H : E → F}
    (hH : ContDiffOn ℂ ((⊤ : ENat) : WithTop ENat) H U)
    (j : ℕ) {p : E} {R V : ℝ} (hR : 0 < R)
    (hball : closedBall p R ⊆ U) (hV : 0 ≤ V)
    (hbound : ∀ z ∈ closedBall p R, ‖H z‖ ≤ V) :
    ‖iteratedFDeriv ℂ j H p‖ ≤ cauchyConstant j * R⁻¹ ^ j * V := by
  induction j generalizing p R V with
  | zero => simpa [cauchyConstant] using hbound p (mem_closedBall_self hR.le)
  | succ j ih =>
    have hhalf : 0 < R / 2 := by positivity
    let B := cauchyConstant j * (R / 2)⁻¹ ^ j * V
    have hlocal (z : E) (hz : z ∈ ball p (R / 2)) :
        ‖iteratedFDeriv ℂ j H z‖ ≤ B := by
      have hsub : closedBall z (R / 2) ⊆ closedBall p R := by
        intro w hw
        rw [mem_closedBall] at hw ⊢
        calc
          dist w p ≤ dist w z + dist z p := dist_triangle _ _ _
          _ ≤ R / 2 + R / 2 := add_le_add hw (mem_ball.mp hz).le
          _ = R := by ring
      exact ih hhalf (hsub.trans hball) hV (fun w hw => hbound w (hsub hw))
    have hdiff : DifferentiableOn ℂ (iteratedFDeriv ℂ j H) (ball p (R / 2)) := by
      intro z hz
      have hzU : z ∈ U := hball (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
      exact ((hH.contDiffAt (hU.mem_nhds hzU)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top j)).differentiableWithinAt
    have hmaps : MapsTo (iteratedFDeriv ℂ j H) (ball p (R / 2))
        (closedBall (iteratedFDeriv ℂ j H p) (2 * B)) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm]
      calc
        ‖iteratedFDeriv ℂ j H z - iteratedFDeriv ℂ j H p‖ ≤
            ‖iteratedFDeriv ℂ j H z‖ + ‖iteratedFDeriv ℂ j H p‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hlocal z hz) (hlocal p (mem_ball_self hhalf))
        _ = 2 * B := by ring
    have hh := Complex.norm_fderiv_le_div_of_mapsTo_ball hdiff hmaps hhalf
    rw [norm_fderiv_iteratedFDeriv] at hh
    calc
      ‖iteratedFDeriv ℂ (j + 1) H p‖ ≤ 2 * B / (R / 2) := hh
      _ = cauchyConstant (j + 1) * R⁻¹ ^ (j + 1) * V := by
        simp only [B, cauchyConstant, inv_div, pow_succ]
        field_simp
        ring

end Submission.Obl.k4_directional_jet_path_transfer
