import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.AffineExit
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.HessianPatch

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open Set Metric MeasureTheory MvPolynomial QuadraticTube

noncomputable section

namespace AffineExit

/-- The affine exit has a heavy inner ball and a doubled certified ball,
with the original base law and an explicit fixed power mass loss. -/
theorem affine_ball_certificate (μ : Measure Base)
    (hμ0 : μ univ ≠ 0) (hμfin : μ univ ≠ ⊤)
    (hsupp : μ (closedBall (0:Base) (1/2))ᶜ=0)
    {A H E : ℝ} (hA : 2 ≤ A) (hH : 1 ≤ H)
    (f:Base → ℝ) (c:ℝ) (L:Base →L[ℝ] ℝ)
    (hc : |c| ≤ H) (hL : ∀ i:Fin 3, |L (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤ H)
    (hfit : ∀ u∈closedBall (0:Base) 1, |f u-c-L u| ≤ E) :
    ∃ cq:Base, ∃ Q:Poly, ‖cq‖ ≤ 1/2 ∧ Q.totalDegree ≤ 2 ∧
      (∀ m, |Q.coeff m| ≤ 5*H) ∧
      μ univ ≤ ENNReal.ofReal (A^21)*μ (ball cq (A^2)⁻¹) ∧
      ∀ u∈closedBall cq (2*(A^2)⁻¹), ∀ w:ℝ,
        |ev Q u w| ≤ E+|w-f u| ∧ ev (pderiv (3:Fin 4) Q) u w=1 ∧
          ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u w=0 := by
  let G := closedBall (0:Base) (1/2)
  have hGae : G =ᵐ[μ] univ := by
    have hs : ∀ᵐ x ∂μ,x∈G := by rw [ae_iff]; exact hsupp
    filter_upwards [hs] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩
  have hmass : μ univ/2 ≤ μ G := by
    rw [measure_congr hGae]
    calc
      _ ≤ μ univ/2+μ univ/2 := le_add_right le_rfl
      _ = _ := ENNReal.add_halves _
  obtain ⟨cq,hcq,hm⟩ := MeasureNorming.heavy_regular_ball μ G measurableSet_closedBall
    (fun _ hx => hx) hμ0 hμfin hmass hA 2
  obtain ⟨Q,hQ,hcoef,hQprop⟩ := affine_certificate f c L hH hc hL hfit
  have hA0 : 0 < A := by linarith only [hA]
  have hr : (A^2)⁻¹ ≤ 1/4 := by
    rw [show (1:ℝ)/4=(2^2:ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hA 2)
  have hcqnorm : ‖cq‖ ≤ 1/2 := by simpa only [G,mem_closedBall,dist_zero_right] using hcq
  refine ⟨cq,Q,hcqnorm,hQ,hcoef,?_,?_⟩
  · have hcoef : 2*A^(3*2+14) ≤ A^21 := by
      calc
        _ ≤ A*A^(3*2+14) := mul_le_mul_of_nonneg_right hA (by positivity)
        _ = _ := by norm_num; ring
    exact hm.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef)
      (measure_mono (fun _ hx => hx.2)))
  · intro u hu w
    have hd := hu
    rw [mem_closedBall,dist_eq_norm] at hd
    have htri : ‖u‖ ≤ ‖u-cq‖+‖cq‖ := by
      convert norm_add_le (u-cq) cq using 1 <;> simp
    have hu1 : u∈closedBall (0:Base) 1 := by
      rw [mem_closedBall,dist_zero_right]
      linarith only [htri,hd,hcqnorm,hr]
    exact hQprop u hu1 w

end AffineExit

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
