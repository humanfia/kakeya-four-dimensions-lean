import Submission.Obl.k4_physical_parent_potential_candidates.FubiniC2Bounds
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniNumerator

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MvPolynomial FubiniJets FubiniHessian

noncomputable section

namespace HessianPatchBounds

theorem mono {f : FubiniBase → ℝ} {K M : ℝ} (hb : HessianPatchBounds f K) (hKM : K ≤ M) :
    HessianPatchBounds f M := {
  value := fun x hx => (hb.value x hx).trans hKM
  gradient := fun x hx i => (hb.gradient x hx i).trans hKM
  hessian := fun x hx i j => (hb.hessian x hx i j).trans hKM
  cubic := fun x hx i j k => (hb.cubic x hx i j k).trans hKM
  fourth := fun x hx i j k l => (hb.fourth x hx i j k l).trans hKM
  inverse := fun x hx i j => (hb.inverse x hx i j).trans hKM }

end HessianPatchBounds

/-- Complete local restoration from a C²-small implicit numerator, with
all denominator and logarithmic-connection conditioning derived from ordinary
graph jets, the normalized hidden derivative, and two regularity floors. -/
theorem restoration_of_conditioned_implicit_numerator
    {f w : FubiniBase → ℝ} {N : FubiniBase → ConicTensor.Tensor} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U)
    (hdom : Metric.closedBall (0:FubiniBase) 1 ⊆ U)
    (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0) (hw : ContDiffOn ℝ 2 w U)
    (hprod : ∀ x ∈ U, ∀ i j k,
      N x i j k = (5*w x*(hessian f x).det)*cubicError f x i j k)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hb : ∀ n : ℕ, n ≤ 4 → ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hHreg : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, K⁻¹ ≤ |(hessian f x).det|)
    (hwreg : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, K⁻¹ ≤ |w x|)
    (hwb : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, C2Bound w K x)
    (hN0 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |N x i j k| ≤ ε)
    (hN1 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p i j k,
      |jet (fun y => N y i j k) 1 ![p] x| ≤ ε)
    (hN2 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p l i j k,
      |jet (fun y => N y i j k) 2 ![p,l] x| ≤ ε)
    (hsmall : 3000000*(frameBudget (2000*K^4))^9*(6*(2000*K^4)^5*ε) ≤ 1) :
    ∃ Q : MvPolynomial (Fin 4) ℝ,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 74*(frameBudget (2000*K^4))^4) ∧
      ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
        |eval (Fin.snoc (fun i => x i) (f x)) Q| ≤
          18000000*(frameBudget (2000*K^4))^8*(2000*K^4)^5*ε ∧
        (frameBudget (2000*K^4))⁻¹ ≤ eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ∧
        eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ≤ 3*frameBudget (2000*K^4) ∧
        |eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤
          2*(frameBudget (2000*K^4))^2 := by
  have hK0 : 0 ≤ K := by linarith
  have hK4 : 1 ≤ K^4 := one_le_pow₀ hK
  have hbig : 1 ≤ 2000*K^4 := by linarith
  have hK34 : K^3 ≤ K^4 := pow_le_pow_right₀ hK (by decide : 3 ≤ 4)
  have hgraph : HessianPatchBounds f (2000*K^4) :=
    (hessianPatchBounds_of_norms hK hb hHreg).mono (by nlinarith [pow_nonneg hK0 4])
  have hD (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :=
    canonical_denominator_conditioned hU hf hw (hdom hx) hK
      (fun n _ hn => hb n hn x hx) (hwb x hx) (hwreg x hx) (hHreg x hx)
  have hds : ContDiffOn ℝ 2 (fun y => 5*w y*(hessian f y).det) U :=
    (contDiffOn_const.mul hw).mul
      (det_contDiffOn (fun i j => contDiffOn_jet hU hf (by norm_num) ![i,j]))
  exact restoration_of_small_numerator hU hf hdom hdet hds hprod hbig hε hgraph
    (fun x hx => (hD x hx).1) (fun x hx => (hD x hx).2.first)
    (fun x hx => (hD x hx).2.second) hN0 hN1 hN2 hsmall

end

end Submission.Obl.k4_physical_parent_potential_candidates
