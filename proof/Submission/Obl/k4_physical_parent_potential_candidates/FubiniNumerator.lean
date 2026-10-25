import Submission.Obl.k4_physical_parent_potential_candidates.FubiniImplicit
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniRestoration

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MvPolynomial FubiniJets FubiniHessian

noncomputable section

/-- A C²-small cleared numerator gives all canonical cubic-error bounds
needed by the restoration, with linear accuracy throughout. -/
theorem cubic_error_C2_of_small_numerator
    {f d : FubiniBase → ℝ} {N : FubiniBase → ConicTensor.Tensor} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U)
    (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0) (hd : ContDiffOn ℝ 2 d U)
    (hprod : ∀ x ∈ U, ∀ i j k, N x i j k = d x*cubicError f x i j k)
    {x : FubiniBase} (hx : x ∈ U) {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hreg : K⁻¹ ≤ |d x|)
    (hD1 : ∀ i, |jet d 1 ![i] x| ≤ K) (hD2 : ∀ i j, |jet d 2 ![i,j] x| ≤ K)
    (hN0 : ∀ i j k, |N x i j k| ≤ ε)
    (hN1 : ∀ p i j k, |jet (fun y => N y i j k) 1 ![p] x| ≤ ε)
    (hN2 : ∀ p l i j k, |jet (fun y => N y i j k) 2 ![p,l] x| ≤ ε) :
    (∀ i j k, |cubicError f x i j k| ≤ 6*K^5*ε) ∧
    (∀ p i j k, |cubicErrorPartial f x p i j k| ≤ 6*K^5*ε) ∧
      ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ 6*K^5*ε := by
  have hE (i j k : Fin 3) := FubiniProductJets.small_of_product hU hd
    ((cubicError_smooth hU hf hdet i j k).of_le (by norm_num))
    (fun y hy => hprod y hy i j k) hx hK hε hreg hD1 hD2
    (hN0 i j k) (fun p => hN1 p i j k) (fun p l => hN2 p l i j k)
  have hK0 : 0 ≤ K := by linarith
  have h15 : K ≤ K^5 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 5)
  have h35 : K^3 ≤ K^5 := pow_le_pow_right₀ hK (by decide : 3 ≤ 5)
  refine ⟨?_, ?_, ?_⟩
  · intro i j k
    apply (hE i j k).1.trans
    nlinarith [mul_le_mul_of_nonneg_right h15 hε, mul_nonneg (pow_nonneg hK0 5) hε]
  · intro p i j k
    apply ((hE i j k).2.1 p).trans
    nlinarith [mul_le_mul_of_nonneg_right h35 hε, mul_nonneg (pow_nonneg hK0 5) hε]
  · intro p l i j k
    exact (hE i j k).2.2 p l

/-- Assemble the quadratic certificate directly from a small numerator of
the canonical tensor. It suffices to bound a single regular scalar denominator. -/
theorem restoration_of_small_numerator
    {f d : FubiniBase → ℝ} {N : FubiniBase → ConicTensor.Tensor} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U)
    (hdom : Metric.closedBall (0:FubiniBase) 1 ⊆ U)
    (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0) (hd : ContDiffOn ℝ 2 d U)
    (hprod : ∀ x ∈ U, ∀ i j k, N x i j k = d x*cubicError f x i j k)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε) (hb : HessianPatchBounds f K)
    (hreg : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, K⁻¹ ≤ |d x|)
    (hD1 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i, |jet d 1 ![i] x| ≤ K)
    (hD2 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j, |jet d 2 ![i,j] x| ≤ K)
    (hN0 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |N x i j k| ≤ ε)
    (hN1 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p i j k,
      |jet (fun y => N y i j k) 1 ![p] x| ≤ ε)
    (hN2 : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p l i j k,
      |jet (fun y => N y i j k) 2 ![p,l] x| ≤ ε)
    (hsmall : 3000000*(frameBudget K)^9*(6*K^5*ε) ≤ 1) :
    ∃ Q : MvPolynomial (Fin 4) ℝ,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 74*(frameBudget K)^4) ∧
      ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
        |eval (Fin.snoc (fun i => x i) (f x)) Q| ≤ 18000000*(frameBudget K)^8*K^5*ε ∧
        (frameBudget K)⁻¹ ≤ eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ∧
        eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ≤ 3*frameBudget K ∧
        |eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤
          2*(frameBudget K)^2 := by
  have hK0 : 0 ≤ K := by linarith
  have hE (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :=
    cubic_error_C2_of_small_numerator hU hf hdet hd hprod (hdom hx) hK hε
      (hreg x hx) (hD1 x hx) (hD2 x hx) (hN0 x hx) (hN1 x hx) (hN2 x hx)
  obtain ⟨Q, hdeg, hcoeff, hest⟩ := restoration_of_cubic_error hU hf hdom hdet hK
    (by positivity : 0 ≤ 6*K^5*ε) hb (fun x hx => (hE x hx).1)
    (fun x hx => (hE x hx).2.1) (fun x hx => (hE x hx).2.2) hsmall
  refine ⟨Q, hdeg, hcoeff, ?_⟩
  intro x hx
  obtain ⟨hv, hl, hu, hc⟩ := hest x hx
  refine ⟨?_, hl, hu, hc⟩
  convert hv using 1 <;> ring

end

end Submission.Obl.k4_physical_parent_potential_candidates
