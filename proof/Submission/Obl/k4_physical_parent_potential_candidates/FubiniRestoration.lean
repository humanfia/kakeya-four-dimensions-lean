import Submission.Obl.k4_physical_parent_potential_candidates.FubiniConditioning

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MvPolynomial
open scoped BigOperators

noncomputable section

open FubiniJets FubiniHessian

/-- Conditioning assumptions on the normalized graph, before constructing
its logarithmic connection. All connection bounds are derived from these. -/
structure HessianPatchBounds (f : FubiniBase → ℝ) (K : ℝ) where
  value : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, |f x| ≤ K
  gradient : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i, |jet f 1 ![i] x| ≤ K
  hessian : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j, |FubiniHessian.hessian f x i j| ≤ K
  cubic : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |FubiniHessian.cubic f x i j k| ≤ K
  fourth : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k l, |jet f 4 ![i,j,k,l] x| ≤ K
  inverse : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j, |(FubiniHessian.hessian f x)⁻¹ i j| ≤ K

/-- Construct the full differential frame from ONE actual smooth graph
and its canonical cubic tensor error, with no auxiliary integrability input. -/
def canonicalGraphData
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdom : Metric.closedBall (0:FubiniBase) 1 ⊆ U)
    (hdet : ∀ x ∈ U, (FubiniHessian.hessian f x).det ≠ 0)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε) (hb : HessianPatchBounds f K)
    (hE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p i j k, |cubicErrorPartial f x p i j k| ≤ ε)
    (hDDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε) :
    FubiniGraphData (frameBudget K) (3000*(frameBudget K)^5*ε) := by
  let A := frameBudget K
  have hA := frameBudget_bounds hK
  have hA1 : 1 ≤ A := hA.1
  have hA0 : 0 ≤ A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hm (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
      ∀ i, |form f x i| ≤ A := fun i =>
    (form_bound hU hf hdet (hdom hx) hK0 (hb.inverse x hx) (hb.cubic x hx) i).trans hA.2.2.1
  have hM (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
      ∀ i j, |formDerivative f x i j| ≤ A := fun i j =>
    (formDerivative_bound hU hf hdet (hdom hx) hK (hb.inverse x hx) (hb.cubic x hx)
      (hb.fourth x hx) i j).trans hA.2.2.2.1
  have hT (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
      ∀ i j, |scalarError f x i j| ≤ 3000*A^5*ε := by
    intro i j
    apply (scalarError_bound hU hf hdet (hdom hx) hA0 hε
      (fun i j => (hb.inverse x hx i j).trans hA.2.1) (hm x hx) (hE x hx) (hDE x hx) i j).trans
    have h25 : A^2 ≤ A^5 := pow_le_pow_right₀ hA1 (by decide : 2 ≤ 5)
    have h15 : A ≤ A^5 := by simpa using pow_le_pow_right₀ hA1 (by decide : 1 ≤ 5)
    have hp : 6*A*(1+A) ≤ 3000*A^5 := by nlinarith [pow_nonneg hA0 5]
    exact (by convert mul_le_mul_of_nonneg_right hp hε using 1 <;> ring)
  have hW (x : FubiniBase) (hx : x ∈ Metric.closedBall (0:FubiniBase) 1) :
      ∀ i, |scalarGradientError f x i| ≤ 3000*A^5*ε :=
    scalarGradientError_bound hU hf hdet (hdom hx) hA1 hε
      (fun i j => (hb.inverse x hx i j).trans hA.2.1)
      (fun i j k => (hb.cubic x hx i j k).trans hA.2.1) (hm x hx) (hM x hx)
      (hE x hx) (hDE x hx) (hDDE x hx)
  have hεA : ε ≤ 3000*A^5*ε := by
    have hp : 1 ≤ 3000*A^5 := by have := one_le_pow₀ hA1 (n := 5); linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hε
  refine {
    f := f
    grad := fun x i => jet f 1 ![i] x
    H := FubiniHessian.hessian f
    m := form f
    lam := scalarCurvature f
    rho := density f
    E := cubicError f
    T := scalarError f
    W := scalarGradientError f
    f_bound := fun x hx => (hb.value x hx).trans hA.2.1
    grad_bound := fun x hx i => (hb.gradient x hx i).trans hA.2.1
    H_bound := fun x hx i j => (hb.hessian x hx i j).trans hA.2.1
    m_bound := hm
    lam_bound := fun x hx => (scalarCurvature_bound hU hf hdet (hdom hx) hK
      (hb.inverse x hx) (hb.cubic x hx) (hb.fourth x hx)).trans hA.2.2.2.2.1
    rho_bound := fun x hx => ((density_bounds hK (hdet x (hdom hx)) (hb.hessian x hx)
      (hb.inverse x hx)).2).trans hA.2.2.2.2.2
    E_bound := fun x hx i j k => (hE x hx i j k).trans hεA
    T_bound := hT
    W_bound := hW
    f_deriv := ?_
    grad_deriv := ?_
    H_deriv := ?_
    m_deriv := ?_
    lam_deriv := ?_
    rho_deriv := ?_
  }
  · intro x hx t ht
    exact hasDerivAt_radial_value hU hf (by norm_num) x t (hdom (FubiniGraphData.radial_mem hx ht))
  · intro x hx t ht i
    have htx := hdom (FubiniGraphData.radial_mem hx ht)
    have hh := hasDerivAt_radial_jet hU hf (by norm_num) ![i] x t htx
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    change jet f 2 ![i,j] (t • x)*x j = jet f 2 ![j,i] (t • x)*x j
    rw [jet_two_symmetric hU hf (by norm_num) htx i j]
  · intro x hx t ht i j
    have htx := hdom (FubiniGraphData.radial_mem hx ht)
    have hh := hasDerivAt_radial_jet hU hf (by norm_num) ![i,j] x t htx
    change HasDerivAt (fun s => jet f 2 ![i,j] (s • x)) _ t
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k _
    change _ = jet f 3 ![k,i,j] (t • x)*x k
    dsimp only [cubicError, FubiniHessian.cubic, FubiniHessian.hessian]
    ring
  · intro x hx t ht i
    have htx := hdom (FubiniGraphData.radial_mem hx ht)
    have hh := hasDerivAt_radial_jet hU (potential_smooth hU hf hdet) (by norm_num) ![i] x t htx
    change HasDerivAt (fun s => jet (potential f) 1 ![i] (s • x)) _ t
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k _
    change _ = jet (potential f) 2 ![k,i] (t • x)*x k
    dsimp only [scalarError, curvature, formDerivative]
    ring
  · intro x hx t ht
    have htx := hdom (FubiniGraphData.radial_mem hx ht)
    have hh := hasDerivAt_radial_value hU (scalarCurvature_smooth hU hf hdet) (by norm_num) x t htx
    convert hh using 1
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [scalarGradientError]
    ring
  · intro x hx t ht
    exact hasDerivAt_radial_density hU hf hdet x t (hdom (FubiniGraphData.radial_mem hx ht))

/-- Palette-free local restoration from the actual canonical cubic tensor.
The accuracy enters linearly and all losses are fixed polynomials in K. -/
theorem restoration_of_cubic_error
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdom : Metric.closedBall (0:FubiniBase) 1 ⊆ U)
    (hdet : ∀ x ∈ U, (FubiniHessian.hessian f x).det ≠ 0)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε) (hb : HessianPatchBounds f K)
    (hE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p i j k, |cubicErrorPartial f x p i j k| ≤ ε)
    (hDDE : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1, ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε)
    (hsmall : 3000000*(frameBudget K)^9*ε ≤ 1) :
    ∃ Q : MvPolynomial (Fin 4) ℝ,
      Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ 74*(frameBudget K)^4) ∧
      ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
        |eval (Fin.snoc (fun i => x i) (f x)) Q| ≤ 3000000*(frameBudget K)^8*ε ∧
        (frameBudget K)⁻¹ ≤ eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ∧
        eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) Q) ≤ 3*frameBudget K ∧
        |eval (Fin.snoc (fun i => x i) (f x)) (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q))| ≤
          2*(frameBudget K)^2 := by
  let data := canonicalGraphData hU hf hdom hdet hK hε hb hE hDE hDDE
  have hA := frameBudget_bounds hK
  have hK0 : 0 < K := by linarith
  have hA0 : 0 ≤ frameBudget K := by linarith [hA.1]
  have hρ : ∀ x ∈ Metric.closedBall (0:FubiniBase) 1,
      (frameBudget K)⁻¹ ≤ data.rho x := by
    intro x hx
    apply le_trans ?_ (density_bounds hK (hdet x (hdom hx)) (hb.hessian x hx) (hb.inverse x hx)).1
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < 6*K^3) hA.2.2.2.2.2
  have hh := data.frozen_graph_certificate hA.1 (by positivity : 0 ≤ 3000*(frameBudget K)^5*ε)
    (by convert hsmall using 1 <;> ring) hρ
  refine ⟨data.frozen, hh.1, hh.2.1, ?_⟩
  intro x hx
  obtain ⟨hv, hd, hu, hc⟩ := hh.2.2 x hx
  refine ⟨?_, hd, hu, hc⟩
  change |eval (Fin.snoc (fun i => x i) (f x)) data.frozen| ≤ _ at hv
  convert hv using 1 <;> ring

end

end Submission.Obl.k4_physical_parent_potential_candidates
