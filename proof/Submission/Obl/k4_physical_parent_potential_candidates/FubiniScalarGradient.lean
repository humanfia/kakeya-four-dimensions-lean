import Submission.Obl.k4_physical_parent_potential_candidates.FubiniScalarDerivative

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open scoped BigOperators

noncomputable section

namespace FubiniHessian

open FubiniJets

def scalarGradientError (f : FubiniBase → ℝ) (x : FubiniBase) (i : Fin 3) : ℝ :=
  jet (scalarCurvature f) 1 ![i] x-scalarCurvature f x*form f x i

/-- The scalar variation used by the algebraic commutator is exactly the
coordinate derivative of the actual scalar defect. -/
theorem scalarErrorPartial_eq_variation
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (k i j : Fin 3) :
    scalarErrorPartial f x k i j =
      fubiniScalarVariation (hessian f x) (cubic f x) (form f x) (formDerivative f x)
        (fun k i j => jet (potential f) 3 ![k,i,j] x) (scalarCurvature f x)
        (fun k => jet (scalarCurvature f) 1 ![k] x) k i j := by
  have hφ := potential_smooth hU hf hdet
  have hm (i : Fin 3) : HasDerivAt (fun s : ℝ => form f (x+s • basis k) i)
      (formDerivative f x k i) 0 := hasDerivAt_coordinate_jet hU hφ (by norm_num) ![i] x hx k
  have hM (i j : Fin 3) : HasDerivAt (fun s : ℝ => formDerivative f (x+s • basis k) i j)
      (jet (potential f) 3 ![k,i,j] x) 0 := hasDerivAt_coordinate_jet hU hφ (by norm_num) ![i,j] x hx k
  have hH (i j : Fin 3) : HasDerivAt (fun s : ℝ => hessian f (x+s • basis k) i j)
      (cubic f x k i j) 0 := hasDerivAt_coordinate_jet hU hf (by norm_num) ![i,j] x hx k
  have hlam : HasDerivAt (fun s : ℝ => scalarCurvature f (x+s • basis k))
      (jet (scalarCurvature f) 1 ![k] x) 0 :=
    hasDerivAt_coordinate_value hU (scalarCurvature_smooth hU hf hdet) (by norm_num) x hx k
  have hh := ((hM i j).sub ((hm i).mul (hm j))).sub (hlam.mul (hH i j))
  simp only [zero_smul, add_zero] at hh
  have hd : HasDerivAt (fun s : ℝ => scalarError f (x+s • basis k) i j)
      (fubiniScalarVariation (hessian f x) (cubic f x) (form f x) (formDerivative f x)
        (fun k i j => jet (potential f) 3 ![k,i,j] x) (scalarCurvature f x)
        (fun k => jet (scalarCurvature f) 1 ![k] x) k i j) 0 := by
    convert hh using 1 <;> (try funext s) <;>
      dsimp [scalarError, curvature, fubiniScalarVariation] <;> ring
  exact (hasDerivAt_coordinate_value hU (scalarError_smooth hU hf hdet i j)
    (by norm_num) x hx k).unique hd

/-- The last integrability defect is bounded by a fixed polynomial times
the original C2 cubic error, preserving exact linear accuracy. -/
theorem scalarGradientError_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K)
    (hC : ∀ p i j, |cubic f x p i j| ≤ K)
    (hm : ∀ i, |form f x i| ≤ K) (hM : ∀ i j, |formDerivative f x i j| ≤ K)
    (hE : ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ l i j k, |cubicErrorPartial f x l i j k| ≤ ε)
    (hDDE : ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε) :
    ∀ k, |scalarGradientError f x k| ≤ 3000*K^5*ε := by
  have hK0 : 0 ≤ K := by linarith
  have hT : ∀ i j, |scalarError f x i j| ≤ 12*K^2*ε := by
    intro i j
    apply (scalarError_bound hU hf hdet hx hK0 hε hG hm hE hDE i j).trans
    have hk := mul_le_mul_of_nonneg_left (by linarith : 1+K ≤ 2*K) (by positivity : 0 ≤ 6*K*ε)
    nlinarith
  have hDT := scalarErrorPartial_bound hU hf hdet hx hK hε hG hC hm hM hE hDE hDDE
  have hMsym : (formDerivative f x).IsSymm := by
    apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    exact form_first_derivatives_symmetric hU hf hdet hx j i
  have hCsym : ∀ k i j, cubic f x k i j = cubic f x i k j :=
    fun k i j => jet_three_first_two_symmetric hU hf (by norm_num) hx k i j
  have hNsym : ∀ k i j,
      jet (potential f) 3 ![k,i,j] x = jet (potential f) 3 ![i,k,j] x :=
    fun k i j => form_second_derivatives_symmetric hU hf hdet hx k i j
  have hdef : ∀ i j, |fubiniScalarDefect (hessian f x) (formDerivative f x) (form f x)
      (scalarCurvature f x) i j| ≤ 12*K^2*ε := hT
  have hvar : ∀ k i j,
      |fubiniScalarVariation (hessian f x) (cubic f x) (form f x) (formDerivative f x)
        (fun k i j => jet (potential f) 3 ![k,i,j] x) (scalarCurvature f x)
        (fun k => jet (scalarCurvature f) 1 ![k] x) k i j| ≤ 200*K^4*ε := by
    intro k i j
    rw [← scalarErrorPartial_eq_variation hU hf hdet hx]
    exact hDT k i j
  have hh := fubini_scalar_gradient_error_bound (hessian f x) (formDerivative f x) (form f x)
    (cubic f x) (fun k i j => jet (potential f) 3 ![k,i,j] x) (scalarCurvature f x)
    (fun k => jet (scalarCurvature f) 1 ![k] x) (hessian_symmetric hU hf hx)
    (isUnit_iff_ne_zero.mpr (hdet x hx)) hMsym hCsym hNsym hK0 hK0
    (by positivity : 0 ≤ 12*K^2*ε) (by positivity : 0 ≤ 200*K^4*ε) hG hm hdef hvar
  intro k
  apply (hh k).trans
  have h45 : K^4 ≤ K^5 := pow_le_pow_right₀ hK (by decide : 4 ≤ 5)
  have hpoly : 10*K*(K*(12*K^2)+200*K^4) ≤ 3000*K^5 := by nlinarith [pow_nonneg hK0 5]
  convert mul_le_mul_of_nonneg_right hpoly hε using 1 <;> ring

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
