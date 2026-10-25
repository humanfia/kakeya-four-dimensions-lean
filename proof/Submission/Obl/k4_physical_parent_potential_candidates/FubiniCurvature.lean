import Submission.Obl.k4_physical_parent_potential_candidates.FubiniHessian

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open scoped BigOperators

noncomputable section

namespace FubiniHessian

open FubiniJets

def cubicError (f : FubiniBase → ℝ) (x : FubiniBase) (i j k : Fin 3) : ℝ :=
  cubic f x i j k-fubiniCubic (hessian f x) (form f x) i j k

def cubicErrorPartial (f : FubiniBase → ℝ) (x : FubiniBase) (l i j k : Fin 3) : ℝ :=
  jet (fun z => cubicError f z i j k) 1 ![l] x

def formDerivative (f : FubiniBase → ℝ) (x : FubiniBase) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => jet (potential f) 2 ![i,j] x

def curvature (f : FubiniBase → ℝ) (x : FubiniBase) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => formDerivative f x i j-form f x i*form f x j

def scalarCurvature (f : FubiniBase → ℝ) (x : FubiniBase) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, (hessian f x)⁻¹ i j*curvature f x i j)/3

def scalarError (f : FubiniBase → ℝ) (x : FubiniBase) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => curvature f x i j-scalarCurvature f x*hessian f x i j

theorem cubicError_smooth
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    (i j k : Fin 3) : ContDiffOn ℝ 3 (fun x => cubicError f x i j k) U := by
  have hH (i j : Fin 3) : ContDiffOn ℝ 3 (fun x => hessian f x i j) U :=
    contDiffOn_jet hU hf (by norm_num) ![i,j]
  have hm (i : Fin 3) : ContDiffOn ℝ 3 (fun x => form f x i) U :=
    contDiffOn_jet hU (potential_smooth hU hf hdet) (by norm_num) ![i]
  exact (contDiffOn_jet hU hf (by norm_num) ![i,j,k]).sub
    ((((hm i).mul (hH j k)).add ((hm j).mul (hH i k))).add ((hm k).mul (hH i j)))

/-- Differentiate the actual cubic defect; all tensors here are actual
coordinate jets of f or its logarithmic Hessian potential. -/
theorem cubicErrorPartial_eq
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (l i j k : Fin 3) :
    cubicErrorPartial f x l i j k = jet f 4 ![l,i,j,k] x-
      fubiniCubicVariation (hessian f x) (cubic f x) (form f x) (formDerivative f x) l i j k := by
  have hφ := potential_smooth hU hf hdet
  have hm (i : Fin 3) : HasDerivAt (fun s : ℝ => form f (x+s • basis l) i)
      (formDerivative f x l i) 0 := hasDerivAt_coordinate_jet hU hφ (by norm_num) ![i] x hx l
  have hH (i j : Fin 3) : HasDerivAt (fun s : ℝ => hessian f (x+s • basis l) i j)
      (cubic f x l i j) 0 := hasDerivAt_coordinate_jet hU hf (by norm_num) ![i,j] x hx l
  have hC : HasDerivAt (fun s : ℝ => cubic f (x+s • basis l) i j k)
      (jet f 4 ![l,i,j,k] x) 0 := hasDerivAt_coordinate_jet hU hf (by norm_num) ![i,j,k] x hx l
  have hh := hC.sub ((((hm i).mul (hH j k)).add ((hm j).mul (hH i k))).add ((hm k).mul (hH i j)))
  simp only [zero_smul, add_zero] at hh
  have he : HasDerivAt (fun s : ℝ => cubicError f (x+s • basis l) i j k)
      (jet f 4 ![l,i,j,k] x-
        fubiniCubicVariation (hessian f x) (cubic f x) (form f x) (formDerivative f x) l i j k) 0 := by
    convert hh using 1 <;> (try funext s) <;> dsimp [cubicError, fubiniCubic, fubiniCubicVariation] <;> ring
  exact (hasDerivAt_coordinate_value hU (cubicError_smooth hU hf hdet i j k)
    (by norm_num) x hx l).unique he

/-- The curvature commutator is an explicit linear combination of the
cubic defect and its first derivatives. -/
theorem curvature_commutator_eq
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (l k i j : Fin 3) :
    fubiniCommutator (hessian f x) (curvature f x) l k i j =
      cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j-
        form f x k*cubicError f x l i j+form f x l*cubicError f x k i j := by
  have hM : (formDerivative f x).IsSymm := by
    apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    exact form_first_derivatives_symmetric hU hf hdet hx j i
  have hC : ∀ l k i, cubic f x l k i = cubic f x k l i :=
    fun l k i => jet_three_first_two_symmetric hU hf (by norm_num) hx l k i
  have hh := fubini_commutator_identity (hessian f x) (formDerivative f x) (form f x)
    (cubic f x) hM hC l k i j
  have h1 := cubicErrorPartial_eq hU hf hdet hx l k i j
  have h2 := cubicErrorPartial_eq hU hf hdet hx k l i j
  have hsym := jet_four_first_two_symmetric hU hf (by norm_num) hx l k i j
  change fubiniCubicVariation _ _ _ _ l k i j-fubiniCubicVariation _ _ _ _ k l i j =
    fubiniCommutator (hessian f x) (curvature f x) l k i j+
      form f x k*cubicError f x l i j-form f x l*cubicError f x k i j at hh
  linarith

/-- The first curvature defect has a linear bound from the cubic error.
No power of the accuracy is lost in this integrability step. -/
theorem scalarError_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hinv : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K) (hm : ∀ i, |form f x i| ≤ K)
    (hE : ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ l i j k, |cubicErrorPartial f x l i j k| ≤ ε) :
    ∀ i j, |scalarError f x i j| ≤ 6*K*(1+K)*ε := by
  have hcomm : ∀ l k i j, |fubiniCommutator (hessian f x) (curvature f x) l k i j| ≤ 2*ε+2*K*ε := by
    intro l k i j
    rw [curvature_commutator_eq hU hf hdet hx]
    have h1 := abs_add_le
      (cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j-form f x k*cubicError f x l i j)
      (form f x l*cubicError f x k i j)
    have h2 := abs_sub
      (cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j)
      (form f x k*cubicError f x l i j)
    have h3 := abs_sub (cubicErrorPartial f x k l i j) (cubicErrorPartial f x l k i j)
    have hb1 : |form f x k*cubicError f x l i j| ≤ K*ε := by
      rw [abs_mul]
      exact mul_le_mul (hm k) (hE l i j) (abs_nonneg _) hK
    have hb2 : |form f x l*cubicError f x k i j| ≤ K*ε := by
      rw [abs_mul]
      exact mul_le_mul (hm l) (hE k i j) (abs_nonneg _) hK
    linarith [hDE k l i j, hDE l k i j]
  have hh := fubini_scalar_error_bound (hessian f x) (curvature f x) (hessian_symmetric hU hf hx)
    (isUnit_iff_ne_zero.mpr (hdet x hx)) hK (by positivity : 0 ≤ 2*ε+2*K*ε) hinv hcomm
  intro i j
  convert hh i j using 1 <;> (try dsimp [scalarError, scalarCurvature]) <;> ring

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
