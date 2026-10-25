import Submission.Obl.k4_physical_parent_potential_candidates.FubiniCurvature
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniInverse
import Submission.Lib.K4CubicTests.WedgeConditioning

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open scoped BigOperators

noncomputable section

namespace FubiniHessian

open FubiniJets

def errorCommutator (f : FubiniBase → ℝ) (x : FubiniBase) (l k i j : Fin 3) : ℝ :=
  cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j-
    form f x k*cubicError f x l i j+form f x l*cubicError f x k i j

def scalarErrorPartial (f : FubiniBase → ℝ) (x : FubiniBase) (p i j : Fin 3) : ℝ :=
  jet (fun z => scalarError f z i j) 1 ![p] x

def cubicErrorSecond (f : FubiniBase → ℝ) (x : FubiniBase) (p l i j k : Fin 3) : ℝ :=
  jet (fun z => cubicError f z i j k) 2 ![p,l] x

def errorCommutatorDerivative (f : FubiniBase → ℝ) (x : FubiniBase) (p l k i j : Fin 3) : ℝ :=
  cubicErrorSecond f x p k l i j-cubicErrorSecond f x p l k i j-
    (formDerivative f x p k*cubicError f x l i j+form f x k*cubicErrorPartial f x p l i j)+
    (formDerivative f x p l*cubicError f x k i j+form f x l*cubicErrorPartial f x p k i j)

theorem scalarError_eq_contraction
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (l i : Fin 3) :
    scalarError f x l i =
      (∑ k : Fin 3, ∑ j : Fin 3, (hessian f x)⁻¹ k j*errorCommutator f x l k i j)/3 := by
  have hh := fubini_contracted_commutator (hessian f x) (curvature f x) (hessian_symmetric hU hf hx)
    (isUnit_iff_ne_zero.mpr (hdet x hx)) l i
  have heq : (∑ k : Fin 3, ∑ j : Fin 3, (hessian f x)⁻¹ k j*errorCommutator f x l k i j) =
      ∑ k : Fin 3, ∑ j : Fin 3, (hessian f x)⁻¹ k j*fubiniCommutator (hessian f x) (curvature f x) l k i j := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    rw [curvature_commutator_eq hU hf hdet hx]
    rfl
  rw [heq, hh]
  dsimp only [scalarError, scalarCurvature]
  ring

theorem scalarCurvature_smooth
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0) :
    ContDiffOn ℝ 2 (scalarCurvature f) U := by
  have hH (i j : Fin 3) : ContDiffOn ℝ 2 (fun x => hessian f x i j) U :=
    contDiffOn_jet hU hf (by norm_num) ![i,j]
  have hG := contDiffOn_inverse_entries_three hH hdet
  have hφ := potential_smooth hU hf hdet
  have hm (i : Fin 3) : ContDiffOn ℝ 2 (fun x => form f x i) U :=
    contDiffOn_jet hU hφ (by norm_num) ![i]
  have hM (i j : Fin 3) : ContDiffOn ℝ 2 (fun x => formDerivative f x i j) U :=
    contDiffOn_jet hU hφ (by norm_num) ![i,j]
  apply ContDiffOn.div_const
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (hG i j).mul ((hM i j).sub ((hm i).mul (hm j)))

theorem scalarError_smooth
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    (i j : Fin 3) : ContDiffOn ℝ 2 (fun x => scalarError f x i j) U := by
  have hφ := potential_smooth hU hf hdet
  have hm (i : Fin 3) : ContDiffOn ℝ 2 (fun x => form f x i) U :=
    contDiffOn_jet hU hφ (by norm_num) ![i]
  exact ((contDiffOn_jet hU hφ (by norm_num) ![i,j]).sub ((hm i).mul (hm j))).sub
    ((scalarCurvature_smooth hU hf hdet).mul (contDiffOn_jet hU hf (by norm_num) ![i,j]))

theorem hasDerivAt_coordinate_errorCommutator
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (p l k i j : Fin 3) :
    HasDerivAt (fun s : ℝ => errorCommutator f (x+s • basis p) l k i j)
      (errorCommutatorDerivative f x p l k i j) 0 := by
  have hφ := potential_smooth hU hf hdet
  have hm (i : Fin 3) : HasDerivAt (fun s : ℝ => form f (x+s • basis p) i)
      (formDerivative f x p i) 0 := hasDerivAt_coordinate_jet hU hφ (by norm_num) ![i] x hx p
  have hE (l i j : Fin 3) : HasDerivAt (fun s : ℝ => cubicError f (x+s • basis p) l i j)
      (cubicErrorPartial f x p l i j) 0 :=
    hasDerivAt_coordinate_value hU (cubicError_smooth hU hf hdet l i j) (by norm_num) x hx p
  have hDE (l i j k : Fin 3) : HasDerivAt (fun s : ℝ => cubicErrorPartial f (x+s • basis p) l i j k)
      (cubicErrorSecond f x p l i j k) 0 :=
    hasDerivAt_coordinate_jet hU (cubicError_smooth hU hf hdet i j k) (by norm_num) ![l] x hx p
  have hh := (((hDE k l i j).sub (hDE l k i j)).sub ((hm k).mul (hE l i j))).add ((hm l).mul (hE k i j))
  simp only [zero_smul, add_zero] at hh
  convert hh using 1 <;> (try funext s) <;> dsimp [errorCommutator, errorCommutatorDerivative] <;> ring


def inversePartial (f : FubiniBase → ℝ) (x : FubiniBase) (p : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  -((hessian f x)⁻¹*Matrix.of (cubic f x p)*(hessian f x)⁻¹)

def scalarErrorDerivativeFormula (f : FubiniBase → ℝ) (x : FubiniBase) (p l i : Fin 3) : ℝ :=
  (∑ k : Fin 3, ∑ j : Fin 3,
    (inversePartial f x p k j*errorCommutator f x l k i j+
      (hessian f x)⁻¹ k j*errorCommutatorDerivative f x p l k i j))/3

theorem hasDerivAt_coordinate_inverse
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (p i j : Fin 3) :
    HasDerivAt (fun s : ℝ => (hessian f (x+s • basis p))⁻¹ i j) (inversePartial f x p i j) 0 := by
  have hH (i j : Fin 3) : HasDerivAt (fun s : ℝ => hessian f (x+s • basis p) i j)
      (cubic f x p i j) 0 := hasDerivAt_coordinate_jet hU hf (by norm_num) ![i,j] x hx p
  have hh := hasDerivAt_inverse_entries_three (H' := Matrix.of (cubic f x p))
    hH (by simpa using hdet x hx) i j
  simpa only [zero_smul, add_zero, inversePartial, Matrix.neg_apply] using hh

/-- Differentiate the global contraction identity for T. Its derivative
still contains only E, DE and D2E, with no accuracy-independent terms. -/
theorem scalarErrorPartial_eq
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (p l i : Fin 3) :
    scalarErrorPartial f x p l i = scalarErrorDerivativeFormula f x p l i := by
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hasDerivAt_coordinate_inverse hU hf hdet hx p k j).mul
        (hasDerivAt_coordinate_errorCommutator hU hf hdet hx p l k i j)))).div_const 3
  simp only [zero_smul, add_zero] at hh
  have hc : ContinuousAt (fun s : ℝ => x+s • basis p) 0 := by fun_prop
  have hnear : ∀ᶠ s in nhds (0:ℝ), x+s • basis p ∈ U := by
    apply hc.eventually
    simpa using hU.mem_nhds hx
  have heq : (fun s : ℝ => scalarError f (x+s • basis p) l i) =ᶠ[nhds (0:ℝ)]
      (fun s => (∑ k : Fin 3, ∑ j : Fin 3,
        (hessian f (x+s • basis p))⁻¹ k j*errorCommutator f (x+s • basis p) l k i j)/3) := by
    filter_upwards [hnear] with s hs
    exact scalarError_eq_contraction hU hf hdet hs l i
  have hd : HasDerivAt (fun s : ℝ => scalarError f (x+s • basis p) l i)
      (scalarErrorDerivativeFormula f x p l i) 0 := by
    exact hh.congr_of_eventuallyEq heq
  exact (hasDerivAt_coordinate_value hU (scalarError_smooth hU hf hdet l i)
    (by norm_num) x hx p).unique hd

theorem inversePartial_bound
    {f : FubiniBase → ℝ} {x : FubiniBase} {K : ℝ} (hK : 0 ≤ K)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K)
    (hC : ∀ p i j, |cubic f x p i j| ≤ K) :
    ∀ p i j, |inversePartial f x p i j| ≤ 9*K^3 := by
  intro p i j
  rw [inversePartial, Matrix.neg_apply, abs_neg]
  have hleft := Submission.Lib.K4CubicTests.matrix_mul_three_entry_abs_le
    (hessian f x)⁻¹ (Matrix.of (cubic f x p)) K K hK hG (hC p)
  have hh := Submission.Lib.K4CubicTests.matrix_mul_three_entry_abs_le
    ((hessian f x)⁻¹*Matrix.of (cubic f x p)) (hessian f x)⁻¹
    (3*K*K) K (by positivity) hleft hG i j
  convert hh using 1 <;> ring

private theorem abs_six_bound (a b c d e f : ℝ) :
    |a-b-(c+d)+(e+f)| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
  have h1 := abs_add_le (a-b-(c+d)) (e+f)
  have h2 := abs_sub (a-b) (c+d)
  have h3 := abs_sub a b
  have h4 := abs_add_le c d
  have h5 := abs_add_le e f
  linarith

theorem errorCommutatorDerivative_bound
    {f : FubiniBase → ℝ} {x : FubiniBase} {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hm : ∀ i, |form f x i| ≤ K) (hM : ∀ i j, |formDerivative f x i j| ≤ K)
    (hE : ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ l i j k, |cubicErrorPartial f x l i j k| ≤ ε)
    (hDDE : ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε) :
    ∀ p l k i j, |errorCommutatorDerivative f x p l k i j| ≤ 6*K*ε := by
  have hK0 : 0 ≤ K := by linarith
  intro p l k i j
  unfold errorCommutatorDerivative
  have hME (a b c d e : Fin 3) : |formDerivative f x a b*cubicError f x c d e| ≤ K*ε := by
    rw [abs_mul]
    exact mul_le_mul (hM a b) (hE c d e) (abs_nonneg _) hK0
  have hmDE (a b c d e : Fin 3) : |form f x a*cubicErrorPartial f x b c d e| ≤ K*ε := by
    rw [abs_mul]
    exact mul_le_mul (hm a) (hDE b c d e) (abs_nonneg _) hK0
  apply (abs_six_bound _ _ _ _ _ _).trans
  have h1 := hDDE p k l i j
  have h2 := hDDE p l k i j
  have h3 := hME p k l i j
  have h4 := hmDE k p l i j
  have h5 := hME p l k i j
  have h6 := hmDE l p k i j
  nlinarith [mul_le_mul_of_nonneg_right hK hε]


theorem errorCommutator_bound
    {f : FubiniBase → ℝ} {x : FubiniBase} {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hm : ∀ i, |form f x i| ≤ K)
    (hE : ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ l i j k, |cubicErrorPartial f x l i j k| ≤ ε) :
    ∀ l k i j, |errorCommutator f x l k i j| ≤ 4*K*ε := by
  have hK0 : 0 ≤ K := by linarith
  intro l k i j
  unfold errorCommutator
  have h1 := abs_add_le
    (cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j-form f x k*cubicError f x l i j)
    (form f x l*cubicError f x k i j)
  have h2 := abs_sub (cubicErrorPartial f x k l i j-cubicErrorPartial f x l k i j)
    (form f x k*cubicError f x l i j)
  have h3 := abs_sub (cubicErrorPartial f x k l i j) (cubicErrorPartial f x l k i j)
  have hb1 : |form f x k*cubicError f x l i j| ≤ K*ε := by
    rw [abs_mul]
    exact mul_le_mul (hm k) (hE l i j) (abs_nonneg _) hK0
  have hb2 : |form f x l*cubicError f x k i j| ≤ K*ε := by
    rw [abs_mul]
    exact mul_le_mul (hm l) (hE k i j) (abs_nonneg _) hK0
  nlinarith [hDE k l i j, hDE l k i j, mul_le_mul_of_nonneg_right hK hε]

/-- The differentiated curvature defect is still linear in the original
cubic tensor error, with one fixed polynomial conditioning loss. -/
theorem scalarErrorPartial_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K)
    (hC : ∀ p i j, |cubic f x p i j| ≤ K)
    (hm : ∀ i, |form f x i| ≤ K) (hM : ∀ i j, |formDerivative f x i j| ≤ K)
    (hE : ∀ i j k, |cubicError f x i j k| ≤ ε)
    (hDE : ∀ l i j k, |cubicErrorPartial f x l i j k| ≤ ε)
    (hDDE : ∀ p l i j k, |cubicErrorSecond f x p l i j k| ≤ ε) :
    ∀ p l i, |scalarErrorPartial f x p l i| ≤ 200*K^4*ε := by
  have hK0 : 0 ≤ K := by linarith
  have hG' := inversePartial_bound hK0 hG hC
  have hB := errorCommutator_bound hK hε hm hE hDE
  have hB' := errorCommutatorDerivative_bound hK hε hm hM hE hDE hDDE
  intro p l i
  rw [scalarErrorPartial_eq hU hf hdet hx, scalarErrorDerivativeFormula, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hterm (k j : Fin 3) :
      |inversePartial f x p k j*errorCommutator f x l k i j+
        (hessian f x)⁻¹ k j*errorCommutatorDerivative f x p l k i j| ≤
      9*K^3*(4*K*ε)+K*(6*K*ε) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add
      (mul_le_mul (hG' p k j) (hB l k i j) (abs_nonneg _) (by positivity))
      (mul_le_mul (hG k j) (hB' p l k i j) (abs_nonneg _) hK0)
  have hsum : |∑ k : Fin 3, ∑ j : Fin 3,
      (inversePartial f x p k j*errorCommutator f x l k i j+
        (hessian f x)⁻¹ k j*errorCommutatorDerivative f x p l k i j)| ≤
      9*(9*K^3*(4*K*ε)+K*(6*K*ε)) := by
    calc
      _ ≤ ∑ k : Fin 3, ∑ j : Fin 3,
          |inversePartial f x p k j*errorCommutator f x l k i j+
            (hessian f x)⁻¹ k j*errorCommutatorDerivative f x p l k i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _k : Fin 3, ∑ _j : Fin 3, (9*K^3*(4*K*ε)+K*(6*K*ε)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hterm k j
      _ = _ := by simp; ring
  calc
    _ ≤ 9*(9*K^3*(4*K*ε)+K*(6*K*ε))/3 := div_le_div_of_nonneg_right hsum (by norm_num)
    _ = (108*K^4+18*K^2)*ε := by ring
    _ ≤ 200*K^4*ε := by
      apply mul_le_mul_of_nonneg_right ?_ hε
      have h2 : K^2 ≤ K^4 := pow_le_pow_right₀ hK (by decide : 2 ≤ 4)
      nlinarith [pow_nonneg hK0 4]

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
