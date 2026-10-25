import Submission.Obl.k4_physical_parent_potential_candidates.FubiniScalarGradient
import Submission.Lib.K4CubicTests.MatrixConditioning

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set Matrix
open scoped BigOperators

noncomputable section

namespace FubiniHessian

open FubiniJets

def canonicalDerivative (f : FubiniBase → ℝ) (x : FubiniBase) (p i : Fin 3) : ℝ :=
  (∑ j : Fin 3, ∑ k : Fin 3,
    (inversePartial f x p j k*cubic f x i j k+
      (hessian f x)⁻¹ j k*jet f 4 ![p,i,j,k] x))/5

theorem formDerivative_eq_canonicalDerivative
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (p i : Fin 3) :
    formDerivative f x p i = canonicalDerivative f x p i := by
  have hC (j k : Fin 3) : HasDerivAt (fun s : ℝ => cubic f (x+s • basis p) i j k)
      (jet f 4 ![p,i,j,k] x) 0 := hasDerivAt_coordinate_jet hU hf (by norm_num) ![i,j,k] x hx p
  have hh := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hasDerivAt_coordinate_inverse hU hf hdet hx p j k).mul (hC j k)))).div_const 5
  simp only [zero_smul, add_zero] at hh
  have hc : ContinuousAt (fun s : ℝ => x+s • basis p) 0 := by fun_prop
  have hnear : ∀ᶠ s in nhds (0:ℝ), x+s • basis p ∈ U := by
    apply hc.eventually
    simpa using hU.mem_nhds hx
  have heq : (fun s : ℝ => form f (x+s • basis p) i) =ᶠ[nhds (0:ℝ)]
      (fun s => canonical f (x+s • basis p) i) := by
    filter_upwards [hnear] with s hs
    exact form_eq_canonical hU hf hdet hs i
  have hd : HasDerivAt (fun s : ℝ => form f (x+s • basis p) i) (canonicalDerivative f x p i) 0 :=
    hh.congr_of_eventuallyEq heq
  exact (hasDerivAt_coordinate_jet hU (potential_smooth hU hf hdet)
    (by norm_num) ![i] x hx p).unique hd

theorem form_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ} (hK : 0 ≤ K)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K) (hC : ∀ i j k, |cubic f x i j k| ≤ K) :
    ∀ i, |form f x i| ≤ 2*K^2 := by
  intro i
  rw [form_eq_canonical hU hf hdet hx, canonical, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have hsum : |∑ j : Fin 3, ∑ k : Fin 3, (hessian f x)⁻¹ j k*cubic f x i j k| ≤ 9*K^2 := by
    calc
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, |(hessian f x)⁻¹ j k*cubic f x i j k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, K*K :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hG j k) (hC i j k) (abs_nonneg _) hK
      _ = _ := by simp; ring
  nlinarith [sq_nonneg K]

theorem formDerivative_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K) (hC : ∀ i j k, |cubic f x i j k| ≤ K)
    (hD : ∀ p i j k, |jet f 4 ![p,i,j,k] x| ≤ K) :
    ∀ p i, |formDerivative f x p i| ≤ 20*K^4 := by
  have hK0 : 0 ≤ K := by linarith
  have hG' := inversePartial_bound hK0 hG hC
  intro p i
  rw [formDerivative_eq_canonicalDerivative hU hf hdet hx, canonicalDerivative, abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 5)]
  have hsum : |∑ j : Fin 3, ∑ k : Fin 3,
      (inversePartial f x p j k*cubic f x i j k+
        (hessian f x)⁻¹ j k*jet f 4 ![p,i,j,k] x)| ≤ 9*(9*K^4+K^2) := by
    calc
      _ ≤ ∑ j : Fin 3, ∑ k : Fin 3,
          |inversePartial f x p j k*cubic f x i j k+
            (hessian f x)⁻¹ j k*jet f 4 ![p,i,j,k] x| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, (9*K^4+K^2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => by
          apply (abs_add_le _ _).trans
          rw [abs_mul, abs_mul]
          have h1 := mul_le_mul (hG' p j k) (hC i j k) (abs_nonneg _) (by positivity : 0 ≤ 9*K^3)
          have h2 := mul_le_mul (hG j k) (hD p i j k) (abs_nonneg _) hK0
          nlinarith
      _ = _ := by simp; ring
  have h24 : K^2 ≤ K^4 := pow_le_pow_right₀ hK (by decide : 2 ≤ 4)
  nlinarith [pow_nonneg hK0 4]

theorem scalarCurvature_bound
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ} (hK : 1 ≤ K)
    (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K) (hC : ∀ i j k, |cubic f x i j k| ≤ K)
    (hD : ∀ p i j k, |jet f 4 ![p,i,j,k] x| ≤ K) :
    |scalarCurvature f x| ≤ 72*K^5 := by
  have hK0 : 0 ≤ K := by linarith
  have hm := form_bound hU hf hdet hx hK0 hG hC
  have hM := formDerivative_bound hU hf hdet hx hK hG hC hD
  have hR (i j : Fin 3) : |curvature f x i j| ≤ 24*K^4 := by
    dsimp only [curvature]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hh := mul_le_mul (hm i) (hm j) (abs_nonneg _) (by positivity : 0 ≤ 2*K^2)
    nlinarith [hM i j]
  unfold scalarCurvature
  rw [abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hsum : |∑ i : Fin 3, ∑ j : Fin 3, (hessian f x)⁻¹ i j*curvature f x i j| ≤ 216*K^5 := by
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |(hessian f x)⁻¹ i j*curvature f x i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, K*(24*K^4) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hG i j) (hR i j) (abs_nonneg _) hK0
      _ = _ := by simp; ring
  nlinarith


/-- Normalized Hessian and inverse bounds control the volume density by
fixed powers, even for an indefinite Hessian. -/
theorem density_bounds
    {f : FubiniBase → ℝ} {x : FubiniBase} {K : ℝ} (hK : 1 ≤ K)
    (hdet : (hessian f x).det ≠ 0)
    (hH : ∀ i j, |hessian f x i j| ≤ K) (hG : ∀ i j, |(hessian f x)⁻¹ i j| ≤ K) :
    (6*K^3)⁻¹ ≤ density f x ∧ |density f x| ≤ 6*K^3 := by
  have hK0 : 0 ≤ K := by linarith
  let D : ℝ := 6*K^3
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith [one_le_pow₀ hK (n := 3)]
  have hD0 : 0 < D := by linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hd := Submission.Lib.K4CubicTests.matrix_det_three_abs_le (hessian f x) K hK0 hH
  have hi : |(hessian f x).det⁻¹| ≤ D := by
    have hh := Submission.Lib.K4CubicTests.matrix_det_three_abs_le (hessian f x)⁻¹ K hK0 hG
    simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using hh
  have hloghi : Real.log (hessian f x).det ≤ Real.log D := by
    rw [← Real.log_abs]
    exact Real.log_le_log (abs_pos.mpr hdet) hd
  have hloglo : -Real.log D ≤ Real.log (hessian f x).det := by
    have hh : Real.log (hessian f x).det⁻¹ ≤ Real.log D := by
      rw [← Real.log_abs]
      exact Real.log_le_log (abs_pos.mpr (inv_ne_zero hdet)) hi
    rw [Real.log_inv] at hh
    linarith
  have hlo : D⁻¹ ≤ density f x := by
    have hh := Real.exp_le_exp.mpr
      (show -Real.log D ≤ - (Real.log (hessian f x).det/5) by linarith)
    rw [Real.exp_neg, Real.exp_log hD0] at hh
    exact hh
  have hhi : density f x ≤ D := by
    have hh := Real.exp_le_exp.mpr
      (show -(Real.log (hessian f x).det/5) ≤ Real.log D by linarith)
    rw [Real.exp_log hD0] at hh
    exact hh
  have hp : 0 < density f x := Real.exp_pos _
  exact ⟨hlo, by rw [abs_of_pos hp]; exact hhi⟩

def frameBudget (K : ℝ) : ℝ := 100*K^5

theorem frameBudget_bounds {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ frameBudget K ∧ K ≤ frameBudget K ∧ 2*K^2 ≤ frameBudget K ∧
      20*K^4 ≤ frameBudget K ∧ 72*K^5 ≤ frameBudget K ∧ 6*K^3 ≤ frameBudget K := by
  have hK0 : 0 ≤ K := by linarith
  have h1 : 1 ≤ K^5 := one_le_pow₀ hK
  have h15 : K ≤ K^5 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 5)
  have h25 : K^2 ≤ K^5 := pow_le_pow_right₀ hK (by decide : 2 ≤ 5)
  have h35 : K^3 ≤ K^5 := pow_le_pow_right₀ hK (by decide : 3 ≤ 5)
  have h45 : K^4 ≤ K^5 := pow_le_pow_right₀ hK (by decide : 4 ≤ 5)
  dsimp [frameBudget]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
