-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/QuadraticSignalOscillation.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Lib.K4HiddenQuadratic

/-! A quantitative base resolution for quadratic native signals. Hidden
motion is estimated with its actual first and second derivatives; large
coefficients affect only the base mesh that must be used. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

noncomputable section

open Finset MvPolynomial

private theorem abs_prod_difference_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ) {B E : ℝ} (hB : 1 ≤ B) (hE : 0 ≤ E)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B)
    (hd : ∀ i ∈ s, |f i - g i| ≤ E) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ (s.card : ℝ) * B ^ s.card * E := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hB0 : 0 ≤ B := by linarith
    have htail := ih (fun j hj => hf j (mem_insert_of_mem hj))
      (fun j hj => hg j (mem_insert_of_mem hj))
      (fun j hj => hd j (mem_insert_of_mem hj))
    have hp : |∏ j ∈ s, f j| ≤ B ^ s.card := by
      rw [abs_prod]
      calc
        _ ≤ ∏ _j ∈ s, B := prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun j hj => hf j (mem_insert_of_mem hj))
        _ = _ := by simp
    rw [prod_insert hi, prod_insert hi, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    calc
      _ = |(f i - g i) * (∏ j ∈ s, f j) +
          g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| := by congr 1; ring
      _ ≤ |f i - g i| * |∏ j ∈ s, f j| +
          |g i| * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| := by
        simpa only [abs_mul] using abs_add_le
          ((f i - g i) * (∏ j ∈ s, f j))
          (g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
      _ ≤ E * B ^ s.card + B * ((s.card : ℝ) * B ^ s.card * E) := by
        gcongr
        · exact hd i (mem_insert_self _ _)
        · exact hg i (mem_insert_self _ _)
      _ ≤ (s.card + 1 : ℝ) * B ^ (s.card + 1) * E := by
        rw [pow_succ]
        have hfirst : E * B ^ s.card ≤ E * B ^ s.card * B := by
          exact le_mul_of_one_le_right (by positivity) hB
        nlinarith only [hfirst]

private theorem abs_pow_difference_two {x y R δ : ℝ} {n : ℕ}
    (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hx : |x| ≤ R) (hy : |y| ≤ R)
    (hd : |x-y| ≤ δ) (hn : n ≤ 2) : |x ^ n - y ^ n| ≤ 2 * R * δ := by
  interval_cases n
  · simp; positivity
  · simp only [pow_one]
    exact hd.trans (by nlinarith)
  · have heq : x ^ 2 - y ^ 2 = (x-y) * (x+y) := by ring
    rw [heq, abs_mul]
    have hs : |x+y| ≤ 2 * R := (abs_add_le x y).trans (by linarith)
    exact (mul_le_mul hd hs (abs_nonneg _) hδ).trans_eq (by ring)

/-- A fixed explicit Lipschitz bound for quadratics on a four-dimensional
box. The deliberately loose power is uniform over all polynomial supports. -/
theorem quadratic_eval_difference_bound
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {A R δ : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R) (hδ : 0 ≤ δ)
    (hcoeff : ∀ e, |P.coeff e| ≤ A) (x y : Fin 4 → ℝ)
    (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R)
    (hd : ∀ i, |x i - y i| ≤ δ) :
    |eval x P - eval y P| ≤ 648 * A * R ^ 9 * δ := by
  classical
  have hR0 : 0 ≤ R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hmon (e : Fin 4 →₀ ℕ) (he : e ∈ P.support) :
      |e.prod (fun i n => x i ^ n) - e.prod (fun i n => y i ^ n)| ≤
        8 * R ^ 9 * δ := by
    have he2 (i : Fin 4) : e i ≤ 2 :=
      (le_degreeOf_of_mem_support i he).trans ((degreeOf_le_totalDegree P i).trans hP)
    have hp (v : Fin 4 → ℝ) (hv : ∀ i, |v i| ≤ R) (i : Fin 4) :
        |v i ^ e i| ≤ R ^ 2 := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hv i) (e i)).trans
        (pow_le_pow_right₀ hR (he2 i))
    have h := abs_prod_difference_le (univ : Finset (Fin 4))
      (fun i => x i ^ e i) (fun i => y i ^ e i) hR2
      (by positivity : 0 ≤ 2 * R * δ)
      (fun i _ => hp x hx i) (fun i _ => hp y hy i)
      (fun i _ => abs_pow_difference_two hR hδ (hx i) (hy i) (hd i) (he2 i))
    rw [Finsupp.prod_fintype _ _ (by intro i; simp),
      Finsupp.prod_fintype _ _ (by intro i; simp)]
    convert h using 1 <;> norm_num <;> ring
  have hsupport : (P.support.card : ℝ) ≤ 81 := by
    have h := Submission.Lib.K4PolynomialRemezThree.card_support_le_degree_box 4 2 P hP
    norm_num at h
    exact_mod_cast h
  have heval (v : Fin 4 → ℝ) :
      eval v P = ∑ e ∈ P.support, P.coeff e * e.prod (fun i n => v i ^ n) := by
    conv_lhs => rw [P.as_sum]
    simp only [eval_sum, eval_monomial]
  rw [heval, heval, ← sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ P.support,
        |P.coeff e * e.prod (fun i n => x i ^ n) -
          P.coeff e * e.prod (fun i n => y i ^ n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ P.support, A * (8 * R ^ 9 * δ) := by
      apply sum_le_sum
      intro e he
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hcoeff e) (hmon e he) (abs_nonneg _) hA
    _ = (P.support.card : ℝ) * (A * (8 * R ^ 9 * δ)) := by simp
    _ ≤ 81 * (A * (8 * R ^ 9 * δ)) := by gcongr
    _ = _ := by ring

/-- A raw hidden interval of width `a` gives a signal interval of width
`(2*K+1)*a` once the base mesh resolves the polynomial coefficients. -/
theorem quadratic_signal_oscillation
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {A R K fine a : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hfine : 0 ≤ fine) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hcoeff : ∀ e, |P.coeff e| ≤ A)
    (hresolve : 648 * A * R ^ 9 * fine ≤ a)
    (x y : Fin 4 → ℝ) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R)
    (hbase : ∀ i : Fin 3, |x i.castSucc - y i.castSucc| ≤ fine)
    (hhidden : |x 3 - y 3| ≤ a)
    (hfirst : |eval x (pderiv (3 : Fin 4) P)| ≤ K)
    (hsecond : |eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) :
    |eval x P - eval y P| ≤ (2 * K + 1) * a := by
  let w : Fin 4 → ℝ := Function.update x 3 (y 3)
  have hw : ∀ i, |w i| ≤ R := by
    intro i
    by_cases hi : i = 3
    · subst i
      simpa [w] using hy 3
    · simpa [w, hi] using hx i
  have hwb : ∀ i, |w i - y i| ≤ fine := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hfine
    · have hj : j.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last j
      simpa [w, hj] using hbase j
  have hbaseEval : |eval w P - eval y P| ≤ a :=
    (quadratic_eval_difference_bound P hP hA hR hfine hcoeff w y hw hy hwb).trans hresolve
  have hTaylor := Submission.Lib.K4HiddenQuadratic.eval_update_add P hP x
    (3 : Fin 4) (y 3 - x 3)
  have hreplace : Function.update x 3 (x 3 + (y 3 - x 3)) = w := by
    simp [w]
  rw [hreplace] at hTaylor
  have hstep : |y 3 - x 3| ≤ a := by simpa [abs_sub_comm] using hhidden
  have hhiddenEval : |eval w P - eval x P| ≤ 2 * K * a := by
    rw [hTaylor]
    have heq : eval x P + (y 3 - x 3) * eval x (pderiv (3 : Fin 4) P) +
        (y 3 - x 3) ^ 2 / 2 * eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) - eval x P =
        (y 3 - x 3) * eval x (pderiv (3 : Fin 4) P) +
        (y 3 - x 3) ^ 2 / 2 * eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by ring
    rw [heq]
    calc
      _ ≤ |(y 3 - x 3) * eval x (pderiv (3 : Fin 4) P)| +
          |(y 3 - x 3) ^ 2 / 2 * eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| :=
        abs_add_le _ _
      _ = |y 3 - x 3| * |eval x (pderiv (3 : Fin 4) P)| +
          |y 3 - x 3| ^ 2 / 2 * |eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| := by
        rw [abs_mul, abs_mul, abs_div, abs_pow]
        norm_num
      _ ≤ a * K + a ^ 2 / 2 * K := by gcongr
      _ ≤ 2 * K * a := by
        have hasq : a ^ 2 ≤ a := by nlinarith
        have hmul := mul_le_mul_of_nonneg_right hasq hK
        nlinarith only [hmul, mul_nonneg hK ha]
  calc
    _ ≤ |eval x P - eval w P| + |eval w P - eval y P| := abs_sub_le _ _ _
    _ ≤ 2 * K * a + a := by
      rw [abs_sub_comm (eval x P)]
      exact add_le_add hhiddenEval hbaseEval
    _ = _ := by ring

/-- Polynomial coefficient and coordinate growth requires only a fixed
shift of the base-mesh exponent to resolve every raw hidden test. -/
theorem quadratic_signal_mesh_resolution {N M r s : ℝ}
    (hN : 2 ≤ N) (hM : 0 ≤ M) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 < N ^ (-(r + s + 10 * M + 10)) ∧
    N ^ (-(r + s + 10 * M + 10)) ≤ N ^ (-r) ∧
    648 * N ^ M * (N ^ M) ^ (9 : ℕ) *
      N ^ (-(r + s + 10 * M + 10)) ≤ N ^ (-s) := by
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := hNpos.le
  refine ⟨by positivity, Real.rpow_le_rpow_of_exponent_le hN1 (by linarith), ?_⟩
  have h648 : (648 : ℝ) ≤ N ^ (10 : ℕ) := by
    calc
      _ ≤ (2 : ℝ) ^ (10 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hN 10
  have hpow : (N ^ M) ^ (9 : ℕ) = N ^ (9 * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    ring
  have hcost : 648 * N ^ (-(10 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hN0]
    have hdiv : 648 / N ^ (10 : ℕ) ≤ 1 :=
      (div_le_iff₀ (by positivity : 0 < N ^ (10 : ℕ))).mpr (by simpa using h648)
    simpa [div_eq_mul_inv] using hdiv
  have hrpow : N ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have heq : 648 * N ^ M * (N ^ M) ^ (9 : ℕ) * N ^ (-(r + s + 10 * M + 10)) =
      (648 * N ^ (-(10 : ℝ))) * N ^ (-r) * N ^ (-s) := by
    rw [hpow]
    simp_rw [mul_assoc]
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos,
      ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 2
    ring
  rw [heq]
  calc
    _ ≤ 1 * 1 * N ^ (-s) := by gcongr
    _ = _ := by ring

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
