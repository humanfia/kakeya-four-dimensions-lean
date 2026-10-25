-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/RawBinTranslation.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials
import Submission.Lib.K4ChartLifting.Normalize
import Submission.Lib.K4HiddenQuadratic

/-! Translation to one raw hidden bin and reconstruction from its calibrated
base value and base derivative. The hidden bin center may be arbitrarily large. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.RawBinTranslation

noncomputable section

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4ChartLifting
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

/-- Translate the old raw hidden coordinate by a fixed bin endpoint. -/
def shiftedPoint (w : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Function.update x 3 (x 3 - w)

def substitution (w : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![X 0, X 1, X 2, X 3 + C w]

def shiftedTest (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (substitution w) P

theorem shiftedTest_degree (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (shiftedTest w P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_bind₁_le_of_le_one
  intro i
  fin_cases i <;> simp [substitution]
  exact deg1_add (deg1_X _) (deg1_C _)

theorem shiftedTest_pderiv (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (shiftedTest w P) = shiftedTest w (pderiv (3 : Fin 4) P) := by
  apply pderiv_bind₁_of_diagonal
  · simp [substitution]
  · intro i hi
    fin_cases i <;> simp_all [substitution]

theorem shiftedTest_pderiv_twice (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (shiftedTest w P)) =
      shiftedTest w (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [shiftedTest_pderiv, shiftedTest_pderiv]

theorem eval_shiftedTest (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    eval (shiftedPoint w x) (shiftedTest w P) = eval x P := by
  rw [shiftedTest, eval_bind₁']
  have heq : (fun i => eval (shiftedPoint w x) (substitution w i)) = x := by
    funext i
    fin_cases i <;> simp [shiftedPoint, substitution]
  rw [heq]

theorem eval_shiftedTest_pderiv (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    eval (shiftedPoint w x) (pderiv (3 : Fin 4) (shiftedTest w P)) =
      eval x (pderiv (3 : Fin 4) P) := by
  rw [shiftedTest_pderiv, eval_shiftedTest]

theorem eval_shiftedTest_pderiv_twice (w : ℝ) (P : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    eval (shiftedPoint w x) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (shiftedTest w P))) =
      eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [shiftedTest_pderiv_twice, eval_shiftedTest]

theorem shiftedPoint_base (w : ℝ) (x : Fin 4 → ℝ) (i : Fin 3) :
    shiftedPoint w x i.castSucc = x i.castSucc := by
  have hi : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
  simp [shiftedPoint, hi]

/-- A raw bin becomes exactly bin zero, with a bounded translated hidden
coordinate; its possibly huge absolute endpoint disappears. -/
theorem shiftedPoint_raw_bin {a : ℝ} (ha : 0 < a) (j : ℤ) (x : Fin 4 → ℝ)
    (hbin : ⌊x 3 / a⌋ = j) :
    0 ≤ shiftedPoint ((j : ℝ) * a) x 3 ∧
      shiftedPoint ((j : ℝ) * a) x 3 < a ∧
      ⌊shiftedPoint ((j : ℝ) * a) x 3 / a⌋ = 0 := by
  have hb := Int.floor_eq_iff.mp hbin
  rw [le_div_iff₀ ha, div_lt_iff₀ ha] at hb
  have hlo : 0 ≤ shiftedPoint ((j : ℝ) * a) x 3 := by
    simp only [shiftedPoint, Function.update_self]
    linarith
  have hhi : shiftedPoint ((j : ℝ) * a) x 3 < a := by
    simp only [shiftedPoint, Function.update_self]
    linarith
  refine ⟨hlo, hhi, Int.floor_eq_iff.mpr ?_⟩
  norm_num only [Int.cast_zero, zero_add, Int.cast_one]
  exact ⟨div_nonneg hlo ha.le, (div_lt_one ha).mpr hhi⟩

private theorem coeffL1_rename_base_le (Q : MvPolynomial (Fin 3) ℝ) :
    coeffL1 (rename Fin.castSucc Q : MvPolynomial (Fin 4) ℝ) ≤ coeffL1 Q := by
  rw [rename_eq_aeval, aeval_eq_bind₁]
  simpa only [Function.comp_def, one_pow, mul_one] using
    coeffL1_bind₁_le (fun i : Fin 3 => (X i.castSucc : MvPolynomial (Fin 4) ℝ))
      1 le_rfl (fun i => le_of_eq (coeffL1_X _)) Q

/-- Calibrating the value and first derivative on the base controls the
ENTIRE quadratic, using its constant second derivative. -/
theorem coefficient_bound_of_base_slices
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) {H : ℝ} (hH : 0 ≤ H)
    (hvalue : ∀ e, |(restrictBase P).coeff e| ≤ H)
    (hfirst : ∀ e, |(restrictBase (pderiv (3 : Fin 4) P)).coeff e| ≤ H)
    (hsecond : |curvature P (3 : Fin 4)| ≤ H) (e : Fin 4 →₀ ℕ) :
    |P.coeff e| ≤ 55 * H := by
  have hdeg0 : (restrictBase P).totalDegree ≤ 2 := (totalDegree_restrictBase P).trans hP
  have hdeg1 : (restrictBase (pderiv (3 : Fin 4) P)).totalDegree ≤ 2 :=
    (totalDegree_restrictBase _).trans
      ((Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred P 3).trans (by omega))
  have hmass0 : coeffL1 (restrictBase P) ≤ 27 * H := by
    have h := coeffL1_le_of_coeff_le (restrictBase P) hdeg0 H hvalue
    norm_num at h
    exact h
  have hmass1 : coeffL1 (restrictBase (pderiv (3 : Fin 4) P)) ≤ 27 * H := by
    have h := coeffL1_le_of_coeff_le (restrictBase (pderiv (3 : Fin 4) P)) hdeg1 H hfirst
    norm_num at h
    exact h
  have hx : coeffL1 ((X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ (2 : ℕ)) ≤ 1 := by
    simpa only [coeffL1_X, one_pow] using coeffL1_pow_le (X (3 : Fin 4)) 2
  have hcurv : coeffL1 (C (curvature P (3 : Fin 4) / 2) * X (3 : Fin 4) ^ 2) ≤ H := by
    calc
      _ ≤ |curvature P (3 : Fin 4) / 2| * coeffL1 (X (3 : Fin 4) ^ 2) := coeffL1_C_mul_le _ _
      _ ≤ (H / 2) * 1 := by
        apply mul_le_mul ?_ hx (coeffL1_nonneg _) (by positivity)
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact div_le_div_of_nonneg_right hsecond (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ H := by linarith
  have hlinear : coeffL1 (rename Fin.castSucc (restrictBase (pderiv (3 : Fin 4) P)) *
      X (3 : Fin 4)) ≤ 27 * H := by
    apply (coeffL1_mul_le _ _).trans
    simpa only [coeffL1_X, mul_one] using (coeffL1_rename_base_le _).trans hmass1
  have hsum : coeffL1 (rename Fin.castSucc (restrictBase P) +
      rename Fin.castSucc (restrictBase (pderiv (3 : Fin 4) P)) * X (3 : Fin 4)) ≤ 54 * H := by
    exact (coeffL1_add_le _ _).trans
      ((add_le_add ((coeffL1_rename_base_le _).trans hmass0) hlinear).trans_eq (by ring))
  have hmass : coeffL1 P ≤ 55 * H := by
    conv_lhs => rw [quadratic_decomposition P hP]
    exact (coeffL1_add_le _ _).trans ((add_le_add hsum hcurv).trans_eq (by ring))
  exact (abs_coeff_le_coeffL1 P e).trans hmass

/-- The value and derivative slices at a raw bin's lower endpoint are
bounded on the SAME source event, without any coefficient-size assumption. -/
theorem raw_bin_base_slice_bounds
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {a K : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (j : ℤ) (x : Fin 4 → ℝ) (hbin : ⌊x 3 / a⌋ = j)
    (hvalue : |eval x P| ≤ K)
    (hfirst : |eval x (pderiv (3 : Fin 4) P)| ≤ K)
    (hsecond : |eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) :
    |eval (Fin.init x) (restrictBase (shiftedTest ((j : ℝ) * a) P))| ≤ 3 * K ∧
    |eval (Fin.init x) (restrictBase (pderiv (3 : Fin 4) (shiftedTest ((j : ℝ) * a) P)))| ≤ 2 * K ∧
    |curvature (shiftedTest ((j : ℝ) * a) P) (3 : Fin 4)| ≤ K := by
  let w := (j : ℝ) * a
  let Q := shiftedTest w P
  let v := shiftedPoint w x
  have hQ : Q.totalDegree ≤ 2 := (shiftedTest_degree w P).trans hP
  obtain ⟨hv0, hva, _⟩ := shiftedPoint_raw_bin ha j x hbin
  have hvabs : |v 3| ≤ a := by
    dsimp [v, w]
    rw [abs_of_nonneg hv0]
    exact hva.le
  have hfirst' : |eval v (pderiv (3 : Fin 4) Q)| ≤ K := by
    simpa only [v, Q, eval_shiftedTest_pderiv] using hfirst
  have hsecond' : |curvature Q (3 : Fin 4)| ≤ K := by
    have hh : |eval v (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ K := by
      simpa only [v, Q, eval_shiftedTest_pderiv_twice] using hsecond
    simpa only [second_pderiv_eq_curvature Q hQ 3, eval_C] using hh
  have hupdate : Function.update v 3 (v 3 + -(v 3)) = Fin.snoc (Fin.init x) 0 := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · change (Function.update v (Fin.last 3) (v (Fin.last 3) + -(v (Fin.last 3))))
        (Fin.last 3) = Fin.snoc (Fin.init x) 0 (Fin.last 3)
      rw [Function.update_self, add_neg_cancel]
      exact (Fin.snoc_last (0 : ℝ) (Fin.init x)).symm
    · have hk : k.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last k
      simp [v, shiftedPoint, hk, Fin.init_def]
  have herror := signal_error_scale Q hQ v (3 : Fin 4) hK (by norm_num : (0 : ℝ) ≤ 1)
    ha.le ha1 hfirst' hsecond' (h := -(v 3)) (by simpa using hvabs)
  rw [hupdate] at herror
  norm_num only [one_pow, one_add_one_eq_two] at herror
  have hbase0 : |eval (Fin.init x) (restrictBase Q)| ≤ 3 * K := by
    rw [eval_restrictBase]
    calc
      _ ≤ |eval v Q| + |eval (Fin.snoc (Fin.init x) 0) Q - eval v Q| := by
        have := abs_add_le (eval v Q) (eval (Fin.snoc (Fin.init x) 0) Q - eval v Q)
        simpa using this
      _ ≤ K + 2 * K * a := by
        apply add_le_add
        · simpa only [v, Q, eval_shiftedTest] using hvalue
        · simpa only [mul_comm K (2 : ℝ)] using herror
      _ ≤ 3 * K := by nlinarith
  have hmove := quadratic_coordinate_derivative Q hQ v (3 : Fin 4) (-(v 3))
  rw [hupdate] at hmove
  have hbase1 : |eval (Fin.init x) (restrictBase (pderiv (3 : Fin 4) Q))| ≤ 2 * K := by
    rw [eval_restrictBase, hmove]
    calc
      _ ≤ |eval v (pderiv (3 : Fin 4) Q)| + |curvature Q (3 : Fin 4)| * |v 3| := by
        simpa only [abs_mul, abs_neg] using
          abs_add_le (eval v (pderiv (3 : Fin 4) Q)) (curvature Q (3 : Fin 4) * -(v 3))
      _ ≤ K + K * a := by gcongr
      _ ≤ 2 * K := by nlinarith
  exact ⟨hbase0, hbase1, hsecond'⟩

/-- The calibrated base slices give a uniform power bound, with only six
extra exponent units; no original hidden endpoint enters the bound. -/
theorem coefficient_power_bound_of_base_slices
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {N A : ℝ} (hN : 2 ≤ N) (hA : 0 ≤ A)
    (hvalue : ∀ e, |(restrictBase P).coeff e| ≤ N ^ A)
    (hfirst : ∀ e, |(restrictBase (pderiv (3 : Fin 4) P)).coeff e| ≤ N ^ A)
    (hsecond : |curvature P (3 : Fin 4)| ≤ N ^ A) (e : Fin 4 →₀ ℕ) :
    |P.coeff e| ≤ N ^ (A + 6) := by
  have hNpos : 0 < N := by linarith
  have h55 : (55 : ℝ) ≤ N ^ (6 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (6 : ℕ) := by norm_num
      _ ≤ N ^ (6 : ℕ) := pow_le_pow_left₀ (by norm_num) hN 6
      _ = _ := by norm_num
  refine (coefficient_bound_of_base_slices P hP (by positivity) hvalue hfirst hsecond e).trans ?_
  calc
    _ ≤ N ^ (6 : ℝ) * N ^ A := mul_le_mul_of_nonneg_right h55 (by positivity)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- Only the base coordinates and the raw-bin width control the translated
point. This has no hypothesis about the old hidden coordinate's size. -/
theorem shiftedPoint_box_bound {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hR : 1 ≤ R)
    (j : ℤ) (x : Fin 4 → ℝ) (hbin : ⌊x 3 / a⌋ = j)
    (hbase : ∀ i : Fin 3, |x i.castSucc| ≤ R) :
    ∀ i, |shiftedPoint ((j : ℝ) * a) x i| ≤ R := by
  obtain ⟨h0, h1, _⟩ := shiftedPoint_raw_bin ha j x hbin
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · change |shiftedPoint ((j : ℝ) * a) x 3| ≤ R
    rw [abs_of_nonneg h0]
    exact h1.le.trans (ha1.trans hR)
  · simpa only [shiftedPoint_base] using hbase k

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.RawBinTranslation
