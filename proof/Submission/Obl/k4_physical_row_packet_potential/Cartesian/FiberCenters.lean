-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/FiberCenters.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/FiberCenters.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/FiberCenters.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.PolynomialFiberLists

/-!
One chosen coefficient bin determines an actual polynomial on each fiber.
The estimates transfer its fit from an original occurrence to its nearby
grid point. No new fit or witness is selected after the table choice.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

noncomputable section

/-- The lower corner of a scalar coefficient bin. -/
def coefficientCenterPolynomial (D : ℕ) (p : ℝ) (m : Fin (D + 1) → ℤ) : Polynomial ℝ :=
  ∑ k : Fin (D + 1), Polynomial.monomial (k : ℕ) (p * (m k : ℝ))

theorem degree_coefficientCenterPolynomial (D : ℕ) (p : ℝ) (m : Fin (D + 1) → ℤ) :
    (coefficientCenterPolynomial D p m).natDegree ≤ D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ k.isLt)

theorem eval_coefficientCenterPolynomial (D : ℕ) (p : ℝ) (m : Fin (D + 1) → ℤ) (t : ℝ) :
    (coefficientCenterPolynomial D p m).eval t =
      ∑ k : Fin (D + 1), p * (m k : ℝ) * t ^ (k : ℕ) := by
  simp only [coefficientCenterPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Quantizing one real coefficient costs at most one coefficient mesh. -/
theorem coefficient_floor_error (p c : ℝ) (hp : 0 < p) :
    |c - p * (⌊c / p⌋ : ℝ)| ≤ p := by
  have hlo := (le_div_iff₀ hp).mp (Int.floor_le (c / p))
  have hhi := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (c / p))
  apply abs_le.mpr
  constructor <;> nlinarith

theorem polynomial_eval_fin_degree (P : Polynomial ℝ) (D : ℕ) (hP : P.natDegree ≤ D) (t : ℝ) :
    P.eval t = ∑ k : Fin (D + 1), P.coeff (k : ℕ) * t ^ (k : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- Every actual fit in the chosen bin stays close to its fixed center polynomial. -/
theorem coefficient_center_eval_error (P : Polynomial ℝ) (D : ℕ) (hP : P.natDegree ≤ D)
    (p A t : ℝ) (hp : 0 < p) (hA : 1 ≤ A) (ht : |t| ≤ A)
    (m : Fin (D + 1) → ℤ) (hcode : ∀ k : Fin (D + 1), ⌊P.coeff (k : ℕ) / p⌋ = m k) :
    |P.eval t - (coefficientCenterPolynomial D p m).eval t| ≤
      ((D : ℝ) + 1) * p * A ^ D := by
  rw [polynomial_eval_fin_degree P D hP, eval_coefficientCenterPolynomial, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin (D + 1), |P.coeff (k : ℕ) * t ^ (k : ℕ) -
        p * (m k : ℝ) * t ^ (k : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (D + 1), p * A ^ D := by
      apply Finset.sum_le_sum
      intro k _
      rw [← sub_mul, abs_mul, abs_pow]
      have hc := coefficient_floor_error p (P.coeff (k : ℕ)) hp
      rw [hcode k] at hc
      have hpow : |t| ^ (k : ℕ) ≤ A ^ D :=
        (pow_le_pow_left₀ (abs_nonneg _) ht _).trans
          (pow_le_pow_right₀ hA (Nat.le_of_lt_succ k.isLt))
      exact mul_le_mul hc hpow (by positivity) hp.le
    _ = _ := by simp; ring

/-- Evaluation of one fixed center polynomial is stable under time displacement.
The coordinate-radius dependence is an explicit fixed power. -/
theorem coefficient_center_eval_lipschitz (D : ℕ) (p : ℝ) (m : Fin (D + 1) → ℤ)
    (A B s t : ℝ) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hcoeff : ∀ k, |p * (m k : ℝ)| ≤ B) (hs : |s| ≤ A) (ht : |t| ≤ A) :
    |(coefficientCenterPolynomial D p m).eval s -
        (coefficientCenterPolynomial D p m).eval t| ≤
      ((D : ℝ) + 1) * D * B * A ^ D * |s - t| := by
  rw [eval_coefficientCenterPolynomial, eval_coefficientCenterPolynomial, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin (D + 1), |p * (m k : ℝ) * s ^ (k : ℕ) -
        p * (m k : ℝ) * t ^ (k : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (D + 1), B * (|s - t| * D * A ^ D) := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub, abs_mul]
      have hpow : |s ^ (k : ℕ) - t ^ (k : ℕ)| ≤ |s - t| * D * A ^ D := by
        apply (abs_pow_sub_pow_le (a := s) (b := t) (n := (k : ℕ))).trans
        have hk : (k : ℝ) ≤ D := by exact_mod_cast Nat.le_of_lt_succ k.isLt
        have hd : (k : ℕ) - 1 ≤ D := (Nat.sub_le _ _).trans (Nat.le_of_lt_succ k.isLt)
        have hn : 0 ≤ max |s| |t| := (abs_nonneg _).trans (le_max_left _ _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
          ((pow_le_pow_left₀ hn (max_le hs ht) _).trans (pow_le_pow_right₀ hA hd))
          (by positivity) (by positivity)
      exact mul_le_mul (hcoeff k) hpow (abs_nonneg _) hB
    _ = _ := by simp; ring

/-- A selected row-coefficient code defines one actual polynomial row. -/
def rowCoefficientCenter {q : ℕ} (D : ℕ) (p : ℝ) (m : Fin (q * (D + 1)) → ℤ) :
    Fin q → Polynomial ℝ := fun j => coefficientCenterPolynomial D p
      (fun k => m (finProdFinEquiv (j, k)))

theorem row_center_code {q : ℕ} (P : Fin q → Polynomial ℝ) (D : ℕ) (p : ℝ)
    (m : Fin (q * (D + 1)) → ℤ) (hcode : polynomialFitCoefficientCode D p P = m)
    (j : Fin q) (k : Fin (D + 1)) :
    ⌊(P j).coeff (k : ℕ) / p⌋ = m (finProdFinEquiv (j, k)) := by
  have h := congrFun hcode (finProdFinEquiv (j, k))
  simpa only [polynomialFitCoefficientCode, polynomialFitCoefficients,
    Equiv.symm_apply_apply] using h

/-- One common fiber polynomial fits a chosen cell value. The error keeps
field-bin rounding, original fit error, coefficient rounding, and actual
occurrence-to-grid displacement explicit. -/
theorem row_center_grid_fit {q : ℕ} (P : Fin q → Polynomial ℝ) (D : ℕ)
    (hP : ∀ j, (P j).natDegree ≤ D)
    (p A B s t ε η : ℝ) (hp : 0 < p) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (hs : |s| ≤ A) (ht : |t| ≤ A)
    (m : Fin (q * (D + 1)) → ℤ) (hcode : polynomialFitCoefficientCode D p P = m)
    (hcoeff : ∀ j k, |(P j).coeff (k : ℕ)| ≤ B)
    (G V : Fin q → ℝ)
    (hfield : ∀ j, |V j - G j| ≤ η) (hfit : ∀ j, |G j - (P j).eval t| ≤ ε) :
    ∀ j, |V j - (rowCoefficientCenter D p m j).eval s| ≤
      η + ε + ((D : ℝ) + 1) * p * A ^ D +
        ((D : ℝ) + 1) * D * (B + p) * A ^ D * |s - t| := by
  intro j
  let mj : Fin (D + 1) → ℤ := fun k => m (finProdFinEquiv (j, k))
  have hcodej : ∀ k : Fin (D + 1), ⌊(P j).coeff (k : ℕ) / p⌋ = mj k := row_center_code P D p m hcode j
  have hround := coefficient_center_eval_error (P j) D (hP j) p A t hp hA ht mj hcodej
  have hc (k : Fin (D + 1)) : |p * (mj k : ℝ)| ≤ B + p := by
    have he := coefficient_floor_error p ((P j).coeff (k : ℕ)) hp
    rw [hcodej k] at he
    have htri := abs_sub_le (p * (mj k : ℝ)) ((P j).coeff (k : ℕ)) 0
    rw [abs_sub_comm (p * (mj k : ℝ)) ((P j).coeff (k : ℕ))] at htri
    simp only [sub_zero] at htri
    linarith [hcoeff j (k : ℕ)]
  have hlip := coefficient_center_eval_lipschitz D p mj A (B + p) t s hA
    (by positivity) hc ht hs
  have htri := abs_sub_le (V j) (G j) ((coefficientCenterPolynomial D p mj).eval s)
  have htri' := abs_sub_le (G j) ((P j).eval t) ((coefficientCenterPolynomial D p mj).eval s)
  have htri'' := abs_sub_le ((P j).eval t) ((coefficientCenterPolynomial D p mj).eval t)
    ((coefficientCenterPolynomial D p mj).eval s)
  change |V j - (coefficientCenterPolynomial D p mj).eval s| ≤ _
  rw [abs_sub_comm t s] at hlip
  linarith [hfield j, hfit j]

/-- On Cartesian coordinates whose basis directions have time component
one, normalized time is the sum of the three axis coordinates. -/
theorem cartesian_time_sum (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ j, A 0 j = 1) (u : Fin 3 → ℝ) :
    (A.mulVec u) 0 = ∑ j, u j := by
  simp only [Matrix.mulVec, dotProduct, hA, one_mul]

def fiberTimeOffset (axis : Fin 3) (u : Fin 3 → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase axis, u j

theorem sum_axis_update (axis : Fin 3) (u : Fin 3 → ℝ) (s : ℝ) :
    (∑ j, Function.update u axis s j) = fiberTimeOffset axis u + s := by
  classical
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ axis)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact Function.update_of_ne (Finset.mem_erase.mp hj).1 s u

/-- The common row polynomial along one grid fiber, in that axis coordinate. -/
def rowFiberCenter {q : ℕ} (D : ℕ) (p : ℝ) (m : Fin (q * (D + 1)) → ℤ)
    (axis : Fin 3) (u : Fin 3 → ℝ) (j : Fin q) : Polynomial ℝ :=
  (rowCoefficientCenter D p m j).comp (Polynomial.C (fiberTimeOffset axis u) + Polynomial.X)

theorem degree_rowFiberCenter {q : ℕ} (D : ℕ) (p : ℝ)
    (m : Fin (q * (D + 1)) → ℤ) (axis : Fin 3) (u : Fin 3 → ℝ) (j : Fin q) :
    (rowFiberCenter D p m axis u j).natDegree ≤ D := by
  apply Polynomial.natDegree_comp_le.trans
  have haff : (Polynomial.C (fiberTimeOffset axis u) + Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (by simp)
  exact (Nat.mul_le_mul (degree_coefficientCenterPolynomial D p _) haff).trans (by simp)

theorem eval_rowFiberCenter {q : ℕ} (D : ℕ) (p : ℝ)
    (m : Fin (q * (D + 1)) → ℤ) (axis : Fin 3) (u : Fin 3 → ℝ) (j : Fin q) (s : ℝ) :
    (rowFiberCenter D p m axis u j).eval s =
      (rowCoefficientCenter D p m j).eval (∑ i, Function.update u axis s i) := by
  simp only [rowFiberCenter, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, sum_axis_update]

/-- A coordinate mesh costs only three mesh widths in normalized time.
Thus one chosen coefficient bin supplies an actual polynomial fit at the
grid center with a fixed-power error and no renewed witness selection. -/
theorem row_center_cartesian_fit {q : ℕ} (P : Fin q → Polynomial ℝ) (D : ℕ)
    (hP : ∀ j, (P j).natDegree ≤ D)
    (p K ξ ε η : ℝ) (hp : 0 < p) (hK : 1 ≤ K) (_hξ : 0 ≤ ξ)
    (u v : Fin 3 → ℝ) (hu : ∀ i, |u i| ≤ K) (hv : ∀ i, |v i| ≤ K)
    (hdist : ∀ i, |u i - v i| ≤ ξ)
    (m : Fin (q * (D + 1)) → ℤ) (hcode : polynomialFitCoefficientCode D p P = m)
    (hcoeff : ∀ j k, |(P j).coeff k| ≤ K)
    (G V : Fin q → ℝ)
    (hfield : ∀ j, |V j - G j| ≤ η)
    (hfit : ∀ j, |G j - (P j).eval (∑ i, u i)| ≤ ε) :
    ∀ j, |V j - (rowCoefficientCenter D p m j).eval (∑ i, v i)| ≤
      η + ε + ((D : ℝ) + 1) * p * (3 * K) ^ D +
        3 * ((D : ℝ) + 1) * D * (K + p) * (3 * K) ^ D * ξ := by
  have hsum (w : Fin 3 → ℝ) (hw : ∀ i, |w i| ≤ K) : |∑ i, w i| ≤ 3 * K := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (s := Finset.univ) (fun i _ => hw i)).trans_eq (by simp))
  have hgap : |(∑ i, v i) - ∑ i, u i| ≤ 3 * ξ := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (s := Finset.univ) (fun i _ => by
        simpa only [abs_sub_comm] using hdist i)).trans_eq (by simp))
  have h := row_center_grid_fit P D hP p (3 * K) K (∑ i, v i) (∑ i, u i) ε η
    hp (by linarith) (by linarith) (hsum v hv) (hsum u hu) m hcode hcoeff G V hfield hfit
  intro j
  have hmul := mul_le_mul_of_nonneg_left hgap
    (by positivity : 0 ≤ ((D : ℝ) + 1) * D * (K + p) * (3 * K) ^ D)
  nlinarith [h j]

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
