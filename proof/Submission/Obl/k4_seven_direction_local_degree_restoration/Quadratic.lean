import Mathlib

/-! Explicit graph polynomials, with coefficient and hidden derivative bounds. -/

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open MvPolynomial

abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Poly := MvPolynomial (Fin 4) ℝ

/-- The test for a graph whose base polynomial has degree at most two. -/
noncomputable def quadraticGraph (c : ℝ) (l : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) : Poly :=
  X 3 - (C c + ∑ i : Fin 3, C (l i) * X i.castSucc +
    ∑ i : Fin 3, ∑ j : Fin 3, C (q i j) * X i.castSucc * X j.castSucc)

lemma quadraticGraph_totalDegree (c : ℝ) (l : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) :
    (quadraticGraph c l q).totalDegree ≤ 2 := by
  unfold quadraticGraph
  have hterm (c : ℝ) (i : Fin 4) : (C c * X i : Poly).totalDegree ≤ 1 := by
    calc (C c * X i : Poly).totalDegree ≤ (C c : Poly).totalDegree + (X i : Poly).totalDegree :=
           totalDegree_mul _ _
         _ = 1 := by simp
  have hlin : (∑ i : Fin 3, C (l i) * X (R := ℝ) i.castSucc).totalDegree ≤ 2 := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
    exact (hterm _ _).trans (by norm_num)
  have hquad : (∑ i : Fin 3, ∑ j : Fin 3,
      C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).totalDegree ≤ 2 := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj => ?_)
    calc
      (C (q i j) * X i.castSucc * X j.castSucc : Poly).totalDegree ≤
          (C (q i j) * X i.castSucc : Poly).totalDegree + (X j.castSucc : Poly).totalDegree :=
        totalDegree_mul _ _
      _ ≤ 1 + 1 := add_le_add (hterm _ _) (by simp)
      _ = 2 := rfl
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (by simp) hlin)) hquad)

lemma quadraticGraph_pderiv (c : ℝ) (l : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) :
    pderiv (3 : Fin 4) (quadraticGraph c l q) = 1 := by
  have hne : ∀ i : Fin 3, i.castSucc ≠ (3 : Fin 4) := by intro i; fin_cases i <;> decide
  simp [quadraticGraph, pderiv_X, hne]

lemma quadraticGraph_eval (c : ℝ) (l : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ)
    (u : Base) (w : ℝ) :
    eval ![u 0, u 1, u 2, w] (quadraticGraph c l q) =
      w - (c + ∑ i : Fin 3, l i * u i + ∑ i : Fin 3, ∑ j : Fin 3, q i j * u i * u j) := by
  have hcoord : ∀ i : Fin 3, (![u 0, u 1, u 2, w] : Fin 4 → ℝ) i.castSucc = u i := by
    intro i; fin_cases i <;> rfl
  simp [quadraticGraph, hcoord]

lemma abs_coeff_C_le {c Z : ℝ} (hc : |c| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(C c : Poly).coeff e| ≤ Z := by
  rw [coeff_C]
  split_ifs
  · exact hc
  · simpa using (abs_nonneg c).trans hc

lemma abs_coeff_mul_X_le {P : Poly} {Z : ℝ} (hZ : 0 ≤ Z)
    (hP : ∀ e, |P.coeff e| ≤ Z) (i : Fin 4) (e : Fin 4 →₀ ℕ) :
    |(P * X i).coeff e| ≤ Z := by
  rw [coeff_mul_X']
  split_ifs
  · exact hP _
  · simpa using hZ

lemma abs_coeff_X_le_one (i : Fin 4) (e : Fin 4 →₀ ℕ) :
    |(X i : Poly).coeff e| ≤ 1 := by
  rw [coeff_X]
  split_ifs <;> norm_num

/-- A coarse coefficient bound which avoids any assumptions about symmetry of `q`. -/
lemma quadraticGraph_coeff_le {c Z : ℝ} {l : Fin 3 → ℝ} {q : Fin 3 → Fin 3 → ℝ}
    (hZ : 0 ≤ Z) (hc : |c| ≤ Z) (hl : ∀ i, |l i| ≤ Z) (hq : ∀ i j, |q i j| ≤ Z)
    (e : Fin 4 →₀ ℕ) : |(quadraticGraph c l q).coeff e| ≤ 1 + 13 * Z := by
  have hlin : |(∑ i : Fin 3, C (l i) * X (R := ℝ) i.castSucc).coeff e| ≤ 3 * Z := by
    rw [coeff_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ i : Fin 3, |(C (l i) * X (R := ℝ) i.castSucc).coeff e| ≤ ∑ _ : Fin 3, Z :=
        Finset.sum_le_sum fun i hi => abs_coeff_mul_X_le hZ (abs_coeff_C_le (hl i)) _ _
      _ = 3 * Z := by simp
  have hquad : |(∑ i : Fin 3, ∑ j : Fin 3,
      C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).coeff e| ≤ 9 * Z := by
    simp only [coeff_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ i : Fin 3, |∑ j : Fin 3,
          (C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).coeff e| ≤
          ∑ i : Fin 3, ∑ j : Fin 3,
            |(C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).coeff e| :=
        Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, Z := by
        gcongr with i hi j hj
        exact abs_coeff_mul_X_le hZ
          (abs_coeff_mul_X_le hZ (abs_coeff_C_le (hq i j)) _) _ _
      _ = 9 * Z := by simp; ring
  unfold quadraticGraph
  simp only [coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  have habs := abs_sub ((X (3 : Fin 4) : Poly).coeff e)
    (((C c : Poly).coeff e + (∑ i : Fin 3, C (l i) * X (R := ℝ) i.castSucc).coeff e) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).coeff e)
  have hsum := abs_add_le (((C c : Poly).coeff e +
    (∑ i : Fin 3, C (l i) * X (R := ℝ) i.castSucc).coeff e))
    ((∑ i : Fin 3, ∑ j : Fin 3,
      C (q i j) * X (R := ℝ) i.castSucc * X j.castSucc).coeff e)
  have hsum' := abs_add_le (C c |>.coeff e)
    ((∑ i : Fin 3, C (l i) * X (R := ℝ) i.castSucc).coeff e)
  have hconst := abs_coeff_C_le hc e
  have hx := abs_coeff_X_le_one 3 e
  linarith

lemma quadraticGraph_coeff_le_pow {c Z : ℝ} {l : Fin 3 → ℝ} {q : Fin 3 → Fin 3 → ℝ}
    (hZ : 2 ≤ Z) (hc : |c| ≤ Z) (hl : ∀ i, |l i| ≤ Z) (hq : ∀ i j, |q i j| ≤ Z)
    (e : Fin 4 →₀ ℕ) : |(quadraticGraph c l q).coeff e| ≤ Z ^ 5 := by
  have hZ0 : 0 ≤ Z := by linarith
  have hpow : (16 : ℝ) ≤ Z ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
         _ ≤ Z ^ 4 := pow_le_pow_left₀ (by norm_num) hZ 4
  have hlarge : 1 + 13 * Z ≤ 16 * Z := by linarith
  refine (quadraticGraph_coeff_le hZ0 hc hl hq e).trans (hlarge.trans ?_)
  calc 16 * Z ≤ Z ^ 4 * Z := mul_le_mul_of_nonneg_right hpow hZ0
       _ = Z ^ 5 := by ring

end Submission.Obl.k4_seven_direction_local_degree_restoration
