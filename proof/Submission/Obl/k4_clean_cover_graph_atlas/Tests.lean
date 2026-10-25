-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Tests.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Tests.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Interface
import Submission.Lib.K4XInterface.Formats
import Submission.Lib.K4XInterface.Charts
import Submission.Lib.K4QuadraticSheets.QuadTest

/-!
# Whole-block tests from finitely many times, and their Boolean formats

A test `R` of total degree at most two restricted to a line `t ↦ x l t` is a quadratic in `t`
(`eval_gx_eq_quadratic`), its hidden derivative is affine in `t` and its second hidden
derivative is constant. Hence bounds at the two endpoints and the midpoint of a block give
whole-block bounds (`whole_block_of_three_points`). The point conditions are polynomial in the
line coordinates (`slicePoly`, `slice7Poly`), so the sets they cut out have a fixed Boolean
format.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Submission.Lib.K4XInterface

section Degree

variable {R : Type*} [CommSemiring R] {σ τ : Type*}

/-- Substitution of polynomials of degree at most `s` multiplies the total degree by at most `s`. -/
theorem totalDegree_eval₂C_le (g : σ → MvPolynomial τ R) {s : ℕ}
    (hg : ∀ i, (g i).totalDegree ≤ s) (P : MvPolynomial σ R) :
    (eval₂ C g P).totalDegree ≤ s * P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [eval₂_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ e.support, (g i ^ e i).totalDegree ≤ ∑ i ∈ e.support, e i * s := by
        apply Finset.sum_le_sum
        intro i _
        exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))
    _ = s * e.sum (fun _ k => k) := by
        simp only [Finsupp.sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _
    _ ≤ s * P.totalDegree := Nat.mul_le_mul_left s (le_totalDegree he)

end Degree

section Line

/-- The coordinates of a line `t ↦ v + t w` as real polynomials in `t`. -/
noncomputable def linePolyR {σ : Type*} (v w : σ → ℝ) (i : σ) : Polynomial ℝ :=
  Polynomial.C (v i) + Polynomial.X * Polynomial.C (w i)

/-- A real polynomial restricted to the line `t ↦ v + t w`. -/
noncomputable def lineRestrR {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C (linePolyR v w) Q

theorem eval_lineRestrR {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) (t : ℝ) :
    (lineRestrR Q v w).eval t = MvPolynomial.eval (fun i => v i + t * w i) Q := by
  rw [lineRestrR, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r
    simp
  · ext i
    simp only [linePolyR, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Function.comp_apply]

theorem natDegree_lineRestrR_le {σ : Type*} (Q : MvPolynomial σ ℝ) (v w : σ → ℝ) :
    (lineRestrR Q v w).natDegree ≤ Q.totalDegree := by
  classical
  rw [lineRestrR]
  conv_lhs => rw [Q.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hQ : ∀ i, (linePolyR v w i).natDegree ≤ 1 := by
    intro i
    rw [linePolyR]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply (Polynomial.natDegree_mul_le).trans
      simp
  calc
    (m.prod fun i e => linePolyR v w i ^ e).natDegree ≤
        m.sum (fun i e => (linePolyR v w i ^ e).natDegree) := Polynomial.natDegree_prod_le _ _
    _ ≤ m.sum (fun _ e => e) := by
        apply Finset.sum_le_sum
        intro i _
        apply (Polynomial.natDegree_pow_le).trans
        calc m i * (linePolyR v w i).natDegree ≤ m i * 1 := Nat.mul_le_mul_left _ (hQ i)
          _ = m i := mul_one _
    _ ≤ Q.totalDegree := le_totalDegree hm

/-- The base point and direction of the frozen line `t ↦ x l t`. -/
def gxBase (l : ℕ × (Fin 6 → ℝ)) : Fin 4 → ℝ := ![0, l.2 0, l.2 1, l.2 2]
def gxDir (l : ℕ × (Fin 6 → ℝ)) : Fin 4 → ℝ := ![1, l.2 3, l.2 4, l.2 5]

theorem gx_eq_line (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    gx l t = fun i => gxBase l i + t * gxDir l i := by
  ext i
  fin_cases i <;> simp [gx, gxBase, gxDir]

/-- A test of total degree at most `d` along a line is a polynomial of degree at most `d` in `t`. -/
theorem eval_gx_eq_poly (P : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ P.totalDegree ∧ ∀ t, MvPolynomial.eval (gx l t) P = p.eval t :=
  ⟨lineRestrR P (gxBase l) (gxDir l), natDegree_lineRestrR_le _ _ _, fun t => by
    rw [eval_lineRestrR, gx_eq_line]⟩

end Line

section Interp

/-- A quadratic bounded at the two endpoints and the midpoint of an interval is bounded by three
times that bound on the interval (the Lagrange basis functions are bounded by one there). -/
theorem abs_quadratic_le_three {a b c t₀ t₂ m t : ℝ} (h02 : t₀ < t₂)
    (h₀ : |a + b * t₀ + c * t₀ ^ 2| ≤ m)
    (h₁ : |a + b * ((t₀ + t₂) / 2) + c * ((t₀ + t₂) / 2) ^ 2| ≤ m)
    (h₂ : |a + b * t₂ + c * t₂ ^ 2| ≤ m) (ht : t ∈ Set.Icc t₀ t₂) :
    |a + b * t + c * t ^ 2| ≤ 3 * m := by
  set q : ℝ → ℝ := fun s => a + b * s + c * s ^ 2 with hq
  set t₁ := (t₀ + t₂) / 2
  set L := t₂ - t₀ with hL
  have hLpos : 0 < L := by linarith
  set s := (t - t₀) / L with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hLpos.le
  have hs1 : s ≤ 1 := (div_le_one hLpos).mpr (by linarith [ht.2])
  have ht_eq : t = t₀ + s * L := by rw [hs]; field_simp; ring
  -- Lagrange interpolation identity
  have hlag : q t = q t₀ * (2 * (s - 1 / 2) * (s - 1)) + q t₁ * (4 * s * (1 - s)) +
      q t₂ * (2 * s * (s - 1 / 2)) := by
    simp only [hq, t₁]
    rw [ht_eq]
    have : t₂ = t₀ + L := by rw [hL]; ring
    rw [this]
    ring
  have l0 : |2 * (s - 1 / 2) * (s - 1)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have l1 : |4 * s * (1 - s)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (2 * s - 1)]
  have l2 : |2 * s * (s - 1 / 2)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hm : 0 ≤ m := (abs_nonneg _).trans h₀
  change |q t| ≤ 3 * m
  rw [hlag]
  calc |q t₀ * (2 * (s - 1 / 2) * (s - 1)) + q t₁ * (4 * s * (1 - s)) +
        q t₂ * (2 * s * (s - 1 / 2))|
      ≤ |q t₀ * (2 * (s - 1 / 2) * (s - 1))| + |q t₁ * (4 * s * (1 - s))| +
        |q t₂ * (2 * s * (s - 1 / 2))| := abs_add_three _ _ _
    _ = |q t₀| * |2 * (s - 1 / 2) * (s - 1)| + |q t₁| * |4 * s * (1 - s)| +
        |q t₂| * |2 * s * (s - 1 / 2)| := by
          rw [abs_mul (q t₀), abs_mul (q t₁), abs_mul (q t₂)]
    _ ≤ m * 1 + m * 1 + m * 1 := by
        have e0 := mul_le_mul h₀ l0 (abs_nonneg _) hm
        have e1 := mul_le_mul h₁ l1 (abs_nonneg _) hm
        have e2 := mul_le_mul h₂ l2 (abs_nonneg _) hm
        linarith
    _ = 3 * m := by ring

/-- An affine function bounded at the endpoints of an interval is bounded on it. -/
theorem abs_affine_le {a b t₀ t₂ m t : ℝ} (h₀ : |a + b * t₀| ≤ m) (h₂ : |a + b * t₂| ≤ m)
    (ht : t ∈ Set.Icc t₀ t₂) : |a + b * t| ≤ m := by
  rcases eq_or_lt_of_le (ht.1.trans ht.2) with h | h
  · have : t = t₀ := le_antisymm (h ▸ ht.2) ht.1
    rw [this]; exact h₀
  · set s := (t - t₀) / (t₂ - t₀)
    have hpos : 0 < t₂ - t₀ := by linarith
    have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hpos.le
    have hs1 : s ≤ 1 := (div_le_one hpos).mpr (by linarith [ht.2])
    have heq : a + b * t = (1 - s) * (a + b * t₀) + s * (a + b * t₂) := by
      have : t = t₀ + s * (t₂ - t₀) := by
        simp only [s]; field_simp; ring
      rw [this]; ring
    rw [heq]
    calc |(1 - s) * (a + b * t₀) + s * (a + b * t₂)|
        ≤ |(1 - s) * (a + b * t₀)| + |s * (a + b * t₂)| := abs_add_le _ _
      _ = (1 - s) * |a + b * t₀| + s * |a + b * t₂| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hs0]
      _ ≤ (1 - s) * m + s * m := by gcongr
      _ = m := by ring

end Interp

section WholeBlock

/-- A polynomial of degree at most two evaluates as `a + b t + c t²`. -/
theorem eval_eq_quadratic {p : Polynomial ℝ} (hp : p.natDegree ≤ 2) (t : ℝ) :
    p.eval t = p.coeff 0 + p.coeff 1 * t + p.coeff 2 * t ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ]

/-- A test of total degree at most two along a line: bounds at the endpoints and midpoint of a
block give whole-block bounds for the value (factor three) and the hidden derivative. -/
theorem whole_block_of_three_points {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) {t₀ t₂ m₀ m₁ : ℝ} (h02 : t₀ < t₂)
    (h₀ : |MvPolynomial.eval (gx l t₀) P| ≤ m₀)
    (h₁ : |MvPolynomial.eval (gx l ((t₀ + t₂) / 2)) P| ≤ m₀)
    (h₂ : |MvPolynomial.eval (gx l t₂) P| ≤ m₀)
    (d₀ : |MvPolynomial.eval (gx l t₀) (pderiv (3 : Fin 4) P)| ≤ m₁)
    (d₂ : |MvPolynomial.eval (gx l t₂) (pderiv (3 : Fin 4) P)| ≤ m₁) :
    ∀ t ∈ Set.Icc t₀ t₂, |MvPolynomial.eval (gx l t) P| ≤ 3 * m₀ ∧
      |MvPolynomial.eval (gx l t) (pderiv (3 : Fin 4) P)| ≤ m₁ := by
  intro t ht
  obtain ⟨p, hp, hpe⟩ := eval_gx_eq_poly P l
  have hp2 : p.natDegree ≤ 2 := hp.trans hP
  have hd1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 :=
    Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' P _ hP
  obtain ⟨q, hq, hqe⟩ := eval_gx_eq_poly (pderiv (3 : Fin 4) P) l
  have hq1 : q.natDegree ≤ 1 := hq.trans hd1
  constructor
  · rw [hpe] at h₀ h₁ h₂ ⊢
    rw [eval_eq_quadratic hp2] at h₀ h₁ h₂ ⊢
    exact abs_quadratic_le_three h02 h₀ h₁ h₂ ht
  · rw [hqe] at d₀ d₂ ⊢
    have hlin : ∀ s, q.eval s = q.coeff 0 + q.coeff 1 * s := by
      intro s
      rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
      simp [Finset.sum_range_succ]
    rw [hlin] at d₀ d₂ ⊢
    exact abs_affine_le d₀ d₂ ht

/-- The second hidden derivative of a test of degree at most two is constant. -/
theorem eval_pderiv_pderiv_const {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (x y : Fin 4 → ℝ) :
    MvPolynomial.eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) =
      MvPolynomial.eval y (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  have h1 := Submission.Lib.K4QuadraticSheets.eval_pderiv2_eq_qc (n := 3) P hP x
  have h2 := Submission.Lib.K4QuadraticSheets.eval_pderiv2_eq_qc (n := 3) P hP y
  exact h1.trans h2.symm

end WholeBlock

section Formats

/-- The frozen line point at a fixed time, as polynomials in the six line coordinates. -/
noncomputable def gxPoly (t : ℝ) : Fin 4 → MvPolynomial (Fin 6) ℝ :=
  ![C t, X 0 + C t * X 3, X 1 + C t * X 4, X 2 + C t * X 5]

/-- A test at a fixed time, as a polynomial in the line coordinates. -/
noncomputable def slicePoly (t : ℝ) (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 6) ℝ :=
  eval₂ C (gxPoly t) P

theorem eval_slicePoly (t : ℝ) (P : MvPolynomial (Fin 4) ℝ) (i : ℕ) (x : Fin 6 → ℝ) :
    MvPolynomial.eval x (slicePoly t P) = MvPolynomial.eval (gx (i, x) t) P := by
  rw [slicePoly, MvPolynomial.eval_eval₂]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r
    simp
  · funext j
    fin_cases j <;> simp [gxPoly, gx]

theorem totalDegree_gxPoly_le (t : ℝ) (j : Fin 4) : (gxPoly t j).totalDegree ≤ 1 := by
  fin_cases j
  · simp [gxPoly]
  all_goals
    simp only [gxPoly, Fin.isValue]
    refine (totalDegree_add _ _).trans (max_le (by simp [totalDegree_X]) ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]

theorem totalDegree_slicePoly_le (t : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (slicePoly t P).totalDegree ≤ P.totalDegree := by
  have := totalDegree_eval₂C_le (gxPoly t) (s := 1) (totalDegree_gxPoly_le t) P
  simpa [slicePoly] using this

/-- The frozen graph point of an incidence, as polynomials in the seven incidence coordinates
(six line coordinates and time). -/
noncomputable def gx7Poly : Fin 4 → MvPolynomial (Fin 7) ℝ :=
  ![X 6, X 0 + X 6 * X 3, X 1 + X 6 * X 4, X 2 + X 6 * X 5]

/-- A test at an incidence, as a polynomial in the incidence coordinates. -/
noncomputable def incPoly (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 7) ℝ :=
  eval₂ C gx7Poly P

theorem eval_incPoly (P : MvPolynomial (Fin 4) ℝ) (i : ℕ) (x₁ : Fin 7 → ℝ) :
    MvPolynomial.eval x₁ (incPoly P) =
      MvPolynomial.eval (gx (i, fun j₁ : Fin 6 => x₁ j₁.castSucc) (x₁ 6)) P := by
  rw [incPoly, MvPolynomial.eval_eval₂]
  simp only [MvPolynomial.eval]
  congr 1
  · ext r
    simp
  · funext j
    fin_cases j <;> simp [gx7Poly, gx]

theorem totalDegree_gx7Poly_le (j : Fin 4) : (gx7Poly j).totalDegree ≤ 2 := by
  fin_cases j
  · simp [gx7Poly, totalDegree_X]
  all_goals
    simp only [gx7Poly, Fin.isValue]
    refine (totalDegree_add _ _).trans (max_le (by simp [totalDegree_X]) ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_X]

theorem totalDegree_incPoly_le (P : MvPolynomial (Fin 4) ℝ) :
    (incPoly P).totalDegree ≤ 2 * P.totalDegree := by
  simpa [incPoly] using totalDegree_eval₂C_le gx7Poly (s := 2) totalDegree_gx7Poly_le P

/-- `|p| ≤ m` as one polynomial sign condition `0 ≤ m² - p²`. -/
theorem gfmt_abs_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {m : ℝ} (hm : 0 ≤ m) :
    gfmt n 1 (2 * p.totalDegree) {x | |MvPolynomial.eval x p| ≤ m} := by
  have h := gfmt_nonneg (C (m ^ 2) - p ^ 2)
  have hdeg : (C (m ^ 2) - p ^ 2).totalDegree ≤ 2 * p.totalDegree := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_C]; exact Nat.zero_le _
    · refine (totalDegree_pow _ _).trans ?_
      omega
  have hset : {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x (C (m ^ 2) - p ^ 2)} =
      {x | |MvPolynomial.eval x p| ≤ m} := by
    ext x
    simp only [Set.mem_ofPred_eq, map_sub, eval_C, map_pow]
    constructor
    · intro hx
      exact abs_le_of_sq_le_sq' (by linarith) hm |>.2 |> fun h2 =>
        abs_le.mpr ⟨(abs_le_of_sq_le_sq' (by linarith) hm).1, h2⟩
    · intro hx
      have := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
      linarith
  rw [← hset]
  exact gfmt_mono le_rfl hdeg h

/-- `m ≤ |p|` as one polynomial sign condition `0 ≤ p² - m²`. -/
theorem gfmt_le_abs {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {m : ℝ} (hm : 0 ≤ m) :
    gfmt n 1 (2 * p.totalDegree) {x | m ≤ |MvPolynomial.eval x p|} := by
  have h := gfmt_nonneg (p ^ 2 - C (m ^ 2))
  have hdeg : (p ^ 2 - C (m ^ 2)).totalDegree ≤ 2 * p.totalDegree := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_pow _ _).trans ?_
      omega
    · rw [totalDegree_C]; exact Nat.zero_le _
  have hset : {x : Fin n → ℝ | 0 ≤ MvPolynomial.eval x (p ^ 2 - C (m ^ 2))} =
      {x | m ≤ |MvPolynomial.eval x p|} := by
    ext x
    simp only [Set.mem_ofPred_eq, map_sub, eval_C, map_pow]
    constructor
    · intro hx
      have : m ^ 2 ≤ |MvPolynomial.eval x p| ^ 2 := by rw [sq_abs]; linarith
      exact (pow_le_pow_iff_left₀ hm (abs_nonneg _) (by norm_num)).mp this
    · intro hx
      have := pow_le_pow_left₀ hm hx 2
      rw [sq_abs] at this
      linarith
  rw [← hset]
  exact gfmt_mono le_rfl hdeg h

end Formats

end Submission.Obl.k4_clean_cover_graph_atlas
