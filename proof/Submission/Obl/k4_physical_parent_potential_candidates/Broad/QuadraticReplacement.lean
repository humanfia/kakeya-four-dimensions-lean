-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/QuadraticReplacement.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Mathlib
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketGradient
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-!
# Quadratic replacement of a potential that is quadratic along broad lines

Let `P` be a real polynomial in `n` variables of degree at most `q`.  Suppose that along
every line `s ↦ z₀ + s • w_k` through a common point `z₀`, for a finite family of directions
`w_k`, the restriction `s ↦ P (z₀ + s • w_k)` is within `ε` of a quadratic on `[0, h]`.
Then all its homogeneous parts of degree `j ≥ 3` at `z₀` are `O(ε / h^j)` at the directions
`w_k`.  If the directions are *unisolvent* for homogeneous polynomials of degree `3, …, q`
with constant `Λ` (every such form is bounded on all of space by `Λ` times its maximum on
the directions, times `‖w‖^j`), then `P` is within `C Λ ε Σ_{3 ≤ j ≤ q} (‖z - z₀‖/h)^j` of its
second-order Taylor polynomial at `z₀`.

In the broad completion of `o265` this turns a potential `P_b` of fixed degree `q`, which
along every retained trajectory equals the native quadratic test minus the trajectory's own
intercept, into a quadratic, so the direct candidate exit applies without the seven-direction
restoration (except when the velocities concentrate near a conic, where unisolvence fails).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial

noncomputable section

/-! ### Coefficients of a polynomial that is close to a quadratic on an interval -/

/-- Iterated derivative bound on an interval. -/
theorem exists_iterate_derivative_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : Polynomial ℝ) (a h E : ℝ), p.natDegree ≤ D → 0 < h → 0 ≤ E →
      (∀ t ∈ Set.Icc a (a + h), |p.eval t| ≤ E) →
      ∀ j : ℕ, ∀ t ∈ Set.Icc a (a + h),
        |(Polynomial.derivative^[j] p).eval t| ≤ C ^ j * E / h ^ j := by
  obtain ⟨C, hC, hder⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_polynomial_interval_derivative_bound D
  refine ⟨C, hC, ?_⟩
  intro p a h E hp hh hE hbound j
  induction j with
  | zero =>
      intro t ht
      simpa using hbound t ht
  | succ j ih =>
      intro t ht
      have hdeg : (Polynomial.derivative^[j] p).natDegree ≤ D :=
        (Polynomial.natDegree_iterate_derivative p j).trans (Nat.sub_le _ _ |>.trans hp)
      have hE' : 0 ≤ C ^ j * E / h ^ j := by positivity
      have := hder (Polynomial.derivative^[j] p) a h (C ^ j * E / h ^ j) hdeg hh hE' ih t ht
      rw [Function.iterate_succ_apply']
      calc |(Polynomial.derivative (Polynomial.derivative^[j] p)).eval t|
          ≤ C * (C ^ j * E / h ^ j) / h := this
        _ = C ^ (j + 1) * E / h ^ (j + 1) := by
            rw [pow_succ, pow_succ]; field_simp

lemma iterate_derivative_eval_zero (p : Polynomial ℝ) (j : ℕ) :
    (Polynomial.derivative^[j] p).eval 0 = (j.factorial : ℝ) * p.coeff j := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

/-- **Coefficient extraction.**  A polynomial of degree at most `q` that is within `ε` of a
quadratic on `[0, h]` has its coefficients of degree `j ≥ 3` bounded by `C ε / h^j`. -/
theorem exists_coeff_bound_of_near_quadratic (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (f g : Polynomial ℝ) (h ε : ℝ), f.natDegree ≤ q → g.natDegree ≤ 2 → 0 < h → 0 ≤ ε →
      (∀ s ∈ Set.Icc 0 h, |f.eval s - g.eval s| ≤ ε) →
      ∀ j : ℕ, 3 ≤ j → |f.coeff j| ≤ C * ε / h ^ j := by
  obtain ⟨C₀, hC₀, hiter⟩ := exists_iterate_derivative_bound (q + 2)
  refine ⟨(max 1 C₀) ^ (q + 2), by positivity, ?_⟩
  intro f g h ε hf hg hh hε hclose j hj
  by_cases hjq : q < j
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf hjq), abs_zero]
    positivity
  push Not at hjq
  set p := f - g with hp
  have hpdeg : p.natDegree ≤ q + 2 :=
    (Polynomial.natDegree_sub_le f g).trans (max_le (by omega) (by omega))
  have hpbound : ∀ s ∈ Set.Icc (0:ℝ) (0 + h), |p.eval s| ≤ ε := by
    intro s hs
    rw [zero_add] at hs
    simpa [hp, Polynomial.eval_sub] using hclose s hs
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) (0 + h) := ⟨le_refl _, by linarith⟩
  have hd := hiter p 0 h ε hpdeg hh hε hpbound j 0 h0
  rw [iterate_derivative_eval_zero] at hd
  have hcoeff : p.coeff j = f.coeff j := by
    rw [hp, Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hg (by omega : 2 < j)), sub_zero]
  rw [hcoeff, abs_mul] at hd
  have hfact : (1:ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfabs : |(j.factorial : ℝ)| = j.factorial := abs_of_nonneg (by positivity)
  rw [hfabs] at hd
  have h1 : |f.coeff j| ≤ C₀ ^ j * ε / h ^ j := by
    calc |f.coeff j| ≤ (j.factorial : ℝ) * |f.coeff j| :=
          le_mul_of_one_le_left (abs_nonneg _) hfact
      _ ≤ C₀ ^ j * ε / h ^ j := hd
  have h2 : C₀ ^ j ≤ (max 1 C₀) ^ (q + 2) := by
    calc C₀ ^ j ≤ (max 1 C₀) ^ j :=
          pow_le_pow_left₀ hC₀.le (le_max_right _ _) j
      _ ≤ (max 1 C₀) ^ (q + 2) :=
          pow_le_pow_right₀ (le_max_left _ _) (by omega)
  calc |f.coeff j| ≤ C₀ ^ j * ε / h ^ j := h1
    _ ≤ (max 1 C₀) ^ (q + 2) * ε / h ^ j := by
        gcongr

/-! ### Homogeneous parts along lines -/

variable {n : ℕ}

/-- A homogeneous polynomial of degree `j` scales by `s^j`. -/
theorem IsHomogeneous.eval_smul' {H : MvPolynomial (Fin n) ℝ} {j : ℕ} (hH : H.IsHomogeneous j)
    (s : ℝ) (w : Fin n → ℝ) : MvPolynomial.eval (s • w) H = s ^ j * MvPolynomial.eval w H := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdeg : ∑ i ∈ d.support, d i = j := by
    have := hH (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The translate `w ↦ P (w + z₀)`. -/
def translate (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  aeval (fun i => X i + C (z₀ i)) P

lemma eval_translate (P : MvPolynomial (Fin n) ℝ) (z₀ w : Fin n → ℝ) :
    MvPolynomial.eval w (translate P z₀) = MvPolynomial.eval (w + z₀) P := by
  rw [translate, MvPolynomial.map_aeval]
  simp only [map_add, eval_X, eval_C]
  have hc : (MvPolynomial.eval w).comp (algebraMap ℝ (MvPolynomial (Fin n) ℝ)) =
      RingHom.id ℝ := by
    ext r; simp
  rw [hc]
  rfl

lemma totalDegree_translate_le (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) :
    (translate P z₀).totalDegree ≤ P.totalDegree :=
  Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le P _ (fun i =>
    (totalDegree_add _ _).trans (max_le (by simp) (by simp)))

/-- The homogeneous part of degree `j` of `P` at the base point `z₀`. -/
def homPart (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) (j : ℕ) : MvPolynomial (Fin n) ℝ :=
  homogeneousComponent j (translate P z₀)

lemma homPart_isHomogeneous (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) (j : ℕ) :
    (homPart P z₀ j).IsHomogeneous j :=
  homogeneousComponent_isHomogeneous j _

lemma homPart_eq_zero {P : MvPolynomial (Fin n) ℝ} {q : ℕ} (hq : P.totalDegree ≤ q)
    (z₀ : Fin n → ℝ) {j : ℕ} (hj : q < j) : homPart P z₀ j = 0 :=
  homogeneousComponent_eq_zero j _ (lt_of_le_of_lt ((totalDegree_translate_le P z₀).trans hq) hj)

/-- Taylor decomposition at `z₀` into homogeneous parts up to degree `q`. -/
lemma eval_eq_sum_homPart {P : MvPolynomial (Fin n) ℝ} {q : ℕ} (hq : P.totalDegree ≤ q)
    (z₀ w : Fin n → ℝ) :
    MvPolynomial.eval (w + z₀) P =
      ∑ j ∈ Finset.range (q + 1), MvPolynomial.eval w (homPart P z₀ j) := by
  rw [← eval_translate]
  conv_lhs => rw [← sum_homogeneousComponent (translate P z₀)]
  rw [map_sum]
  have hle : (translate P z₀).totalDegree + 1 ≤ q + 1 :=
    Nat.succ_le_succ ((totalDegree_translate_le P z₀).trans hq)
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  have hzero : ∑ j ∈ Finset.Ico ((translate P z₀).totalDegree + 1) (q + 1),
      MvPolynomial.eval w (homPart P z₀ j) = 0 := by
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_Ico] at hj
    rw [homPart, homogeneousComponent_eq_zero j _ (by omega), map_zero]
  rw [hzero, add_zero]
  rfl

/-- The restriction of `P` to the line `s ↦ s • w + z₀`, as a univariate polynomial whose
coefficients are the homogeneous parts at `z₀`. -/
def restrictLine (P : MvPolynomial (Fin n) ℝ) (z₀ w : Fin n → ℝ) (q : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (q + 1),
    Polynomial.C (MvPolynomial.eval w (homPart P z₀ j)) * Polynomial.X ^ j

lemma eval_restrictLine {P : MvPolynomial (Fin n) ℝ} {q : ℕ} (hq : P.totalDegree ≤ q)
    (z₀ w : Fin n → ℝ) (s : ℝ) :
    (restrictLine P z₀ w q).eval s = MvPolynomial.eval (s • w + z₀) P := by
  rw [eval_eq_sum_homPart hq, restrictLine, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [IsHomogeneous.eval_smul' (homPart_isHomogeneous P z₀ j)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

lemma coeff_restrictLine (P : MvPolynomial (Fin n) ℝ) (z₀ w : Fin n → ℝ) {q j : ℕ}
    (hj : j ≤ q) :
    (restrictLine P z₀ w q).coeff j = MvPolynomial.eval w (homPart P z₀ j) := by
  rw [restrictLine, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hb]
  · intro hjn
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hjn

lemma natDegree_restrictLine_le (P : MvPolynomial (Fin n) ℝ) (z₀ w : Fin n → ℝ) (q : ℕ) :
    (restrictLine P z₀ w q).natDegree ≤ q := by
  rw [restrictLine]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- The second-order Taylor polynomial of `P` at `z₀`. -/
def taylorTwo (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  aeval (fun i => X i - C (z₀ i)) (∑ j ∈ Finset.range 3, homPart P z₀ j)

lemma eval_taylorTwo (P : MvPolynomial (Fin n) ℝ) (z₀ z : Fin n → ℝ) :
    MvPolynomial.eval z (taylorTwo P z₀) =
      ∑ j ∈ Finset.range 3, MvPolynomial.eval (z - z₀) (homPart P z₀ j) := by
  rw [taylorTwo, MvPolynomial.map_aeval]
  simp only [map_sub, eval_X, eval_C]
  have hc : (MvPolynomial.eval z).comp (algebraMap ℝ (MvPolynomial (Fin n) ℝ)) =
      RingHom.id ℝ := by
    ext r; simp
  rw [hc, ← map_sum]
  rfl

lemma totalDegree_taylorTwo_le (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) :
    (taylorTwo P z₀).totalDegree ≤ 2 := by
  refine (Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le _ _ (fun i =>
    (totalDegree_sub _ _).trans (max_le (by simp) (by simp)))).trans ?_
  refine totalDegree_finsetSum_le (fun j hj => ?_)
  exact ((homPart_isHomogeneous P z₀ j).totalDegree_le).trans
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- **Quadratic replacement.** -/
theorem exists_quadratic_replacement (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin n) ℝ) (z₀ : Fin n → ℝ) {ι : Type} [Fintype ι]
      (w : ι → Fin n → ℝ) (Λ h ε : ℝ), P.totalDegree ≤ q → 0 < h → 0 ≤ ε → 0 ≤ Λ →
      (∀ k, ∃ g : Polynomial ℝ, g.natDegree ≤ 2 ∧
        ∀ s ∈ Set.Icc 0 h, |MvPolynomial.eval (s • w k + z₀) P - g.eval s| ≤ ε) →
      (∀ j : ℕ, 3 ≤ j → j ≤ q → ∀ H : MvPolynomial (Fin n) ℝ, H.IsHomogeneous j →
        ∀ M : ℝ, (∀ k, |MvPolynomial.eval (w k) H| ≤ M) →
        ∀ v : Fin n → ℝ, |MvPolynomial.eval v H| ≤ Λ * M * ‖v‖ ^ j) →
      ∀ z : Fin n → ℝ, |MvPolynomial.eval z P - MvPolynomial.eval z (taylorTwo P z₀)| ≤
        C * Λ * ε * ∑ j ∈ Finset.Icc 3 q, (‖z - z₀‖ / h) ^ j := by
  obtain ⟨C, hC, hcoeff⟩ := exists_coeff_bound_of_near_quadratic q
  refine ⟨C, hC, ?_⟩
  intro P z₀ ι _ w Λ h ε hq hh hε hΛ hnear huni z
  have hsplit : MvPolynomial.eval z P - MvPolynomial.eval z (taylorTwo P z₀) =
      ∑ j ∈ Finset.Icc 3 q, MvPolynomial.eval (z - z₀) (homPart P z₀ j) := by
    have hz : z = (z - z₀) + z₀ := by abel
    conv_lhs => rw [hz]
    rw [eval_eq_sum_homPart hq, eval_taylorTwo, sub_add_cancel]
    by_cases h3 : 3 ≤ q + 1
    · rw [← Finset.sum_range_add_sum_Ico _ h3, add_sub_cancel_left]
      apply Finset.sum_congr
      · ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      · intro _ _; rfl
    · push Not at h3
      have hIcc : Finset.Icc 3 q = ∅ := by
        ext j; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [hIcc, Finset.sum_empty, sub_eq_zero]
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : q + 1 ≤ 3)]
      have : ∑ j ∈ Finset.Ico (q + 1) 3, MvPolynomial.eval (z - z₀) (homPart P z₀ j) = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          rw [Finset.mem_Ico] at hj
          rw [homPart_eq_zero hq z₀ (by omega), map_zero])
      rw [this, add_zero]
  rw [hsplit, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
  rw [Finset.mem_Icc] at hj
  have hk : ∀ k, |MvPolynomial.eval (w k) (homPart P z₀ j)| ≤ C * ε / h ^ j := by
    intro k
    obtain ⟨g, hg, hgclose⟩ := hnear k
    have := hcoeff (restrictLine P z₀ (w k) q) g h ε (natDegree_restrictLine_le _ _ _ _) hg hh hε
      (fun s hs => by rw [eval_restrictLine hq]; exact hgclose s hs) j hj.1
    rwa [coeff_restrictLine _ _ _ hj.2] at this
  have := huni j hj.1 hj.2 (homPart P z₀ j) (homPart_isHomogeneous P z₀ j) _ hk (z - z₀)
  calc |MvPolynomial.eval (z - z₀) (homPart P z₀ j)|
      ≤ Λ * (C * ε / h ^ j) * ‖z - z₀‖ ^ j := this
    _ = C * Λ * ε * (‖z - z₀‖ / h) ^ j := by rw [div_pow]; ring

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
