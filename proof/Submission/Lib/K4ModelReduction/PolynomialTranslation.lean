import Submission.Lib.K4ModelReduction.FiberTranslation

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
Uniform translation bounds for one-dimensional polynomial predicates. These
are the fiber estimates in the supplied paper's joint base-flattening lemma.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

/-- A polynomial inequality has constant truth value on an interval avoiding
all roots. Identically zero polynomials are handled separately by callers. -/
theorem polynomial_nonpos_iff_of_avoiding_roots (p : Polynomial ℝ) (hp : p ≠ 0)
    (x y : ℝ) (hfar : ∀ a ∈ p.roots.toFinset, dist x y < dist x a) :
    (p.eval x ≤ 0 ↔ p.eval y ≤ 0) := by
  have hnozero (hz : 0 ∈ uIcc (p.eval x) (p.eval y)) : False := by
    obtain ⟨a, ha, hroot⟩ := intermediate_value_uIcc p.continuous.continuousOn hz
    have haroot : a ∈ p.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hroot)
    exact (not_lt_of_ge (Real.dist_left_le_of_mem_uIcc ha)) (hfar a haroot)
  constructor
  · intro hx
    by_contra hy
    exact hnozero (mem_uIcc_of_le hx (lt_of_not_ge hy).le)
  · intro hy
    by_contra hx
    exact hnozero (mem_uIcc_of_ge hy (lt_of_not_ge hx).le)

/-- All possible change points of a finite polynomial sign table. -/
noncomputable def polynomialBoundaries {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.biUnion fun i => (p i).roots.toFinset

theorem polynomialBoundaries_card_le {ι : Type*} [Fintype ι] (p : ι → Polynomial ℝ) :
    (polynomialBoundaries p).card ≤ ∑ i, (p i).natDegree := by
  classical
  calc
    (polynomialBoundaries p).card ≤ ∑ i, (p i).roots.toFinset.card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)

theorem polynomial_pattern_locally_constant
    {ι : Type*} [Fintype ι] (p : ι → Polynomial ℝ) (f : ℝ → ℝ)
    (hdepend : ∀ x y, (∀ i, (p i).eval x ≤ 0 ↔ (p i).eval y ≤ 0) → f x = f y)
    (x y : ℝ) (hfar : ∀ a ∈ polynomialBoundaries p, dist x y < dist x a) :
    f x = f y := by
  classical
  apply hdepend
  intro i
  by_cases hp : p i = 0
  · simp [hp]
  · apply polynomial_nonpos_iff_of_avoiding_roots (p i) hp x y
    intro a ha
    exact hfar a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)

/-- A bounded function determined by finitely many polynomial inequality
truth values has translation error controlled by their total degree. This
allows arbitrary Boolean combinations and arbitrary constant labels/heights. -/
theorem polynomial_pattern_translation_bound
    {ι : Type*} [Fintype ι] (p : ι → Polynomial ℝ)
    (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, |f x| ≤ M)
    (hdepend : ∀ x y, (∀ i, (p i).eval x ≤ 0 ↔ (p i).eval y ≤ 0) → f x = f y)
    (h : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal |f (x + h) - f x| ≤
      ENNReal.ofReal (4 * M * ((∑ i, (p i).natDegree : ℕ) : ℝ) * |h|) := by
  have hreal : ((polynomialBoundaries p).card : ℝ) ≤ ((∑ i, (p i).natDegree : ℕ) : ℝ) := by
    exact_mod_cast polynomialBoundaries_card_le p
  refine (fiber_translation_bound f (polynomialBoundaries p) M hM hbound
    (polynomial_pattern_locally_constant p f hdepend) h).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hreal (by positivity)) (abs_nonneg h)

/-- In particular the indicator of one polynomial sublevel set has a
coefficient-independent L1 translation bound linear in its degree. -/
theorem polynomial_sublevel_translation_bound (p : Polynomial ℝ) (h : ℝ) :
    ∫⁻ x : ℝ, ENNReal.ofReal
      |(if p.eval (x + h) ≤ 0 then (1 : ℝ) else 0) - (if p.eval x ≤ 0 then (1 : ℝ) else 0)| ≤
        ENNReal.ofReal (4 * (p.natDegree : ℝ) * |h|) := by
  have hbound (x : ℝ) : |if p.eval x ≤ 0 then (1 : ℝ) else 0| ≤ 1 := by
    split_ifs <;> norm_num
  have hdepend (x y : ℝ)
      (hh : ∀ _i : Fin 1, p.eval x ≤ 0 ↔ p.eval y ≤ 0) :
      (if p.eval x ≤ 0 then (1 : ℝ) else 0) = (if p.eval y ≤ 0 then (1 : ℝ) else 0) := by
    simp only [hh 0]
  have hh := polynomial_pattern_translation_bound (fun _ : Fin 1 => p)
    (fun x => if p.eval x ≤ 0 then (1 : ℝ) else 0) 1 (by norm_num) hbound hdepend h
  simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, mul_one] using hh

end Submission.Lib.K4ModelReduction
