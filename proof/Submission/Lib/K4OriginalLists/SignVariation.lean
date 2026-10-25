/-
Adapted from: here:o064
Written in this workspace by session x0217, from the supplied paper,
Lemma a03:actual-lists. No external formal code.
-/

import Mathlib

/-!
Quantitative translation variation of finite polynomial sign descriptions.
This is the one-dimensional boundary estimate used in the base averaging
argument of the supplied paper's Lemma `a03:actual-lists`.
-/

namespace Submission.Lib.K4OriginalLists

open Finset MeasureTheory Set

/-- An arbitrary finite rule on measurable sign tests remains measurable. -/
theorem measurable_sign_rule {X γ : Type*} [MeasurableSpace X] [MeasurableSpace γ]
    {m : ℕ} (f : Fin m → X → ℝ) (hf : ∀ i, Measurable (f i))
    (rule : (Fin m → Bool) → γ) :
    Measurable (fun x => rule (fun i => decide (0 ≤ f i x))) := by
  classical
  apply (measurable_of_countable rule).comp
  apply Measurable.of_eval
  intro i
  apply measurable_to_bool
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    measurableSet_le (measurable_const (a := (0 : ℝ))) (hf i)

/-- Bounded polynomial sign densities are integrable on every finite cell measure. -/
theorem integrable_polynomial_sign_rule_component {m : ℕ} {β : Type*} [Fintype β]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (p : Fin m → Polynomial ℝ)
    (rule : (Fin m → Bool) → β → ℝ) (H : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H) (a : β) :
    Integrable (fun x => rule (fun i => decide (0 ≤ (p i).eval x)) a) ν := by
  classical
  have hmeas := measurable_sign_rule (fun i x => (p i).eval x)
    (fun i => (p i).continuous.measurable) (fun s => rule s a)
  apply Integrable.of_bound hmeas.aestronglyMeasurable H
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    exact (single_le_sum (fun b _ => abs_nonneg _) (mem_univ a)).trans (hbound _))

/-- A change of a polynomial sign under translation occurs near a real root. -/
theorem exists_root_near_sign_change (p : Polynomial ℝ) (h x : ℝ)
    (hne : decide (0 ≤ p.eval x) ≠ decide (0 ≤ p.eval (x + h))) :
    ∃ r ∈ p.roots.toFinset, x ∈ Icc (r - |h|) (r + |h|) := by
  classical
  have hp : p ≠ 0 := by
    intro hp
    simp [hp] at hne
  have hzero : 0 ∈ uIcc (p.eval x) (p.eval (x + h)) := by
    by_cases hx : 0 ≤ p.eval x
    · have hy : p.eval (x + h) < 0 := by
        by_contra hy
        have hy' : 0 ≤ p.eval (x + h) := by linarith
        exact hne (by simp [hx, hy'])
      exact mem_uIcc_of_ge hy.le hx
    · have hy : 0 ≤ p.eval (x + h) := by
        by_contra hy
        exact hne (by simp [hx, hy])
      exact mem_uIcc_of_le (le_of_not_ge hx) hy
  obtain ⟨r, hr, hroot⟩ := intermediate_value_uIcc p.continuous.continuousOn hzero
  refine ⟨r, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hroot), ?_⟩
  rcases mem_uIcc.mp hr with hr | hr
  · constructor <;> linarith [le_abs_self h, neg_abs_le h]
  · constructor <;> linarith [le_abs_self h, neg_abs_le h]

/-- The closed neighborhood of the real roots of a polynomial. -/
noncomputable def polynomialRootNeighborhood (p : Polynomial ℝ) (h : ℝ) : Set ℝ :=
  ⋃ r ∈ p.roots.toFinset, Icc (r - |h|) (r + |h|)

theorem measurableSet_polynomialRootNeighborhood (p : Polynomial ℝ) (h : ℝ) :
    MeasurableSet (polynomialRootNeighborhood p h) := by
  classical
  exact p.roots.toFinset.measurableSet_biUnion (fun _ _ => measurableSet_Icc)

/-- Root neighborhoods have total length at most twice degree times radius. -/
theorem volume_polynomialRootNeighborhood_le (p : Polynomial ℝ) (h : ℝ) :
    volume (polynomialRootNeighborhood p h) ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * |h|) := by
  classical
  have hcard : p.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le _).trans p.card_roots'
  calc
    _ ≤ ∑ r ∈ p.roots.toFinset, volume (Icc (r - |h|) (r + |h|)) :=
      measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((p.roots.toFinset.card : ℝ) * (2 * |h|)) := by
      simp only [Real.volume_Icc]
      simp_rw [show ∀ r : ℝ, (r + |h|) - (r - |h|) = 2 * |h| by intro r; ring]
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * (p.natDegree : ℝ) * |h|) := by
      apply ENNReal.ofReal_le_ofReal
      have hcard' : (p.roots.toFinset.card : ℝ) ≤ p.natDegree := by exact_mod_cast hcard
      nlinarith [abs_nonneg h]

/-- The mass of polynomial sign changes is bounded by degree times translation length. -/
theorem volume_polynomial_sign_change_le (p : Polynomial ℝ) (h : ℝ) :
    volume {x : ℝ | decide (0 ≤ p.eval x) ≠ decide (0 ≤ p.eval (x + h))} ≤
      ENNReal.ofReal (2 * (p.natDegree : ℝ) * |h|) := by
  classical
  apply (measure_mono (t := polynomialRootNeighborhood p h) ?_).trans
    (volume_polynomialRootNeighborhood_le p h)
  intro x hx
  obtain ⟨r, hr, hx⟩ := exists_root_near_sign_change p h x hx
  exact mem_iUnion₂.mpr ⟨r, hr, hx⟩

/-- Neighborhood of every boundary that can occur in a finite sign rule. -/
noncomputable def signRootNeighborhood {m : ℕ} (p : Fin m → Polynomial ℝ) (h : ℝ) : Set ℝ :=
  ⋃ i, polynomialRootNeighborhood (p i) h

theorem measurableSet_signRootNeighborhood {m : ℕ} (p : Fin m → Polynomial ℝ) (h : ℝ) :
    MeasurableSet (signRootNeighborhood p h) :=
  MeasurableSet.iUnion (fun i => measurableSet_polynomialRootNeighborhood (p i) h)

theorem volume_signRootNeighborhood_le {m : ℕ} (p : Fin m → Polynomial ℝ) (h : ℝ) :
    volume (signRootNeighborhood p h) ≤
      ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |h|) := by
  calc
    _ ≤ ∑ i, volume (polynomialRootNeighborhood (p i) h) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (2 * ((p i).natDegree : ℝ) * |h|) :=
      sum_le_sum fun i _ => volume_polynomialRootNeighborhood_le (p i) h
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      simp only [sum_mul, mul_sum]

/-- Away from these boundary neighborhoods, every sign rule is constant throughout a cell. -/
theorem sign_rule_eq_of_not_mem_rootNeighborhood {m : ℕ} {γ : Type*}
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → γ) (ρ x y : ℝ)
    (hx : x ∉ signRootNeighborhood p ρ) (hxy : |x - y| ≤ |ρ|) :
    rule (fun i => decide (0 ≤ (p i).eval x)) =
      rule (fun i => decide (0 ≤ (p i).eval y)) := by
  classical
  apply congrArg rule
  funext i
  by_contra hne
  have hne' : decide (0 ≤ (p i).eval x) ≠ decide (0 ≤ (p i).eval (x + (y - x))) := by
    simpa using hne
  obtain ⟨r, hr, hxr⟩ := exists_root_near_sign_change (p i) (y - x) x hne'
  have hdist : |y - x| ≤ |ρ| := by simpa only [abs_sub_comm] using hxy
  apply hx
  refine mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr ⟨r, hr, ?_⟩⟩
  exact ⟨by linarith [hxr.1], by linarith [hxr.2]⟩

/-- Any rule on finitely many polynomial signs has the same translation estimate.
In particular arbitrary Boolean priority rules introduce no additional boundaries. -/
theorem volume_sign_rule_change_le {m : ℕ} {γ : Type*}
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → γ) (h : ℝ) :
    volume {x : ℝ | rule (fun i => decide (0 ≤ (p i).eval x)) ≠
        rule (fun i => decide (0 ≤ (p i).eval (x + h)))} ≤
      ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |h|) := by
  classical
  have hcover : {x : ℝ | rule (fun i => decide (0 ≤ (p i).eval x)) ≠
      rule (fun i => decide (0 ≤ (p i).eval (x + h)))} ⊆
      ⋃ i : Fin m, {x : ℝ | decide (0 ≤ (p i).eval x) ≠
        decide (0 ≤ (p i).eval (x + h))} := by
    intro x hx
    by_contra hnot
    have heq : ∀ i, decide (0 ≤ (p i).eval x) = decide (0 ≤ (p i).eval (x + h)) := by
      simpa only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] using hnot
    exact hx (congrArg rule (funext heq))
  calc
    _ ≤ volume (⋃ i : Fin m, {x : ℝ | decide (0 ≤ (p i).eval x) ≠
        decide (0 ≤ (p i).eval (x + h))}) := measure_mono hcover
    _ ≤ ∑ i, volume {x : ℝ | decide (0 ≤ (p i).eval x) ≠
        decide (0 ≤ (p i).eval (x + h))} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (2 * ((p i).natDegree : ℝ) * |h|) :=
      sum_le_sum fun i _ => volume_polynomial_sign_change_le (p i) h
    _ = ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |h|) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      simp only [sum_mul, mul_sum]

/-- Joint tagged densities have translation variation controlled by their total density,
without a factor for the number of possible tags. -/
theorem lintegral_sign_vector_variation_le {m : ℕ} {β : Type*} [Fintype β]
    (p : Fin m → Polynomial ℝ) (rule : (Fin m → Bool) → β → ℝ)
    (H h : ℝ) (hbound : ∀ s, ∑ a, |rule s a| ≤ H) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      (∑ a, |rule (fun i => decide (0 ≤ (p i).eval x)) a -
        rule (fun i => decide (0 ≤ (p i).eval (x + h))) a|)) ≤
      ENNReal.ofReal (4 * H * (∑ i, ((p i).natDegree : ℝ)) * |h|) := by
  classical
  let f : ℝ → β → ℝ := fun x => rule (fun i => decide (0 ≤ (p i).eval x))
  let S : Set ℝ := {x | f x ≠ f (x + h)}
  have hH : 0 ≤ H :=
    (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans (hbound _)
  have hpoint : ∀ x, ∑ a, |f x a - f (x + h) a| ≤ 2 * H := by
    intro x
    calc
      _ ≤ ∑ a, (|f x a| + |f (x + h) a|) :=
        sum_le_sum fun a _ => abs_sub (f x a) (f (x + h) a)
      _ = (∑ a, |f x a|) + ∑ a, |f (x + h) a| := sum_add_distrib
      _ ≤ 2 * H := by
        have hx : ∑ a, |f x a| ≤ H := hbound _
        have hy : ∑ a, |f (x + h) a| ≤ H := hbound _
        linarith
  have hdom : ∀ x, ENNReal.ofReal (∑ a, |f x a - f (x + h) a|) ≤
      ENNReal.ofReal (2 * H) * S.indicator 1 x := by
    intro x
    by_cases hx : x ∈ S
    · simpa [Set.indicator_of_mem hx] using ENNReal.ofReal_le_ofReal (hpoint x)
    · have heq : f x = f (x + h) := by simpa [S] using hx
      simp [heq, Set.indicator_of_notMem hx]
  change (∫⁻ x : ℝ, ENNReal.ofReal (∑ a, |f x a - f (x + h) a|)) ≤ _
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (2 * H) * S.indicator 1 x := lintegral_mono hdom
    _ = ENNReal.ofReal (2 * H) * ∫⁻ x : ℝ, S.indicator 1 x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * H) * volume S :=
      mul_le_mul_of_nonneg_left (lintegral_indicator_one_le S) zero_le
    _ ≤ ENNReal.ofReal (2 * H) *
        ENNReal.ofReal (2 * (∑ i, ((p i).natDegree : ℝ)) * |h|) :=
      mul_le_mul_of_nonneg_left (volume_sign_rule_change_le p rule h) zero_le
    _ = ENNReal.ofReal (4 * H * (∑ i, ((p i).natDegree : ℝ)) * |h|) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * H)]
      congr 1
      ring

/-- Integrating the line estimate over bounded transverse support gives the joint estimate.
The polynomial coefficients may depend arbitrarily on the transverse variables. -/
theorem lintegral_sign_vector_transverse_variation_le
    {Y β : Type*} [MeasurableSpace Y] [Fintype β] {m : ℕ}
    (μ : Measure Y) (E : Set Y) (p : Y → Fin m → Polynomial ℝ)
    (rule : (Fin m → Bool) → β → ℝ) (H D h : ℝ)
    (hbound : ∀ s, ∑ a, |rule s a| ≤ H)
    (hdegree : ∀ y ∈ E, ∑ i, ((p y i).natDegree : ℝ) ≤ D)
    (hsupport : ∀ y ∉ E, ∀ t a, rule (fun i => decide (0 ≤ (p y i).eval t)) a = 0) :
    (∫⁻ y, (∫⁻ t : ℝ, ENNReal.ofReal
      (∑ a, |rule (fun i => decide (0 ≤ (p y i).eval t)) a -
        rule (fun i => decide (0 ≤ (p y i).eval (t + h))) a|)) ∂μ) ≤
      ENNReal.ofReal (4 * H * D * |h|) * μ E := by
  classical
  have hH : 0 ≤ H :=
    (sum_nonneg (fun a _ => abs_nonneg (rule (fun _ => false) a))).trans (hbound _)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (4 * H * D * |h|) * E.indicator 1 y ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ E
      · simp only [indicator_of_mem hy, Pi.one_apply, mul_one]
        apply (lintegral_sign_vector_variation_le (p y) rule H h hbound).trans
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hdegree y hy) (by positivity)) (abs_nonneg h)
      · simp only [hsupport y hy, sub_self, abs_zero, sum_const_zero,
          ENNReal.ofReal_zero, lintegral_zero, indicator_of_notMem hy, mul_zero]
        exact le_rfl
    _ = ENNReal.ofReal (4 * H * D * |h|) * ∫⁻ y, E.indicator 1 y ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 * H * D * |h|) * μ E :=
      mul_le_mul_of_nonneg_left (lintegral_indicator_one_le E) zero_le

end Submission.Lib.K4OriginalLists
