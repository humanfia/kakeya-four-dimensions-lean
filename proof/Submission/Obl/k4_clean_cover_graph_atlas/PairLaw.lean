-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PairLaw.lean (namespace renamed).

import Submission.Obl.k4_original_prior_line_extraction.FiniteDensities

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset

section Density

variable {α : Type*} [Fintype α]

/-- Independent posterior draws, multiplied by the original observation density.
The denominator is zero only where every component is zero. -/
noncomputable def posteriorPairDensity (p : α → ℝ) (a b : α) : ℝ :=
  p a * p b / ∑ c, p c

theorem posteriorPairDensity_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (a b : α) :
    0 ≤ posteriorPairDensity p a b := by
  unfold posteriorPairDensity
  exact div_nonneg (mul_nonneg (hp a) (hp b)) (sum_nonneg fun c _ => hp c)

theorem posteriorPairDensity_sum {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (a : α) :
    ∑ b, posteriorPairDensity p a b = p a := by
  classical
  by_cases hzero : ∑ c, p c = 0
  · have hpa : p a = 0 := le_antisymm
      ((single_le_sum (fun c _ => hp c) (mem_univ a)).trans_eq hzero) (hp a)
    simp [posteriorPairDensity, hzero, hpa]
  · simp only [posteriorPairDensity, ← sum_div, ← mul_sum]
    rw [mul_div_cancel_right₀ _ hzero]

theorem posteriorPairDensity_symm (p : α → ℝ) (a b : α) :
    posteriorPairDensity p a b = posteriorPairDensity p b a := by
  unfold posteriorPairDensity
  rw [mul_comm]

theorem posteriorPairDensity_sum_left {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (b : α) :
    ∑ a, posteriorPairDensity p a b = p b := by
  simp_rw [posteriorPairDensity_symm p _ b]
  exact posteriorPairDensity_sum hp b

theorem posteriorPairDensity_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (a b : α) :
    posteriorPairDensity p a b ≤ p a := by
  rw [← posteriorPairDensity_sum hp a]
  exact single_le_sum (fun b _ => posteriorPairDensity_nonneg hp a b) (mem_univ b)

theorem posteriorPairDensity_sum_ofReal {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (a : α) :
    ∑ b, ENNReal.ofReal (posteriorPairDensity p a b) = ENNReal.ofReal (p a) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => posteriorPairDensity_nonneg hp a b),
    posteriorPairDensity_sum hp]

end Density

section Law

variable {α X : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace X]

/-- The finite indexed original observation law. -/
noncomputable def originalLabelLaw (μ : Measure X) (p : X → α → ℝ) : Measure (α × X) :=
  Submission.Obl.k4_original_prior_line_extraction.indexedLaw μ
    (fun a x => ENNReal.ofReal (p x a))

/-- The unnormalized posterior pair law at the original observation. -/
noncomputable def posteriorPairLaw (μ : Measure X) (p : X → α → ℝ) :
    Measure ((α × α) × X) :=
  Submission.Obl.k4_original_prior_line_extraction.indexedLaw μ
    (fun a x => ENNReal.ofReal (posteriorPairDensity (p x) a.1 a.2))

/-- The first marginal of the posterior pair law is exactly the original covered law. -/
theorem posteriorPairLaw_first_marginal (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a) :
    (posteriorPairLaw μ p).map (fun q => (q.1.1, q.2)) = originalLabelLaw μ p := by
  classical
  have hm : Measurable (fun q : (α × α) × X => (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hd (a b : α) : Measurable (fun x =>
      ENNReal.ofReal (posteriorPairDensity (p x) a b)) := by
    unfold posteriorPairDensity
    fun_prop
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE]
  unfold posteriorPairLaw originalLabelLaw
  rw [Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ (hE.preimage hm),
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ hE,
    Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  change (∑ b, ∫⁻ x in {x | (a, x) ∈ E},
    ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ) = _
  rw [← lintegral_finsetSum univ (fun b _ => hd a b)]
  simp_rw [posteriorPairDensity_sum_ofReal (hp _)]

/-- The second marginal is the same original covered law. -/
theorem posteriorPairLaw_second_marginal (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a) :
    (posteriorPairLaw μ p).map (fun q => (q.1.2, q.2)) = originalLabelLaw μ p := by
  classical
  have hm : Measurable (fun q : (α × α) × X => (q.1.2, q.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hd (a b : α) : Measurable (fun x =>
      ENNReal.ofReal (posteriorPairDensity (p x) a b)) := by
    unfold posteriorPairDensity
    fun_prop
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE]
  unfold posteriorPairLaw originalLabelLaw
  rw [Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ (hE.preimage hm),
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ hE,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply sum_congr rfl
  intro b _
  change (∑ a, ∫⁻ x in {x | (b, x) ∈ E},
    ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ) = _
  rw [← lintegral_finsetSum univ (fun a _ => hd a b)]
  simp_rw [posteriorPairDensity_symm (p _) _ b, posteriorPairDensity_sum_ofReal (hp _)]

/-- Pairing preserves the original covered mass, including when it is small. -/
theorem posteriorPairLaw_univ (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a) :
    posteriorPairLaw μ p univ = originalLabelLaw μ p univ := by
  rw [← posteriorPairLaw_first_marginal μ p hpmeas hp]
  exact (Measure.map_apply ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    MeasurableSet.univ).symm

/-- Support statements are checked only on pairs of positive component densities. -/
theorem posteriorPairLaw_ae (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    {P : (α × α) × X → Prop}
    (hP : ∀ a b, ∀ᵐ x ∂μ, 0 < p x a → 0 < p x b → P ((a, b), x)) :
    ∀ᵐ q ∂posteriorPairLaw μ p, P q := by
  apply Submission.Obl.k4_original_prior_line_extraction.indexedLaw_ae
  · intro a
    unfold posteriorPairDensity
    fun_prop
  · intro a
    filter_upwards [hP a.1 a.2] with x hx hpos
    have h₁ : 0 < p x a.1 := by
      by_contra! hn
      have hz := le_antisymm hn (hp x a.1)
      simp [posteriorPairDensity, hz] at hpos
    have h₂ : 0 < p x a.2 := by
      by_contra! hn
      have hz := le_antisymm hn (hp x a.2)
      simp [posteriorPairDensity, hz] at hpos
    exact hx h₁ h₂

end Law

end Submission.Obl.k4_clean_cover_graph_atlas
