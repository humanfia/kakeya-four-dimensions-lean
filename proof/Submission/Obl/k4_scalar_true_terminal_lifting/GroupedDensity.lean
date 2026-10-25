import Submission.Obl.k4_scalar_true_terminal_lifting.DensityLists

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open Classical in
/-- The list estimate can be summed with the original world weights, even when
many selected labels come from one original world. -/
theorem grouped_listed_shift_density_lower_tail
    {Ω Z I A : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [Fintype A]
    (μ : I → Measure Ω) (ρ : Measure Z) (z : Ω → Z)
    (γ : I → A) (fine : I → Ω → ℤ) (coarse : Ω → ℤ)
    (g : I → Z → ℤ → ℝ≥0∞) (f : A → Z → ℤ → ℝ≥0∞)
    (hg : ∀ i a, Measurable (fun x => g i x a))
    (hf : ∀ a b, Measurable (fun x => f a x b))
    (hslice : ∀ i a S, MeasurableSet S →
      μ i {p | fine i p = a ∧ z p ∈ S} = ∫⁻ x in S, g i x a ∂ρ)
    (Λ : A → Z × ℤ → Finset I)
    (hΛ : ∀ a i, MeasurableSet {p | i ∈ Λ a p})
    (hlist : ∀ i, ∀ᵐ p ∂μ i, i ∈ Λ (γ i) (z p, coarse p))
    (shift : I → Z → ℤ) (hshift : ∀ i, Measurable (shift i))
    (hbins : ∀ i, ∀ᵐ p ∂μ i,
      fine i p = coarse p + shift i (z p) ∨
        fine i p = coarse p + shift i (z p) + 1)
    (D : ℝ≥0∞) (hcard : ∀ a p, ((Λ a p).card : ℝ≥0∞) ≤ D)
    (w : A → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ i, w (γ i) * μ i {p | g i (z p) (fine i p) < ε * f (γ i) (z p) (coarse p)}) ≤
      ε * (2 * D) * ∑ a, w a * ∫⁻ x, ∑' b, f a x b ∂ρ := by
  classical
  have ha (a : A) :
      (∑ i : {i // γ i = a}, μ i.val
        {p | g i.val (z p) (fine i.val p) < ε * f a (z p) (coarse p)}) ≤
          ε * (2 * D) * ∫⁻ x, ∑' b, f a x b ∂ρ := by
    let L : Z × ℤ → Finset {i // γ i = a} := fun p =>
      (Λ a p).subtype (fun i => γ i = a)
    have hL (i : {i // γ i = a}) : MeasurableSet {p | i ∈ L p} := by
      simpa only [L, Finset.mem_subtype] using hΛ a i.val
    have hknown (i : {i // γ i = a}) : ∀ᵐ p ∂μ i.val, i ∈ L (z p, coarse p) := by
      simpa only [L, Finset.mem_subtype, i.property] using hlist i.val
    have hsize (p : Z × ℤ) : ((L p).card : ℝ≥0∞) ≤ D := by
      calc
        _ ≤ ((Λ a p).card : ℝ≥0∞) := by
          exact_mod_cast (show (L p).card ≤ (Λ a p).card by
            dsimp only [L]
            rw [Finset.card_subtype]
            exact Finset.card_filter_le _ _)
        _ ≤ D := hcard a p
    exact listed_shift_density_lower_tail (fun i : {i // γ i = a} => μ i.val) ρ
      (fun _ => z) (fun i => fine i.val) (fun _ => coarse)
      (fun i => g i.val) (f a) (fun i => hg i.val) (hf a)
      (fun i => hslice i.val) L hL hknown (fun i => shift i.val)
      (fun i => hshift i.val) (fun i => hbins i.val) D hsize ε
  rw [← Fintype.sum_fiberwise γ]
  calc
    _ = ∑ a, w a * ∑ i : {i // γ i = a}, μ i.val
        {p | g i.val (z p) (fine i.val p) < ε * f a (z p) (coarse p)} := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ ≤ ∑ a, w a * (ε * (2 * D) * ∫⁻ x, ∑' b, f a x b ∂ρ) :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (ha a)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end Submission.Obl.k4_scalar_true_terminal_lifting
