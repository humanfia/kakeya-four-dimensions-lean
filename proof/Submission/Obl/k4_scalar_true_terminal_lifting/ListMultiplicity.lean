import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_scalar_true_terminal_lifting

/-- An almost-sure list of possible restriction labels bounds the sum of the
restricted measures by its cardinality times the original measure. -/
theorem sum_restrict_le_smul_of_list
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (L : Ω → Finset I) (hknown : ∀ i, ∀ᵐ z ∂μ.restrict (C i), i ∈ L z)
    (D : ℝ≥0∞) (hcard : ∀ z, ((L z).card : ℝ≥0∞) ≤ D) :
    (∑ i, μ.restrict (C i)) ≤ D • μ := by
  classical
  let f : I → Ω → ℝ≥0∞ := fun i => (C i).indicator 1
  have hrep (i : I) : μ.restrict (C i) = μ.withDensity (f i) :=
    (withDensity_indicator_one (hC i)).symm
  have hf (i : I) : Measurable (f i) :=
    (measurable_const : Measurable (fun _ : Ω => (1 : ℝ≥0∞))).indicator (hC i)
  have hsum : (∑ i, μ.restrict (C i)) = μ.withDensity (fun z => ∑ i, f i z) := by
    simp_rw [hrep]
    rw [← Measure.sum_fintype, ← withDensity_tsum hf]
    congr 1
    ext z
    simp [tsum_fintype]
  have hae : ∀ᵐ z ∂μ, ∀ i, z ∈ C i → i ∈ L z :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hC i)).mp (hknown i))
  have hden : (fun z => ∑ i, f i z) ≤ᵐ[μ] fun _ => D := by
    filter_upwards [hae] with z hz
    have hi (i : I) : f i z ≤ if i ∈ L z then (1 : ℝ≥0∞) else 0 := by
      by_cases hc : z ∈ C i
      · simp [f, hc, hz i hc]
      · simp [f, hc]
    calc
      _ ≤ ∑ i, if i ∈ L z then (1 : ℝ≥0∞) else 0 := Finset.sum_le_sum fun i _ => hi i
      _ = ((L z).card : ℝ≥0∞) := by rw [← Finset.sum_filter]; simp
      _ ≤ D := hcard z
  rw [hsum, ← withDensity_const]
  exact withDensity_mono hden

open Classical in
/-- The preceding multiplicity bound, grouped by original worlds and multiplied
by their original weights. -/
theorem grouped_restriction_mass_le
    {Ω I A : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype A]
    (μ : A → Measure Ω) (γ : I → A) (C : I → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (L : A → Ω → Finset I)
    (hknown : ∀ i, ∀ᵐ z ∂(μ (γ i)).restrict (C i), i ∈ L (γ i) z)
    (D : ℝ≥0∞) (hcard : ∀ a z, ((L a z).card : ℝ≥0∞) ≤ D)
    (w : A → ℝ≥0∞) (E : A → Set Ω) :
    (∑ i, w (γ i) * (μ (γ i)).restrict (C i) (E (γ i))) ≤
      D * ∑ a, w a * μ a (E a) := by
  classical
  have ha (a : A) : (∑ i : {i // γ i = a}, (μ a).restrict (C i.val) (E a)) ≤
      D * μ a (E a) := by
    let La : Ω → Finset {i // γ i = a} := fun z => (L a z).subtype (fun i => γ i = a)
    have hk (i : {i // γ i = a}) : ∀ᵐ z ∂(μ a).restrict (C i.val), i ∈ La z := by
      simpa only [La, Finset.mem_subtype, i.property] using hknown i.val
    have hc (z : Ω) : ((La z).card : ℝ≥0∞) ≤ D := by
      calc
        _ ≤ ((L a z).card : ℝ≥0∞) := by
          exact_mod_cast (show (La z).card ≤ (L a z).card by
            dsimp only [La]
            rw [Finset.card_subtype]
            exact Finset.card_filter_le _ _)
        _ ≤ D := hcard a z
    have hm := sum_restrict_le_smul_of_list (μ a) (fun i : {i // γ i = a} => C i.val)
      (fun i => hC i.val) La hk D hc
    simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using
      (Measure.le_iff'.mp hm (E a))
  rw [← Fintype.sum_fiberwise γ]
  calc
    _ = ∑ a, w a * ∑ i : {i // γ i = a}, (μ a).restrict (C i.val) (E a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ ≤ ∑ a, w a * (D * μ a (E a)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (ha a)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- A list-known family of parent selections also controls arbitrary measurable
subselections. This converts a sum of transported retained masses to the mass
of their original-world union, at the same list-size loss. -/
theorem grouped_subselection_mass_le_union
    {Ω I A : Type*} [MeasurableSpace Ω] [Fintype I] [Fintype A]
    (μ : A → Measure Ω) (γ : I → A) (C : I → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (L : A → Ω → Finset I)
    (hknown : ∀ i, ∀ᵐ z ∂(μ (γ i)).restrict (C i), i ∈ L (γ i) z)
    (D : ℝ≥0∞) (hcard : ∀ a z, ((L a z).card : ℝ≥0∞) ≤ D)
    (w : A → ℝ≥0∞) (R : I → Set Ω) (hR : ∀ i, MeasurableSet (R i))
    (hsub : ∀ i, R i ⊆ C i) :
    (∑ i, w (γ i) * μ (γ i) (R i)) ≤
      D * ∑ a, w a * μ a {z | ∃ i, γ i = a ∧ z ∈ R i} := by
  have hi (i : I) : μ (γ i) (R i) ≤
      (μ (γ i)).restrict (C i) {z | ∃ i', γ i' = γ i ∧ z ∈ R i'} := by
    calc
      _ = (μ (γ i)).restrict (C i) (R i) := by
        rw [Measure.restrict_apply (hR i), Set.inter_eq_left.mpr (hsub i)]
      _ ≤ _ := measure_mono (show R i ⊆ {z | ∃ i', γ i' = γ i ∧ z ∈ R i'} from
        fun z hz => ⟨i, rfl, hz⟩)
  exact (Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (hi i)).trans
    (grouped_restriction_mass_le μ γ C hC L hknown D hcard w
      (fun a => {z | ∃ i, γ i = a ∧ z ∈ R i}))

end Submission.Obl.k4_scalar_true_terminal_lifting
