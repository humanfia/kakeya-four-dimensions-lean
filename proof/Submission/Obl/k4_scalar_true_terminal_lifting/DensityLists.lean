import Mathlib
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open Classical in
/-- A density lower tail is controlled by the number of compatible fine labels.
Compatibility may depend on the continuous observation. Only the fine slice law is
needed; the comparison density need not be the law of the coarse labels. -/
theorem compatible_density_lower_tail
    {Ω Z A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Countable A] [Countable B]
    (μ : Measure Ω) (ρ : Measure Z) (z : Ω → Z) (fine : Ω → A) (coarse : Ω → B)
    (g : Z → A → ℝ≥0∞) (f : Z → B → ℝ≥0∞)
    (hg : ∀ a, Measurable (fun x => g x a))
    (hf : ∀ b, Measurable (fun x => f x b))
    (hslice : ∀ a S, MeasurableSet S →
      μ {p | fine p = a ∧ z p ∈ S} = ∫⁻ x in S, g x a ∂ρ)
    (R : Z → A → B → Prop) (hRm : ∀ a b, MeasurableSet {x | R x a b})
    (hR : ∀ᵐ p ∂μ, R (z p) (fine p) (coarse p))
    (D : ℝ≥0∞) (hD : ∀ x b, ∑' a, (if R x a b then (1 : ℝ≥0∞) else 0) ≤ D)
    (ε : ℝ≥0∞) :
    μ {p | g (z p) (fine p) < ε * f (z p) (coarse p)} ≤
      ε * D * ∫⁻ x, ∑' b, f x b ∂ρ := by
  classical
  let E : A → B → Set Z := fun a b => {x | R x a b ∧ g x a < ε * f x b}
  have hE (a : A) (b : B) : MeasurableSet (E a b) :=
    (hRm a b).inter (measurableSet_lt (hg a) (measurable_const.mul (hf b)))
  have hcover : {p | g (z p) (fine p) < ε * f (z p) (coarse p)} ≤ᵐ[μ]
      ⋃ ab : A × B, {p | fine p = ab.1 ∧ z p ∈ E ab.1 ab.2} := by
    filter_upwards [hR] with p hp hbad
    exact mem_iUnion.mpr ⟨(fine p, coarse p), rfl, hp, hbad⟩
  have hterm (a : A) (b : B) :
      μ {p | fine p = a ∧ z p ∈ E a b} ≤
        ∫⁻ x, {x | R x a b}.indicator (fun x => ε * f x b) x ∂ρ := by
    rw [hslice a _ (hE a b), ← lintegral_indicator (hE a b)]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ E a b
    · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ {x | R x a b} from hx.1)]
      exact hx.2.le
    · rw [indicator_of_notMem hx]
      exact zero_le
  calc
    _ ≤ μ (⋃ ab : A × B, {p | fine p = ab.1 ∧ z p ∈ E ab.1 ab.2}) :=
      measure_mono_ae hcover
    _ ≤ ∑' ab : A × B, μ {p | fine p = ab.1 ∧ z p ∈ E ab.1 ab.2} :=
      measure_iUnion_le _
    _ ≤ ∑' ab : A × B, ∫⁻ x, {x | R x ab.1 ab.2}.indicator
        (fun x => ε * f x ab.2) x ∂ρ :=
      ENNReal.tsum_le_tsum fun ab => hterm ab.1 ab.2
    _ = ∫⁻ x, ∑' ab : A × B, {x | R x ab.1 ab.2}.indicator
        (fun x => ε * f x ab.2) x ∂ρ := by
      rw [lintegral_tsum]
      intro ab
      exact ((measurable_const.mul (hf ab.2)).indicator (hRm ab.1 ab.2)).aemeasurable
    _ ≤ ∫⁻ x, ε * D * ∑' b, f x b ∂ρ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
      calc
        (∑' b, ∑' a, {x | R x a b}.indicator (fun x => ε * f x b) x) =
            ∑' b, (∑' a, if R x a b then (1 : ℝ≥0∞) else 0) * (ε * f x b) := by
          apply tsum_congr
          intro b
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro a
          by_cases ha : R x a b <;> simp [ha]
        _ ≤ ∑' b, D * (ε * f x b) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul' (hD x b) le_rfl
        _ = ε * D * ∑' b, f x b := by
          simp_rw [← mul_assoc, mul_comm D ε]
          exact ENNReal.tsum_mul_left
    _ = ε * D * ∫⁻ x, ∑' b, f x b ∂ρ :=
      lintegral_const_mul _ (Measurable.tsum hf)

open Classical in
/-- Finite families of selected laws can be compared simultaneously. The bound
counts compatible pairs consisting of a family index and a fine counting label. -/
theorem family_compatible_density_lower_tail
    {Ω Z I A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [Countable A] [Countable B]
    (μ : I → Measure Ω) (ρ : Measure Z) (z : I → Ω → Z)
    (fine : I → Ω → A) (coarse : I → Ω → B)
    (g : I → Z → A → ℝ≥0∞) (f : Z → B → ℝ≥0∞)
    (hg : ∀ i a, Measurable (fun x => g i x a))
    (hf : ∀ b, Measurable (fun x => f x b))
    (hslice : ∀ i a S, MeasurableSet S →
      μ i {p | fine i p = a ∧ z i p ∈ S} = ∫⁻ x in S, g i x a ∂ρ)
    (R : Z → I × A → B → Prop) (hRm : ∀ ia b, MeasurableSet {x | R x ia b})
    (hR : ∀ i, ∀ᵐ p ∂μ i, R (z i p) (i, fine i p) (coarse i p))
    (D : ℝ≥0∞) (hD : ∀ x b, ∑' ia, (if R x ia b then (1 : ℝ≥0∞) else 0) ≤ D)
    (ε : ℝ≥0∞) :
    (∑ i, μ i {p | g i (z i p) (fine i p) < ε * f (z i p) (coarse i p)}) ≤
      ε * D * ∫⁻ x, ∑' b, f x b ∂ρ := by
  classical
  let ν : Measure (I × Ω) := Measure.sum (fun i => (μ i).map (Prod.mk i))
  have hν (S : Set (I × Ω)) : ν S = ∑ i, μ i {p | (i, p) ∈ S} := by
    simp only [ν, Measure.sum_apply_of_countable, tsum_fintype]
    congr 1
    funext i
    exact (measurableEmbedding_prodMk_left i).map_apply (μ i) S
  have hslice' (ia : I × A) (S : Set Z) (hS : MeasurableSet S) :
      ν {p | (p.1, fine p.1 p.2) = ia ∧ z p.1 p.2 ∈ S} =
        ∫⁻ x in S, g ia.1 x ia.2 ∂ρ := by
    rw [hν]
    simp only [Set.mem_ofPred_eq, Prod.ext_iff]
    have heq (i : I) :
        μ i {p | (i = ia.1 ∧ fine i p = ia.2) ∧ z i p ∈ S} =
          if i = ia.1 then μ ia.1 {p | fine ia.1 p = ia.2 ∧ z ia.1 p ∈ S} else 0 := by
      by_cases hi : i = ia.1
      · subst i
        simp
      · simp [hi]
    simp_rw [heq]
    simpa using hslice ia.1 ia.2 S hS
  have hR' : ∀ᵐ p ∂ν, R (z p.1 p.2) (p.1, fine p.1 p.2) (coarse p.1 p.2) := by
    change ∀ᵐ p ∂Measure.sum (fun i => (μ i).map (Prod.mk i)), _
    rw [Measure.ae_sum_iff]
    intro i
    rw [ae_iff, (measurableEmbedding_prodMk_left i).map_apply]
    exact (ae_iff.mp (hR i))
  have h := compatible_density_lower_tail ν ρ (fun p => z p.1 p.2)
    (fun p => (p.1, fine p.1 p.2)) (fun p => coarse p.1 p.2)
    (fun x ia => g ia.1 x ia.2) f (fun ia => hg ia.1 ia.2) hf
    hslice' R hRm hR' D hD ε
  simpa only [hν, Set.mem_ofPred_eq] using h

open Classical in
/-- A finite parent list and the two possible shifts of each hidden bin give
an exceptional-mass bound with twice the list cardinality. -/
theorem listed_shift_density_lower_tail
    {Ω Z I : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : I → Measure Ω) (ρ : Measure Z) (z : I → Ω → Z)
    (fine coarse : I → Ω → ℤ)
    (g : I → Z → ℤ → ℝ≥0∞) (f : Z → ℤ → ℝ≥0∞)
    (hg : ∀ i a, Measurable (fun x => g i x a))
    (hf : ∀ b, Measurable (fun x => f x b))
    (hslice : ∀ i a S, MeasurableSet S →
      μ i {p | fine i p = a ∧ z i p ∈ S} = ∫⁻ x in S, g i x a ∂ρ)
    (Λ : Z × ℤ → Finset I)
    (hΛ : ∀ i, MeasurableSet {p | i ∈ Λ p})
    (hlist : ∀ i, ∀ᵐ p ∂μ i, i ∈ Λ (z i p, coarse i p))
    (shift : I → Z → ℤ) (hshift : ∀ i, Measurable (shift i))
    (hbins : ∀ i, ∀ᵐ p ∂μ i,
      fine i p = coarse i p + shift i (z i p) ∨
        fine i p = coarse i p + shift i (z i p) + 1)
    (D : ℝ≥0∞) (hcard : ∀ p, ((Λ p).card : ℝ≥0∞) ≤ D) (ε : ℝ≥0∞) :
    (∑ i, μ i {p | g i (z i p) (fine i p) < ε * f (z i p) (coarse i p)}) ≤
      ε * (2 * D) * ∫⁻ x, ∑' b, f x b ∂ρ := by
  classical
  let R : Z → I × ℤ → ℤ → Prop := fun x ia b =>
    ia.1 ∈ Λ (x, b) ∧ (ia.2 = b + shift ia.1 x ∨ ia.2 = b + shift ia.1 x + 1)
  letI (x : Z) (ia : I × ℤ) (b : ℤ) : Decidable (R x ia b) := Classical.propDecidable _
  have hRm (ia : I × ℤ) (b : ℤ) : MeasurableSet {x | R x ia b} := by
    exact ((hΛ ia.1).preimage (measurable_id.prodMk measurable_const)).inter
      ((measurableSet_eq_fun measurable_const (measurable_const.add (hshift ia.1))).union
        (measurableSet_eq_fun measurable_const ((measurable_const.add (hshift ia.1)).add_const 1)))
  have hR (i : I) : ∀ᵐ p ∂μ i, R (z i p) (i, fine i p) (coarse i p) := by
    filter_upwards [hlist i, hbins i] with p hp hb
    exact ⟨hp, hb⟩
  have hD (x : Z) (b : ℤ) :
      (∑' ia : I × ℤ, if R x ia b then (1 : ℝ≥0∞) else 0) ≤ 2 * D := by
    rw [ENNReal.tsum_prod', tsum_fintype]
    have hi (i : I) : (∑' a : ℤ, if R x (i, a) b then (1 : ℝ≥0∞) else 0) ≤
        if i ∈ Λ (x, b) then 2 else 0 := by
      by_cases hmem : i ∈ Λ (x, b)
      · rw [ite_eq_left hmem]
        calc
          _ ≤ (({b + shift i x, b + shift i x + 1} : Finset ℤ).card : ℝ≥0∞) :=
            k4_scalar_grid_density_extension.tsum_ite_one_le_card
              (fun a => R x (i, a) b) _ (by
              intro a ha
              simpa only [Finset.mem_insert, Finset.mem_singleton] using ha.2)
          _ ≤ 2 := by
            exact_mod_cast (Finset.card_le_two : ({b + shift i x, b + shift i x + 1} : Finset ℤ).card ≤ 2)
      · simp [R, hmem]
    calc
      _ ≤ ∑ i, if i ∈ Λ (x, b) then (2 : ℝ≥0∞) else 0 :=
        Finset.sum_le_sum fun i _ => hi i
      _ = 2 * ((Λ (x, b)).card : ℝ≥0∞) := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ ≤ 2 * D := mul_le_mul' le_rfl (hcard (x, b))
  exact family_compatible_density_lower_tail μ ρ z fine coarse g f hg hf hslice
    R hRm hR (2 * D) hD ε

end Submission.Obl.k4_scalar_true_terminal_lifting
