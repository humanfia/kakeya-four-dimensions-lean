-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/TripleSelection.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Selection of one triple of velocity bins with qualified
witnesses on a substantial part of a finite state family (paper,
tex-06 §"Cartesian interpolation": conditional product sampling at each good
state, palette domination, and averaging over the product palette).

Each state `D` carries the law `ρ D` of the bins of its qualified witnesses.
If every state samples a good triple with probability `≥ c` and every bin law
is dominated by `Kr m_D π`, then one triple has witnesses in all three bins on
states of total mass `≥ c / Kr³` of the family. There is no loss in the number
of states or bins.
-/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]

/-- Measures of triples, as sums over singletons. -/
theorem prod3_apply_eq_tsum (ρ₀ ρ₁ ρ₂ : Measure β) [SigmaFinite ρ₁] [SigmaFinite ρ₂]
    (T : Set (β × β × β)) :
    (ρ₀.prod (ρ₁.prod ρ₂)) T =
      ∑' t : β × β × β, T.indicator (fun t => ρ₀ {t.1} * (ρ₁ {t.2.1} * ρ₂ {t.2.2})) t := by
  have hT : MeasurableSet T := (Set.to_countable T).measurableSet
  rw [← Measure.tsum_indicator_apply_singleton _ T hT]
  congr 1
  funext t
  by_cases ht : t ∈ T
  · rw [indicator_of_mem ht, indicator_of_mem ht]
    have hsing : ({t} : Set (β × β × β)) = {t.1} ×ˢ ({t.2.1} ×ˢ {t.2.2}) := by
      ext x
      simp only [mem_singleton_iff, mem_prod, Prod.ext_iff]
    rw [hsing, Measure.prod_prod, Measure.prod_prod]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

/-- Domination of each factor at every bin dominates the product. -/
theorem prod3_le_of_le (ρ π : Measure β) [SigmaFinite ρ] [SigmaFinite π] (a : ℝ≥0∞)
    (h : ∀ b, ρ {b} ≤ a * π {b}) (T : Set (β × β × β)) :
    (ρ.prod (ρ.prod ρ)) T ≤ a ^ 3 * (π.prod (π.prod π)) T := by
  rw [prod3_apply_eq_tsum, prod3_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : t ∈ T
  · simp only [indicator_of_mem ht]
    calc ρ {t.1} * (ρ {t.2.1} * ρ {t.2.2}) ≤
        (a * π {t.1}) * ((a * π {t.2.1}) * (a * π {t.2.2})) := by
          gcongr <;> exact h _
      _ = a ^ 3 * (π {t.1} * (π {t.2.1} * π {t.2.2})) := by ring
  · simp only [indicator_of_notMem ht, mul_zero, le_refl]

/-- Triples meeting a null bin carry no product mass. -/
theorem prod3_eq_of_support (ρ : Measure β) [SigmaFinite ρ] (T : Set (β × β × β)) :
    (ρ.prod (ρ.prod ρ)) T =
      (ρ.prod (ρ.prod ρ)) (T ∩ {t | ρ {t.1} ≠ 0 ∧ ρ {t.2.1} ≠ 0 ∧ ρ {t.2.2} ≠ 0}) := by
  rw [prod3_apply_eq_tsum, prod3_apply_eq_tsum]
  congr 1
  funext t
  by_cases ht : t ∈ T
  · by_cases hs : ρ {t.1} ≠ 0 ∧ ρ {t.2.1} ≠ 0 ∧ ρ {t.2.2} ≠ 0
    · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ T ∩ {t | ρ {t.1} ≠ 0 ∧
        ρ {t.2.1} ≠ 0 ∧ ρ {t.2.2} ≠ 0} from ⟨ht, hs⟩)]
    · rw [indicator_of_mem ht, indicator_of_notMem (fun h => hs h.2)]
      simp only [not_and_or, not_not] at hs
      rcases hs with h | h | h <;> simp [h]
  · rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht h.1)]

open Classical in
/-- **One common triple of bins.** -/
theorem exists_common_bin_triple {ι : Type*} (Fam : Finset ι) (m : ι → ℝ≥0∞)
    (hm : ∀ D ∈ Fam, m D ≠ ⊤) (ρ : ι → Measure β) [∀ D, SigmaFinite (ρ D)]
    (π : Measure β) [IsProbabilityMeasure π] (Kr : ℝ≥0∞) (hKr : Kr ≠ ⊤)
    (hdom : ∀ D ∈ Fam, ∀ b, ρ D {b} ≤ Kr * m D * π {b})
    (G : Set (β × β × β)) (c : ℝ≥0∞)
    (hspan : ∀ D ∈ Fam, c * m D ^ 3 ≤ ((ρ D).prod ((ρ D).prod (ρ D))) G) :
    ∃ t : β × β × β, c * ∑ D ∈ Fam, m D ≤
      Kr ^ 3 * ∑ D ∈ Fam.filter (fun D => t ∈ G ∧ ρ D {t.1} ≠ 0 ∧ ρ D {t.2.1} ≠ 0 ∧
        ρ D {t.2.2} ≠ 0), m D := by
  classical
  let P : Measure (β × β × β) := π.prod (π.prod π)
  haveI : IsProbabilityMeasure P := by
    simp only [P]; infer_instance
  let Tset : ι → Set (β × β × β) := fun D =>
    G ∩ {t | ρ D {t.1} ≠ 0 ∧ ρ D {t.2.1} ≠ 0 ∧ ρ D {t.2.2} ≠ 0}
  let f : β × β × β → ℝ≥0∞ := fun t => ∑ D ∈ Fam, (Tset D).indicator (fun _ => m D) t
  have hf (t : β × β × β) : f t = ∑ D ∈ Fam.filter (fun D => t ∈ Tset D), m D := by
    simp only [f, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D _
    by_cases ht : t ∈ Tset D
    · rw [indicator_of_mem ht, if_pos ht]
    · rw [indicator_of_notMem ht, if_neg ht]
  -- per state: `c m_D ≤ Kr³ m_D P(T_D)`
  have hstate : ∀ D ∈ Fam, c * m D ≤ Kr ^ 3 * (m D * P (Tset D)) := by
    intro D hD
    have h1 : c * m D ^ 3 ≤ (Kr * m D) ^ 3 * P (Tset D) := by
      calc c * m D ^ 3 ≤ ((ρ D).prod ((ρ D).prod (ρ D))) G := hspan D hD
        _ = ((ρ D).prod ((ρ D).prod (ρ D))) (Tset D) := prod3_eq_of_support (ρ D) G
        _ ≤ (Kr * m D) ^ 3 * P (Tset D) := prod3_le_of_le (ρ D) π (Kr * m D) (hdom D hD) _
    by_cases h0 : m D = 0
    · simp [h0]
    · have hmt : m D ^ 2 ≠ 0 := pow_ne_zero 2 h0
      have hmt' : m D ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (hm D hD)
      have h2 : m D ^ 2 * (c * m D) ≤ m D ^ 2 * (Kr ^ 3 * (m D * P (Tset D))) := by
        calc m D ^ 2 * (c * m D) = c * m D ^ 3 := by ring
          _ ≤ (Kr * m D) ^ 3 * P (Tset D) := h1
          _ = m D ^ 2 * (Kr ^ 3 * (m D * P (Tset D))) := by ring
      exact (ENNReal.mul_le_mul_iff_right hmt hmt').mp h2
  -- the integral of `f`
  have hint : ∫⁻ t, f t ∂P = ∑ D ∈ Fam, m D * P (Tset D) := by
    simp only [f]
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro D _
      rw [lintegral_indicator_const ((Set.to_countable _).measurableSet)]
    · intro D _
      exact measurable_const.indicator ((Set.to_countable _).measurableSet)
  -- `f` attains its maximum
  have hrange : (range f).Finite := by
    apply Set.Finite.subset ((Fam.powerset.image (fun s => ∑ D ∈ s, m D)).finite_toSet)
    rintro _ ⟨t, rfl⟩
    simp only [Finset.coe_image, Finset.coe_powerset, mem_image]
    exact ⟨Fam.filter (fun D => t ∈ Tset D), Finset.filter_subset _ _, (hf t).symm⟩
  have hne : (range f).Nonempty := by
    obtain ⟨b⟩ : Nonempty β := by
      by_contra hb
      rw [not_nonempty_iff] at hb
      have := measure_univ (μ := π)
      rw [univ_eq_empty_iff.mpr hb, measure_empty] at this
      exact zero_ne_one this
    exact ⟨f (b, b, b), ⟨(b, b, b), rfl⟩⟩
  obtain ⟨_, ⟨t₀, rfl⟩, hmax⟩ := Set.exists_max_image (range f) id hrange hne
  have hle : ∀ t, f t ≤ f t₀ := fun t => hmax (f t) ⟨t, rfl⟩
  refine ⟨t₀, ?_⟩
  have hmono : ∫⁻ t, f t ∂P ≤ f t₀ := by
    calc ∫⁻ t, f t ∂P ≤ ∫⁻ _, f t₀ ∂P := lintegral_mono hle
      _ = f t₀ := by rw [lintegral_const, measure_univ, mul_one]
  calc c * ∑ D ∈ Fam, m D = ∑ D ∈ Fam, c * m D := Finset.mul_sum _ _ _
    _ ≤ ∑ D ∈ Fam, Kr ^ 3 * (m D * P (Tset D)) := Finset.sum_le_sum hstate
    _ = Kr ^ 3 * ∫⁻ t, f t ∂P := by rw [hint, Finset.mul_sum]
    _ ≤ Kr ^ 3 * f t₀ := by gcongr
    _ = _ := by rw [hf]; rfl

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
