-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.MeasureSampling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.Sampling
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Holder

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped Classical ENNReal

/-- Measurable sampling reduction. If every rich point has a complete bipartite
incidence rectangle, bounds for unions over small sampled subfamilies bound its measure.
The rich set itself need not be measurable. -/
theorem measure_rich_le_of_sample_unions {α β X : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [MeasurableSpace X]
    (ν : Measure X) (R : α → β → Set X) (hR : ∀ a b, MeasurableSet (R a b))
    (E : Set X) (k l : ℕ) (V : ℝ)
    (hrich : ∀ p ∈ E, ∃ (F : Finset α) (G : Finset β),
      Fintype.card α ≤ k * F.card ∧ Fintype.card β ≤ l * G.card ∧
      ∀ a ∈ F, ∀ b ∈ G, p ∈ R a b)
    (hbound : ∀ (F : Finset α) (G : Finset β), F.card ≤ k → G.card ≤ l →
      ν (⋃ a ∈ F, ⋃ b ∈ G, R a b) ≤ ENNReal.ofReal V) :
    ν E ≤ ENNReal.ofReal (4 * V) := by
  classical
  let Ω := (Fin k → α) × (Fin l → β)
  let U : Ω → Set X := fun w => ⋃ s, ⋃ t, R (w.1 s) (w.2 t)
  have hU (w : Ω) : MeasurableSet (U w) :=
    MeasurableSet.iUnion (fun s => MeasurableSet.iUnion (fun t => hR _ _))
  let f : X → ℝ≥0∞ := fun p => ∑ w : Ω, (U w).indicator (fun _ => 1) p
  have hf : Measurable f :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.measurable_multiplicity hU
  have hNU : ∀ w : Ω, ν (U w) ≤ ENNReal.ofReal V := by
    intro w
    have hb := hbound (Finset.univ.image w.1) (Finset.univ.image w.2)
      (by simpa using Finset.card_image_le (f := w.1) (s := Finset.univ))
      (by simpa using Finset.card_image_le (f := w.2) (s := Finset.univ))
    have he : (⋃ a ∈ Finset.univ.image w.1, ⋃ b ∈ Finset.univ.image w.2, R a b) = U w := by
      ext p
      simp [U]
    rwa [he] at hb
  have hlow : E ⊆ {p | ENNReal.ofReal ((Fintype.card Ω : ℝ) / 4) ≤ f p} := by
    intro p hp
    obtain ⟨F, G, hF, hG, hFG⟩ := hrich p hp
    have hh := quarter_samples_hit_both (fun a => a ∈ F) (fun b => b ∈ G) k l
      (by simpa using hF) (by simpa using hG)
    have hc : Fintype.card {w : Ω // (∃ s, w.1 s ∈ F) ∧ (∃ t, w.2 t ∈ G)} ≤
        Fintype.card {w : Ω // p ∈ U w} := by
      apply Fintype.card_subtype_mono
      intro w hw
      obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hw
      exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨t, hFG _ hs _ ht⟩⟩
    have hr : (Fintype.card Ω : ℝ) / 4 ≤ Fintype.card {w : Ω // p ∈ U w} := by
      simp only [← Nat.card_eq_fintype_card] at hh hc ⊢
      exact hh.trans (Nat.cast_le.mpr hc)
    have he : f p = (Fintype.card {w : Ω // p ∈ U w} : ℝ≥0∞) := by
      simp [f, Set.indicator_apply, Fintype.card_subtype]
    change ENNReal.ofReal ((Fintype.card Ω : ℝ) / 4) ≤ f p
    rw [he]
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hr
  have hint : (∫⁻ p, f p ∂ν) ≤ ENNReal.ofReal ((Fintype.card Ω : ℝ) * V) := by
    calc
      _ = ∑ w : Ω, ν (U w) :=
        WangZahlLot.Obl.wz_normalized_projection_coarse_fine.lintegral_multiplicity hU ν
      _ ≤ ∑ _w : Ω, ENNReal.ofReal V := Finset.sum_le_sum (fun w _ => hNU w)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card Ω)), ENNReal.ofReal_natCast]
  have hN : 0 < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hN4 : 0 < (Fintype.card Ω : ℝ) / 4 := by positivity
  calc
    ν E ≤ ν {p | ENNReal.ofReal ((Fintype.card Ω : ℝ) / 4) ≤ f p} := measure_mono hlow
    _ ≤ (∫⁻ p, f p ∂ν) / ENNReal.ofReal ((Fintype.card Ω : ℝ) / 4) :=
      meas_ge_le_lintegral_div hf.aemeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hN4)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((Fintype.card Ω : ℝ) * V) /
        ENNReal.ofReal ((Fintype.card Ω : ℝ) / 4) :=
      ENNReal.div_le_div_right hint _
    _ = ENNReal.ofReal (4 * V) := by
      rw [← ENNReal.ofReal_div_of_pos hN4]
      congr 1
      field_simp

/-- The reciprocal-density sample lengths used in the measurable sampling reduction. -/
theorem measure_rich_le_of_ceil_sample_unions {α β X : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] [MeasurableSpace X]
    (ν : Measure X) (R : α → β → Set X) (hR : ∀ a b, MeasurableSet (R a b))
    (E : Set X) {μ : ℝ} (hμ : 0 < μ) (V : ℝ)
    (hrich : ∀ p ∈ E, ∃ (F : Finset α) (G : Finset β),
      μ ≤ (F.card : ℝ) ∧ μ ≤ (G.card : ℝ) ∧ ∀ a ∈ F, ∀ b ∈ G, p ∈ R a b)
    (hbound : ∀ (F : Finset α) (G : Finset β),
      F.card ≤ ⌈(Fintype.card α : ℝ) / μ⌉₊ →
      G.card ≤ ⌈(Fintype.card β : ℝ) / μ⌉₊ →
      ν (⋃ a ∈ F, ⋃ b ∈ G, R a b) ≤ ENNReal.ofReal V) :
    ν E ≤ ENNReal.ofReal (4 * V) := by
  apply measure_rich_le_of_sample_unions ν R hR E
    ⌈(Fintype.card α : ℝ) / μ⌉₊ ⌈(Fintype.card β : ℝ) / μ⌉₊ V _ hbound
  intro p hp
  obtain ⟨F, G, hF, hG, hFG⟩ := hrich p hp
  refine ⟨F, G, ?_, ?_, hFG⟩
  · have hc : (Fintype.card α : ℝ) ≤ (⌈(Fintype.card α : ℝ) / μ⌉₊ : ℝ) * μ :=
      (div_le_iff₀ hμ).mp (Nat.le_ceil _)
    have hb := hc.trans (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg _))
    exact_mod_cast hb
  · have hc : (Fintype.card β : ℝ) ≤ (⌈(Fintype.card β : ℝ) / μ⌉₊ : ℝ) * μ :=
      (div_le_iff₀ hμ).mp (Nat.le_ceil _)
    have hb := hc.trans (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _))
    exact_mod_cast hb

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
