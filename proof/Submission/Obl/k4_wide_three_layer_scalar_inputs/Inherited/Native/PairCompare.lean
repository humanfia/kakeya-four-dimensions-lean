/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/PairCompare.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.KeyCompare

/-!
# Two-colour comparison of label families on one domain

`Core.key_compare` with the key filter removed and a general label coordinate: two finite
families of label sets `C₁ i`, `C₂ j` (disjoint within each colour), each index with a
normalized quadratic graph over (time, `y`) where `y = yf l` is a measurable coordinate of the
label.  On the pair law of a finite event measure, pairs whose graphs agree along the whole time
interval at the label's `y` cannot carry much mass unless their coefficient vectors are within
`Mst`.  This is the matching step used for the short domains (true blocks against coarse
projected pieces).
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchCor
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- **Comparison of two label families on one domain.** -/
theorem pair_compare (hM : MatchHyp) {dg : ℝ} (hd0 : 0 ≤ dg) (hd1 : dg < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (yf : α → ℝ), Measurable yf →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
      (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α)
      (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
      (δ Mst A B w : ℝ),
      (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
      (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
      (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
      (∀ i (x : ℝ), ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
        ENNReal.ofReal (A * T₁ i * w)) →
      (∀ j (x : ℝ), ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
        ENNReal.ofReal (A * T₂ j * w)) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ dg) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ dg) →
      (∀ i j, ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → yf p.1 ∈ closeSet (F₁ i) (F₂ j) δ) →
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
          ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j)) := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := gml2D hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro ρs _ yf hyf ι₁ ι₂ _ _ _ _ C₁ C₂ F₁ F₂ T₁ T₂ δ Mst A B w hC₁ hC₂ hdisj₂ hdisj₁ hδ hMst
    hA1 hA hw hw4 hwδ hT₁ hT₂ hB₁ hB₂ hI₁ hI₂ hJ₁ hJ₂ hclose
  classical
  letI : MeasurableSpace ι₁ := ⊤
  letI : MeasurableSpace ι₂ := ⊤
  haveI : DiscreteMeasurableSpace ι₁ := ⟨fun _ => trivial⟩
  haveI : DiscreteMeasurableSpace ι₂ := ⟨fun _ => trivial⟩
  let f : ι₁ × ι₂ → α × ℝ → (ι₁ × ι₂) × ℝ := fun ij p => (ij, yf p.1)
  have hf : ∀ ij, Measurable (f ij) := fun ij =>
    measurable_const.prodMk (hyf.comp measurable_fst)
  let comp : ι₁ × ι₂ → Measure ((ι₁ × ι₂) × ℝ) := fun ij =>
    Measure.map (f ij) (ρs.restrict ((C₁ ij.1 ∩ C₂ ij.2) ×ˢ univ))
  let P : Measure ((ι₁ × ι₂) × ℝ) := Measure.sum comp
  have hcomp_apply : ∀ ij (S : Set ((ι₁ × ι₂) × ℝ)), MeasurableSet S →
      comp ij S = ρs (((C₁ ij.1 ∩ C₂ ij.2) ×ˢ univ) ∩ f ij ⁻¹' S) := by
    intro ij S hS
    simp only [comp]
    rw [Measure.map_apply (hf ij) hS, Measure.restrict_apply ((hf ij) hS), inter_comm]
  have hP_apply : ∀ S, MeasurableSet S → P S = ∑ ij, comp ij S := by
    intro S hS
    simp only [P]
    rw [Measure.sum_apply _ hS, tsum_fintype]
  have hPfin : IsFiniteMeasure P := by
    constructor
    rw [hP_apply univ MeasurableSet.univ]
    exact ENNReal.sum_lt_top.mpr fun ij _ => by
      rw [hcomp_apply ij univ MeasurableSet.univ]
      exact measure_lt_top _ _
  let bad : Set ((ι₁ × ι₂) × ℝ) :=
    {p | ∃ k, Mst ≤ |F₁ p.1.1 k - F₂ p.1.2 k|}
  have hbadm : MeasurableSet bad := by
    have : bad = Prod.fst ⁻¹' {ij : ι₁ × ι₂ | ∃ k, Mst ≤ |F₁ ij.1 k - F₂ ij.2 k|} := rfl
    rw [this]
    exact measurable_fst (Set.Finite.measurableSet (Set.toFinite _))
  have hcomp_bad : ∀ ij : ι₁ × ι₂, comp ij bad =
      if (∃ k, Mst ≤ |F₁ ij.1 k - F₂ ij.2 k|) then ρs ((C₁ ij.1 ∩ C₂ ij.2) ×ˢ univ)
      else 0 := by
    intro ij
    rw [hcomp_apply ij bad hbadm]
    by_cases hq : ∃ k, Mst ≤ |F₁ ij.1 k - F₂ ij.2 k|
    · rw [if_pos hq]
      congr 1
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, hq⟩
    · rw [if_neg hq]
      convert measure_empty (μ := ρs)
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
      intro _ h
      exact hq h
  have hlhs : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
          ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) = P bad := by
    rw [hP_apply bad hbadm, Fintype.sum_prod_type]
    simp_rw [hcomp_bad]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_filter]
  have hsum_le₁ : ∀ (i : ι₁) (E : Set α), MeasurableSet E →
      (∑ j : ι₂, ρs ((C₁ i ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) ≤ ρs ((C₁ i ∩ E) ×ˢ univ) := by
    intro i E hE
    have hpd : Pairwise (Function.onFun Disjoint
        (fun j : ι₂ => (C₁ i ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) := by
      intro j j' hjj'
      have hd := hdisj₂ j j' hjj'
      exact Set.disjoint_prod.mpr (Or.inl (hd.mono (fun l hl => hl.1.2) (fun l hl => hl.1.2)))
    have hU := measure_iUnion (μ := ρs) hpd
      (fun j => (((hC₁ i).inter (hC₂ j)).inter hE).prod MeasurableSet.univ)
    rw [tsum_fintype] at hU
    rw [← hU]
    apply measure_mono
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact ⟨⟨hj.1.1.1, hj.1.2⟩, trivial⟩
  have hsum_le₂ : ∀ (j : ι₂) (E : Set α), MeasurableSet E →
      (∑ i : ι₁, ρs ((C₁ i ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) ≤ ρs ((C₂ j ∩ E) ×ˢ univ) := by
    intro j E hE
    have hpd : Pairwise (Function.onFun Disjoint
        (fun i : ι₁ => (C₁ i ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) := by
      intro i i' hii'
      have hd := hdisj₁ i i' hii'
      exact Set.disjoint_prod.mpr (Or.inl (hd.mono (fun l hl => hl.1.1) (fun l hl => hl.1.1)))
    have hU := measure_iUnion (μ := ρs) hpd
      (fun i => (((hC₁ i).inter (hC₂ j)).inter hE).prod MeasurableSet.univ)
    rw [tsum_fintype] at hU
    rw [← hU]
    apply measure_mono
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨⟨hi.1.1.2, hi.1.2⟩, trivial⟩
  have hetaS : ∀ x : ℝ, MeasurableSet {l : α | yf l ∈ Icc (x - w) x} := fun x =>
    hyf measurableSet_Icc
  have hIP₁ : ∀ (i : ι₁) (x : ℝ), P {p | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x} ≤
      ENNReal.ofReal (A * T₁ i * w) := by
    intro i x
    have hS : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x} :=
      (measurable_fst.fst (measurableSet_singleton i)).inter (measurable_snd measurableSet_Icc)
    rw [hP_apply _ hS, Fintype.sum_prod_type]
    calc ∑ i' : ι₁, ∑ j : ι₂, comp (i', j) {p | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x}
        = ∑ j : ι₂, ρs ((C₁ i ∩ C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) := by
          rw [Finset.sum_eq_single i]
          · apply Finset.sum_congr rfl
            intro j _
            rw [hcomp_apply _ _ hS]
            congr 1
            ext p
            simp [f]
          · intro i' _ hi'
            apply Finset.sum_eq_zero
            intro j _
            rw [hcomp_apply _ _ hS]
            convert measure_empty (μ := ρs)
            ext p
            simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, mem_empty_iff_false,
              iff_false, not_and, f]
            intro _ h
            exact absurd h hi'
          · intro h; exact absurd (Finset.mem_univ i) h
      _ ≤ ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) := hsum_le₁ i _ (hetaS x)
      _ ≤ _ := hI₁ i x
  have hIP₂ : ∀ (j : ι₂) (x : ℝ), P {p | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x} ≤
      ENNReal.ofReal (A * T₂ j * w) := by
    intro j x
    have hS : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x} :=
      (measurable_fst.snd (measurableSet_singleton j)).inter (measurable_snd measurableSet_Icc)
    rw [hP_apply _ hS, Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ j' : ι₂, ∑ i : ι₁, comp (i, j') {p | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x}
        = ∑ i : ι₁, ρs ((C₁ i ∩ C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) := by
          rw [Finset.sum_eq_single j]
          · apply Finset.sum_congr rfl
            intro i _
            rw [hcomp_apply _ _ hS]
            congr 1
            ext p
            simp [f]
          · intro j' _ hj'
            apply Finset.sum_eq_zero
            intro i _
            rw [hcomp_apply _ _ hS]
            convert measure_empty (μ := ρs)
            ext p
            simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, mem_empty_iff_false,
              iff_false, not_and, f]
            intro _ h
            exact absurd h hj'
          · intro h; exact absurd (Finset.mem_univ j) h
      _ ≤ ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) := hsum_le₂ j _ (hetaS x)
      _ ≤ _ := hI₂ j x
  have hcloseP : ∀ᵐ p ∂P, p.2 ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |quad2 (F₁ p.1.1) t p.2 - quad2 (F₂ p.1.2) t p.2| ≤ δ := by
    have hgood : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.2 ∈ closeSet (F₁ p.1.1) (F₂ p.1.2) δ} := by
      have : {p : (ι₁ × ι₂) × ℝ | p.2 ∈ closeSet (F₁ p.1.1) (F₂ p.1.2) δ} =
          ⋃ ij : ι₁ × ι₂, (Prod.fst ⁻¹' {ij} ∩ Prod.snd ⁻¹' closeSet (F₁ ij.1) (F₂ ij.2) δ) := by
        ext p
        simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h => ⟨p.1, rfl, h⟩, fun ⟨ij, hij, h⟩ => hij ▸ h⟩
      rw [this]
      exact MeasurableSet.iUnion fun ij => (measurable_fst (measurableSet_singleton ij)).inter
        (measurable_snd (isClosed_closeSet _ _ _).measurableSet)
    have hae : ∀ᵐ p ∂P, p.2 ∈ closeSet (F₁ p.1.1) (F₂ p.1.2) δ := by
      simp only [P]
      rw [Measure.ae_sum_iff]
      intro ij
      simp only [comp]
      rw [ae_map_iff (hf ij).aemeasurable hgood]
      have hS : MeasurableSet ((C₁ ij.1 ∩ C₂ ij.2) ×ˢ (univ : Set ℝ)) :=
        ((hC₁ _).inter (hC₂ _)).prod MeasurableSet.univ
      rw [ae_restrict_iff' hS]
      filter_upwards [hclose ij.1 ij.2] with p hp hpS
      exact hp hpS.1.1 hpS.1.2
    filter_upwards [hae] with p hp
    refine ⟨hp.1, fun t ht => ?_⟩
    have := mem_iInter₂.mp hp.2 t ht
    exact this
  have hmain := H ι₁ ι₂ F₁ F₂ T₁ T₂ P δ Mst A B w hδ hMst hA1 hA hw hw4 hwδ hT₁ hT₂
    hB₁ hB₂ hIP₁ hIP₂ hJ₁ hJ₂ hcloseP
  rw [hlhs]
  exact hmain

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
