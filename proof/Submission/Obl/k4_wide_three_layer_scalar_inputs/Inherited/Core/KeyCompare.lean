/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Core/KeyCompare.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchGML2D

/-!
# Layer comparison inside one chart key

The pieces of two layers of the three-layer datum with the same chart key (velocity bin,
intercept bin and `b₁`-bin) carry normalized sheets `F₁ i`, `F₂ j` (two-variable quadratics in
time and the strip coordinate `η = eta(b₁)`).  The pair law of a trajectory in `C₁ i ∩ C₂ j` at
its strip coordinate is fed to `gml2D`: interval ceilings and jet counts are hypotheses here
(they come from the joint caps and the layer floors), closeness comes from the two fits.
Pairs whose sheets differ by `Mst` in some coefficient carry little mass.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchCor
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The good strip coordinates of a pair of sheets. -/
def closeSet (F₁ F₂ : Fin 6 → ℝ) (δ : ℝ) : Set ℝ :=
  Icc (1 / 4 : ℝ) (3 / 4) ∩ ⋂ t ∈ Icc (0 : ℝ) 1, {y | |quad2 F₁ t y - quad2 F₂ t y| ≤ δ}

theorem continuous_quad2_right (F : Fin 6 → ℝ) (t : ℝ) : Continuous (quad2 F t) := by
  unfold quad2; fun_prop

theorem isClosed_closeSet (F₁ F₂ : Fin 6 → ℝ) (δ : ℝ) : IsClosed (closeSet F₁ F₂ δ) := by
  apply isClosed_Icc.inter
  apply isClosed_biInter
  intro t _
  exact isClosed_le ((continuous_quad2_right F₁ t).sub (continuous_quad2_right F₂ t)).abs
    continuous_const

/-- **Comparison of two layers in one key.** -/
theorem key_compare (hM : MatchHyp) {dg : ℝ} (hd0 : 0 ≤ dg) (hd1 : dg < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (b : α → Fin 6 → ℝ), Measurable b →
    ∀ {n₁ n₂ : ℕ} (C₁ : Fin n₁ → Set α) (C₂ : Fin n₂ → Set α)
      (key₁ : Fin n₁ → Fin 3 → ℤ) (key₂ : Fin n₂ → Fin 3 → ℤ) (κ : Fin 3 → ℤ)
      (F₁ : Fin n₁ → Fin 6 → ℝ) (F₂ : Fin n₂ → Fin 6 → ℝ) (T₁ : Fin n₁ → ℝ) (T₂ : Fin n₂ → ℝ)
      (eta : ℝ → ℝ) (δ Mst A B w : ℝ),
      Measurable eta →
      (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
      (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
      (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
      0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
      0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
      (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
      (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
      (∀ i, key₁ i = κ → ∀ x : ℝ,
        ρs ((C₁ i ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) ≤ ENNReal.ofReal (A * T₁ i * w)) →
      (∀ j, key₂ j = κ → ∀ x : ℝ,
        ρs ((C₂ j ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) ≤ ENNReal.ofReal (A * T₂ j * w)) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => key₁ i = κ ∧ ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤
          A * (M / δ) ^ dg) →
      (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun j => key₂ j = κ ∧ ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤
          A * (M / δ) ^ dg) →
      (∀ i j, key₁ i = κ → key₂ j = κ →
        ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → eta (b p.1 1) ∈ closeSet (F₁ i) (F₂ j) δ) →
      (∑ i ∈ Finset.univ.filter (fun i => key₁ i = κ),
        ∑ j ∈ Finset.univ.filter (fun j => key₂ j = κ ∧ ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
          ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
          (∑ i ∈ Finset.univ.filter (fun i => key₁ i = κ), T₁ i +
            ∑ j ∈ Finset.univ.filter (fun j => key₂ j = κ), T₂ j)) := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := gml2D hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro ρs _ b hb n₁ n₂ C₁ C₂ key₁ key₂ κ F₁ F₂ T₁ T₂ eta δ Mst A B w heta hC₁ hC₂ hdisj₂
    hdisj₁ hδ hMst hA1 hA hw hw4 hwδ hT₁ hT₂ hB₁ hB₂ hI₁ hI₂ hJ₁ hJ₂ hclose
  classical
  -- index types of the key
  let ι₁ := {i : Fin n₁ // key₁ i = κ}
  let ι₂ := {j : Fin n₂ // key₂ j = κ}
  -- the pair law
  let f : ι₁ × ι₂ → α × ℝ → (ι₁ × ι₂) × ℝ := fun ij p => (ij, eta (b p.1 1))
  have hf : ∀ ij, Measurable (f ij) := fun ij =>
    measurable_const.prodMk (heta.comp ((measurable_pi_apply 1).comp (hb.comp measurable_fst)))
  let comp : ι₁ × ι₂ → Measure ((ι₁ × ι₂) × ℝ) := fun ij =>
    Measure.map (f ij) (ρs.restrict ((C₁ ij.1.1 ∩ C₂ ij.2.1) ×ˢ univ))
  let P : Measure ((ι₁ × ι₂) × ℝ) := Measure.sum comp
  have hcomp_apply : ∀ ij (S : Set ((ι₁ × ι₂) × ℝ)), MeasurableSet S →
      comp ij S = ρs (((C₁ ij.1.1 ∩ C₂ ij.2.1) ×ˢ univ) ∩ f ij ⁻¹' S) := by
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
  -- the bad mass of the key is the `P`-mass of the bad pairs
  let bad : Set ((ι₁ × ι₂) × ℝ) :=
    {p | ∃ k, Mst ≤ |F₁ p.1.1.1 k - F₂ p.1.2.1 k|}
  have hbadm : MeasurableSet bad := by
    have : bad = Prod.fst ⁻¹' {ij : ι₁ × ι₂ | ∃ k, Mst ≤ |F₁ ij.1.1 k - F₂ ij.2.1 k|} := rfl
    rw [this]
    exact measurable_fst (Set.Finite.measurableSet (Set.toFinite _))
  have hcomp_bad : ∀ ij : ι₁ × ι₂, comp ij bad =
      if (∃ k, Mst ≤ |F₁ ij.1.1 k - F₂ ij.2.1 k|) then ρs ((C₁ ij.1.1 ∩ C₂ ij.2.1) ×ˢ univ)
      else 0 := by
    intro ij
    rw [hcomp_apply ij bad hbadm]
    by_cases hq : ∃ k, Mst ≤ |F₁ ij.1.1 k - F₂ ij.2.1 k|
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
  have hlhs : (∑ i ∈ Finset.univ.filter (fun i => key₁ i = κ),
        ∑ j ∈ Finset.univ.filter (fun j => key₂ j = κ ∧ ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
          ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) = P bad := by
    rw [hP_apply bad hbadm, Fintype.sum_prod_type]
    simp_rw [hcomp_bad]
    rw [Finset.sum_subtype (Finset.univ.filter (fun i => key₁ i = κ)) (p := fun i => key₁ i = κ)
      (fun i => by simp)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.filter_filter, Finset.sum_filter]
    rw [Finset.sum_subtype (Finset.univ.filter (fun j => key₂ j = κ)) (p := fun j => key₂ j = κ)
      (fun j => by simp)]
  -- disjoint unions inside one piece
  have hsum_le₁ : ∀ (i : Fin n₁) (E : Set α), MeasurableSet E →
      (∑ j : ι₂, ρs ((C₁ i ∩ C₂ j.1 ∩ E) ×ˢ (univ : Set ℝ))) ≤ ρs ((C₁ i ∩ E) ×ˢ univ) := by
    intro i E hE
    have hpd : Pairwise (Function.onFun Disjoint
        (fun j : ι₂ => (C₁ i ∩ C₂ j.1 ∩ E) ×ˢ (univ : Set ℝ))) := by
      intro j j' hjj'
      have hd := hdisj₂ j.1 j'.1 (fun h => hjj' (Subtype.ext h))
      exact Set.disjoint_prod.mpr (Or.inl (hd.mono (fun l hl => hl.1.2) (fun l hl => hl.1.2)))
    have hU := measure_iUnion (μ := ρs) hpd
      (fun j => (((hC₁ i).inter (hC₂ j.1)).inter hE).prod MeasurableSet.univ)
    rw [tsum_fintype] at hU
    rw [← hU]
    apply measure_mono
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    exact ⟨⟨hj.1.1.1, hj.1.2⟩, trivial⟩
  have hsum_le₂ : ∀ (j : Fin n₂) (E : Set α), MeasurableSet E →
      (∑ i : ι₁, ρs ((C₁ i.1 ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) ≤ ρs ((C₂ j ∩ E) ×ˢ univ) := by
    intro j E hE
    have hpd : Pairwise (Function.onFun Disjoint
        (fun i : ι₁ => (C₁ i.1 ∩ C₂ j ∩ E) ×ˢ (univ : Set ℝ))) := by
      intro i i' hii'
      have hd := hdisj₁ i.1 i'.1 (fun h => hii' (Subtype.ext h))
      exact Set.disjoint_prod.mpr (Or.inl (hd.mono (fun l hl => hl.1.1) (fun l hl => hl.1.1)))
    have hU := measure_iUnion (μ := ρs) hpd
      (fun i => (((hC₁ i.1).inter (hC₂ j)).inter hE).prod MeasurableSet.univ)
    rw [tsum_fintype] at hU
    rw [← hU]
    apply measure_mono
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨⟨hi.1.1.2, hi.1.2⟩, trivial⟩
  have hetaS : ∀ x : ℝ, MeasurableSet {l : α | eta (b l 1) ∈ Icc (x - w) x} := fun x =>
    (heta.comp ((measurable_pi_apply 1).comp hb)) measurableSet_Icc
  -- interval ceilings of the pair law
  have hIP₁ : ∀ (i : ι₁) (x : ℝ), P {p | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x} ≤
      ENNReal.ofReal (A * T₁ i.1 * w) := by
    intro i x
    have hS : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x} :=
      (measurable_fst.fst (measurableSet_singleton i)).inter (measurable_snd measurableSet_Icc)
    rw [hP_apply _ hS, Fintype.sum_prod_type]
    calc ∑ i' : ι₁, ∑ j : ι₂, comp (i', j) {p | p.1.1 = i ∧ p.2 ∈ Icc (x - w) x}
        = ∑ j : ι₂, ρs ((C₁ i.1 ∩ C₂ j.1 ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) := by
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
      _ ≤ ρs ((C₁ i.1 ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) := hsum_le₁ i.1 _ (hetaS x)
      _ ≤ _ := hI₁ i.1 i.2 x
  have hIP₂ : ∀ (j : ι₂) (x : ℝ), P {p | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x} ≤
      ENNReal.ofReal (A * T₂ j.1 * w) := by
    intro j x
    have hS : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x} :=
      (measurable_fst.snd (measurableSet_singleton j)).inter (measurable_snd measurableSet_Icc)
    rw [hP_apply _ hS, Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ j' : ι₂, ∑ i : ι₁, comp (i, j') {p | p.1.2 = j ∧ p.2 ∈ Icc (x - w) x}
        = ∑ i : ι₁, ρs ((C₁ i.1 ∩ C₂ j.1 ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) := by
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
      _ ≤ ρs ((C₂ j.1 ∩ {l | eta (b l 1) ∈ Icc (x - w) x}) ×ˢ univ) := hsum_le₂ j.1 _ (hetaS x)
      _ ≤ _ := hI₂ j.1 j.2 x
  -- jet counts on the key
  have hJP₁ : ∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
      ((Finset.univ.filter (fun i : ι₁ => ∀ k, |F₁ i.1 k - r k| ≤ M)).card : ℝ) ≤
        A * (M / δ) ^ dg := by
    intro r M hM
    refine le_trans ?_ (hJ₁ r M hM)
    exact_mod_cast Finset.card_le_card_of_injOn Subtype.val
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at hi ⊢
        exact ⟨i.2, hi⟩)
      (fun i _ i' _ h => Subtype.ext h)
  have hJP₂ : ∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
      ((Finset.univ.filter (fun j : ι₂ => ∀ k, |F₂ j.1 k - r k| ≤ M)).card : ℝ) ≤
        A * (M / δ) ^ dg := by
    intro r M hM
    refine le_trans ?_ (hJ₂ r M hM)
    exact_mod_cast Finset.card_le_card_of_injOn Subtype.val
      (fun j hj => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at hj ⊢
        exact ⟨j.2, hj⟩)
      (fun j _ j' _ h => Subtype.ext h)
  -- closeness almost everywhere
  have hcloseP : ∀ᵐ p ∂P, p.2 ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |quad2 (F₁ p.1.1.1) t p.2 - quad2 (F₂ p.1.2.1) t p.2| ≤ δ := by
    have hgood : MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.2 ∈ closeSet (F₁ p.1.1.1) (F₂ p.1.2.1) δ} := by
      have : {p : (ι₁ × ι₂) × ℝ | p.2 ∈ closeSet (F₁ p.1.1.1) (F₂ p.1.2.1) δ} =
          ⋃ ij : ι₁ × ι₂, (Prod.fst ⁻¹' {ij} ∩ Prod.snd ⁻¹' closeSet (F₁ ij.1.1) (F₂ ij.2.1) δ) := by
        ext p
        simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨fun h => ⟨p.1, rfl, h⟩, fun ⟨ij, hij, h⟩ => hij ▸ h⟩
      rw [this]
      exact MeasurableSet.iUnion fun ij => (measurable_fst (measurableSet_singleton ij)).inter
        (measurable_snd (isClosed_closeSet _ _ _).measurableSet)
    have hae : ∀ᵐ p ∂P, p.2 ∈ closeSet (F₁ p.1.1.1) (F₂ p.1.2.1) δ := by
      simp only [P]
      rw [Measure.ae_sum_iff]
      intro ij
      simp only [comp]
      rw [ae_map_iff (hf ij).aemeasurable hgood]
      have hS : MeasurableSet ((C₁ ij.1.1 ∩ C₂ ij.2.1) ×ˢ (univ : Set ℝ)) :=
        ((hC₁ _).inter (hC₂ _)).prod MeasurableSet.univ
      rw [ae_restrict_iff' hS]
      filter_upwards [hclose ij.1.1 ij.2.1 ij.1.2 ij.2.2] with p hp hpS
      exact hp hpS.1.1 hpS.1.2
    filter_upwards [hae] with p hp
    refine ⟨hp.1, fun t ht => ?_⟩
    have := mem_iInter₂.mp hp.2 t ht
    exact this
  have hmain := H ι₁ ι₂ (fun i => F₁ i.1) (fun j => F₂ j.1) (fun i => T₁ i.1) (fun j => T₂ j.1)
    P δ Mst A B w hδ hMst hA1 hA hw hw4 hwδ (fun i => hT₁ i.1) (fun j => hT₂ j.1)
    (fun i k => hB₁ i.1 k) (fun j k => hB₂ j.1 k) hIP₁ hIP₂ hJP₁ hJP₂ hcloseP
  rw [hlhs]
  refine hmain.trans (le_of_eq ?_)
  congr 2
  rw [Finset.sum_subtype (Finset.univ.filter (fun i => key₁ i = κ)) (p := fun i => key₁ i = κ)
      (fun i => by simp) T₁,
    Finset.sum_subtype (Finset.univ.filter (fun j => key₂ j = κ)) (p := fun j => key₂ j = κ)
      (fun j => by simp) T₂]

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
