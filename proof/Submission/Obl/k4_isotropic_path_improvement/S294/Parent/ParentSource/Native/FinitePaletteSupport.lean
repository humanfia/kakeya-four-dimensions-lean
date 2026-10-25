-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FinitePaletteSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FinitePaletteSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FinitePaletteSupport.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FinitePaletteSupport.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/FinitePaletteSupport.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.ContinuousPaletteTransfer
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode

/-! Apply finite palette transfer to actual countable histories and integer
velocity bins whose ranges are finite only on the original full-mass support. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

/-- Reuse the accepted finite-record encoder, retaining the original component
values as the finite label types. Their decoders are then automatically injective. -/
theorem finite_support_component_codes {Ω E Z Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (f : Ω → E) (z : Ω → Z) (y : Ω → Y) (hf : Measurable f) (hz : Measurable z) (hy : Measurable y)
    (hffin : (f '' S).Finite) (hzfin : (z '' S).Finite) (hyfin : (y '' S).Finite) :
    ∃ (fc : Ω → (f '' S)) (zc : Ω → (z '' S)) (yc : Ω → (y '' S)),
      Measurable fc ∧ Measurable zc ∧ Measurable yc ∧
      ∀ x ∈ S, (fc x).1 = f x ∧ (zc x).1 = z x ∧ (yc x).1 = y x := by
  let G : Ω → E × Z × Y := fun x => (f x, z x, y x)
  have hG : Measurable G := hf.prodMk (hz.prodMk hy)
  have hGfin : (G '' S).Finite := by
    apply (hffin.prod (hzfin.prod hyfin)).subset
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  obtain ⟨n, _, X, decode, hX, hdecode, hrepr⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_ae μ S hS hμS G hG hGfin
  have hfm (x : Ω) : (decode (X x)).1 ∈ f '' S := by
    obtain ⟨q, hq, he⟩ := hrepr (X x)
    exact ⟨q, hq, congrArg (fun p : E × Z × Y => p.1) he⟩
  have hzm (x : Ω) : (decode (X x)).2.1 ∈ z '' S := by
    obtain ⟨q, hq, he⟩ := hrepr (X x)
    exact ⟨q, hq, congrArg (fun p : E × Z × Y => p.2.1) he⟩
  have hym (x : Ω) : (decode (X x)).2.2 ∈ y '' S := by
    obtain ⟨q, hq, he⟩ := hrepr (X x)
    exact ⟨q, hq, congrArg (fun p : E × Z × Y => p.2.2) he⟩
  let fc : Ω → (f '' S) := fun x => ⟨(decode (X x)).1, hfm x⟩
  let zc : Ω → (z '' S) := fun x => ⟨(decode (X x)).2.1, hzm x⟩
  let yc : Ω → (y '' S) := fun x => ⟨(decode (X x)).2.2, hym x⟩
  refine ⟨fc, zc, yc, ?_, ?_, ?_, ?_⟩
  · exact ((measurable_of_countable (fun i : Fin n => (decode i).1)).comp hX).subtype_mk
  · exact ((measurable_of_countable (fun i : Fin n => (decode i).2.1)).comp hX).subtype_mk
  · exact ((measurable_of_countable (fun i : Fin n => (decode i).2.2)).comp hX).subtype_mk
  · intro x hx
    have he := hdecode x hx
    exact ⟨congrArg (fun p : E × Z × Y => p.1) he,
      congrArg (fun p : E × Z × Y => p.2.1) he,
      congrArg (fun p : E × Z × Y => p.2.2) he⟩

/-- Actual history and velocity labels may be infinite types. Finiteness only
on the old full-mass support suffices, with all original marginals unchanged. -/
theorem continuous_palette_refinement_on_support {Ω E Z Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S U : Set Ω) (hS : MeasurableSet S) (hμS : μ Sᶜ = 0)
    (hU : MeasurableSet U) (hUS : U ⊆ S)
    (f : Ω → E) (z : Ω → Z) (y : Ω → Y) (hf : Measurable f) (hz : Measurable z) (hy : Measurable y)
    (hffin : (f '' S).Finite) (hzfin : (z '' S).Finite) (hyfin : (y '' S).Finite)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (K : ℕ)
    (hK : ∀ a, (y '' {x | x ∈ S ∧ z x = a}).ncard ≤ K)
    (hOld : ∀ e a, μ.real {x | x ∈ U ∧ f x = e ∧ z x = a} ≤
      R * μ.real {x | f x = e} * μ.real {x | z x = a}) :
    MeasurableSet (paletteStateCut μ U z y ε) ∧ paletteStateCut μ U z y ε ⊆ U ∧
      μ.real (U \ paletteStateCut μ U z y ε) ≤ ε * (K : ℝ) ∧
      ∀ e b, μ.real {x | x ∈ paletteStateCut μ U z y ε ∧ f x = e ∧ y x = b} ≤
        (R / ε) * μ.real {x | f x = e} * μ.real {x | y x = b} := by
  classical
  letI : Fintype (f '' S) := hffin.fintype
  letI : Fintype (z '' S) := hzfin.fintype
  letI : Fintype (y '' S) := hyfin.fintype
  obtain ⟨fc, zc, yc, hfc, hzc, hyc, hval⟩ :=
    finite_support_component_codes μ S hS hμS f z y hf hz hy hffin hzfin hyfin
  have hSae : ∀ᵐ x ∂μ, x ∈ S := ae_iff.mpr hμS
  have hfCell (e : f '' S) : μ.real {x | fc x = e} = μ.real {x | f x = e.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).1]
  have hzCell (a : z '' S) : μ.real {x | zc x = a} = μ.real {x | z x = a.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).2.1]
  have hyCell (b : y '' S) : μ.real {x | yc x = b} = μ.real {x | y x = b.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).2.2]
  have hzJoint (a : z '' S) (b : y '' S) : μ.real {x | zc x = a ∧ yc x = b} =
      μ.real {x | z x = a.1 ∧ y x = b.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).2.1, (hval x hx).2.2]
  have hfOld (B : Set Ω) (e : f '' S) (a : z '' S) :
      μ.real {x | x ∈ B ∧ fc x = e ∧ zc x = a} =
        μ.real {x | x ∈ B ∧ f x = e.1 ∧ z x = a.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).1, (hval x hx).2.1]
  have hfNew (B : Set Ω) (e : f '' S) (b : y '' S) :
      μ.real {x | x ∈ B ∧ fc x = e ∧ yc x = b} =
        μ.real {x | x ∈ B ∧ f x = e.1 ∧ y x = b.1} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hSae] with x hx
    simp only [mem_ofPred_eq, Subtype.ext_iff]
    rw [(hval x hx).1, (hval x hx).2.2]
  have hKc (a : z '' S) :
      (Finset.univ.filter (fun b => 0 < μ.real {x | zc x = a ∧ yc x = b})).card ≤ K := by
    let B := Finset.univ.filter (fun b => 0 < μ.real {x | zc x = a ∧ yc x = b})
    have hfin : (y '' {x | x ∈ S ∧ z x = a.1}).Finite :=
      hyfin.subset (image_mono (fun x hx => hx.1))
    have hsub : B.image Subtype.val ⊆ hfin.toFinset := by
      intro b hb
      obtain ⟨bc, hbc, rfl⟩ := Finset.mem_image.mp hb
      have hp := (Finset.mem_filter.mp hbc).2
      have hex : ∃ x, x ∈ S ∧ zc x = a ∧ yc x = bc := by
        by_contra hn
        have hs : {x | zc x = a ∧ yc x = bc} ⊆ Sᶜ := by
          intro x hx hxS
          exact hn ⟨x, hxS, hx⟩
        have hz0 := measure_mono_null hs hμS
        change 0 < (μ {x | zc x = a ∧ yc x = bc}).toReal at hp
        rw [hz0, ENNReal.toReal_zero] at hp
        exact (lt_irrefl 0) hp
      obtain ⟨x, hx, hza, hyb⟩ := hex
      apply hfin.mem_toFinset.mpr
      refine ⟨x, ⟨hx, ?_⟩, ?_⟩
      · exact (hval x hx).2.1.symm.trans (congrArg Subtype.val hza)
      · exact (hval x hx).2.2.symm.trans (congrArg Subtype.val hyb)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective B Subtype.val_injective] at hc
    exact hc.trans (by simpa only [Set.ncard_eq_toFinset_card _ hfin] using hK a.1)
  have hOldc (e : f '' S) (a : z '' S) :
      μ.real {x | x ∈ U ∧ fc x = e ∧ zc x = a} ≤
        R * μ.real {x | fc x = e} * μ.real {x | zc x = a} := by
    rw [hfOld U e a, hfCell e, hzCell a]
    exact hOld e.1 a.1
  have heqG : paletteStateCut μ U zc yc ε = paletteStateCut μ U z y ε := by
    ext x
    by_cases hx : x ∈ U
    · have hv := hval x (hUS hx)
      simp only [paletteStateCut, mem_ofPred_eq, hx, true_and]
      rw [hzCell (zc x), hzJoint (zc x) (yc x), hv.2.1, hv.2.2]
    · simp only [paletteStateCut, mem_ofPred_eq, hx, false_and]
  obtain ⟨hG, hGU, hlost, hcap⟩ := continuous_palette_refinement μ U hU fc zc yc hfc hzc hyc hε hR K hKc hOldc
  rw [heqG] at hG hGU hlost hcap
  refine ⟨hG, hGU, hlost, ?_⟩
  intro e b
  by_cases he : e ∈ f '' S
  · by_cases hb : b ∈ y '' S
    · have hh := hcap ⟨e, he⟩ ⟨b, hb⟩
      rw [hfNew, hfCell, hyCell] at hh
      exact hh
    · have hempty : {x | x ∈ paletteStateCut μ U z y ε ∧ f x = e ∧ y x = b} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hb ⟨x, hUS (hGU hx.1), hx.2.2⟩
      rw [hempty, measureReal_empty]
      exact mul_nonneg (mul_nonneg (div_nonneg hR hε.le) measureReal_nonneg) measureReal_nonneg
  · have hempty : {x | x ∈ paletteStateCut μ U z y ε ∧ f x = e ∧ y x = b} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact he ⟨x, hUS (hGU hx.1), hx.2.1⟩
    rw [hempty, measureReal_empty]
    exact mul_nonneg (mul_nonneg (div_nonneg hR hε.le) measureReal_nonneg) measureReal_nonneg

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
