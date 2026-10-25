/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/AngularCoarsening.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Lib.K4Homogenization.AngularCoarsening
import Submission.Lib.K4Homogenization.DyadicObservations
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions

/-! Exceptional-mass bounds for coarsening the pure observation. The conclusion
uses any of the measurable density representatives in the frozen interface. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open Submission.Lib.K4Homogenization
open scoped ENNReal

section General

variable {Ω X Y I : Type*}
  [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I]

/-- A conditional joint ceiling on a retained source fails for the full source
on at most twice the omitted mass. No density of the retained source is an input. -/
theorem observation_tail_of_restricted_joint_le
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (κ : Measure I) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (Z : Set Ω) (hZ : MeasurableSet Z) (c : ℝ≥0∞)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (H : X × I → ℝ≥0∞) (hH : Measurable H)
    (hpure : ν.map obs = μ.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (μ.prod κ).withDensity H)
    (hbound : (ν.restrict Z).map (fun p => (obs p, ang p)) ≤
      c • (ν.map obs).prod κ) :
    ν {p | 2 * c * f (obs p) < H (obs p, ang p)} ≤ 2 * ν Zᶜ := by
  let o : Ω → X × I := fun p => (obs p, ang p)
  have ho : Measurable o := hobs.prodMk hang
  let ξ := (ν.restrict Z).map o
  let ζ := (ν.restrict Zᶜ).map o
  let ρ := μ.prod κ
  let g := ξ.rnDeriv ρ
  let b := ζ.rnDeriv ρ
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  have hb : Measurable b := Measure.measurable_rnDeriv _ _
  have hξle : ξ ≤ ν.map o := Measure.map_mono Measure.restrict_le_self ho
  have hζle : ζ ≤ ν.map o := Measure.map_mono Measure.restrict_le_self ho
  have habs : ν.map o ≪ ρ := by
    rw [hjoint]
    exact withDensity_absolutelyContinuous _ _
  have hξ : ρ.withDensity g = ξ :=
    Measure.withDensity_rnDeriv_eq _ _ (hξle.absolutelyContinuous.trans habs)
  have hζ : ρ.withDensity b = ζ :=
    Measure.withDensity_rnDeriv_eq _ _ (hζle.absolutelyContinuous.trans habs)
  have hsum : ν.map o = ρ.withDensity (g + b) := by
    rw [withDensity_add_left hg, hξ, hζ]
    change ν.map o = (ν.restrict Z).map o + (ν.restrict Zᶜ).map o
    rw [← Measure.map_add _ _ ho, Measure.restrict_add_restrict_compl hZ]
  have hgood : g ≤ᵐ[ρ] fun p => c * f p.1 := by
    apply coarsened_joint_density_le (ν.map obs) κ ξ c hbound id measurable_id μ f hf
    · simpa only [Measure.map_id] using hpure
    · exact hg
    · simpa only [Prod.map_id, Measure.map_id] using hξ.symm
  have htail := observation_upper_except_omitted ν ρ o ho
    (fun p : X × I => f p.1) g b c (hf.comp measurable_fst) hg hb hgood hsum
  have hmass : (∫⁻ x, b x ∂ρ) = ν Zᶜ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, hζ]
    change ((ν.restrict Zᶜ).map o) univ = ν Zᶜ
    rw [Measure.map_apply ho MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hver := observation_density_test_mass_eq ν ρ o ho
    hH (hg.add hb) hjoint hsum
    (fun p h => 2 * c * f p.1 < h)
  rw [hver]
  simpa only [o, hmass, Pi.add_apply] using htail

/-- Remove precisely those fine observations that violate a conditional ceiling. -/
theorem restricted_joint_le_of_density_ceiling
    (ν : Measure Ω) (μ : Measure X) [SigmaFinite μ]
    (κ : Measure I) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (c : ℝ≥0∞) (f : X → ℝ≥0∞) (hf : Measurable f)
    (H : X × I → ℝ≥0∞) (hH : Measurable H)
    (hpure : ν.map obs = μ.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (μ.prod κ).withDensity H) :
    (ν.restrict {p | H (obs p, ang p) ≤ c * f (obs p)}).map
      (fun p => (obs p, ang p)) ≤ c • (ν.map obs).prod κ := by
  let o : Ω → X × I := fun p => (obs p, ang p)
  let A : Set (X × I) := {p | H p ≤ c * f p.1}
  have hA : MeasurableSet A := measurableSet_le hH (measurable_const.mul
    (hf.comp measurable_fst))
  have ho : Measurable o := hobs.prodMk hang
  change (ν.restrict (o ⁻¹' A)).map o ≤ _
  rw [← Measure.restrict_map ho hA, hjoint, restrict_withDensity hA,
    ← withDensity_indicator hA, hpure, prod_withDensity_left hf,
    ← withDensity_smul (f := fun p : X × I => f p.1) c
      (hf.comp measurable_fst)]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun p => by
    by_cases hp : p ∈ A
    · simpa only [indicator_of_mem hp, Pi.smul_apply, smul_eq_mul] using
        (show H p ≤ c * f p.1 from hp)
    · simp only [indicator_of_notMem hp, Pi.smul_apply, smul_eq_mul, zero_le]

/-- Coarsening the pure observation preserves the conditional angular ceiling,
apart from twice the mass violating that ceiling at the original fine scale. -/
theorem angular_tail_after_coarsening
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (μ' : Measure Y) [SigmaFinite μ']
    (κ : Measure I) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (q : X → Y) (hq : Measurable q) (c : ℝ≥0∞)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (H : X × I → ℝ≥0∞) (hH : Measurable H)
    (F : Y → ℝ≥0∞) (hF : Measurable F)
    (J : Y × I → ℝ≥0∞) (hJ : Measurable J)
    (hpure : ν.map obs = μ.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (μ.prod κ).withDensity H)
    (hpure' : ν.map (q ∘ obs) = μ'.withDensity F)
    (hjoint' : ν.map (fun p => (q (obs p), ang p)) = (μ'.prod κ).withDensity J) :
    ν {p | 2 * c * F (q (obs p)) < J (q (obs p), ang p)} ≤
      2 * ν {p | c * f (obs p) < H (obs p, ang p)} := by
  let Z : Set Ω := {p | H (obs p, ang p) ≤ c * f (obs p)}
  have hZ : MeasurableSet Z := measurableSet_le
    (hH.comp (hobs.prodMk hang)) (measurable_const.mul (hf.comp hobs))
  have hgood := restricted_joint_le_of_density_ceiling ν μ κ obs hobs ang hang c
    f hf H hH hpure hjoint
  have hcoarse := coarsened_observation_measure_le ν (ν.restrict Z) κ
    obs hobs ang hang q hq c hgood
  have htail := observation_tail_of_restricted_joint_le ν μ' κ (q ∘ obs)
    (hq.comp hobs) ang hang Z hZ c F hF J hJ hpure' hjoint' hcoarse
  have hcompl : Zᶜ = {p | c * f (obs p) < H (obs p, ang p)} := by
    ext p
    simp only [Z, mem_compl_iff, mem_ofPred_eq, not_le]
  simpa only [Function.comp_apply, hcompl] using htail

/-- Absolute angular-density bounds after coarsening cost only the old lower pure
tail, the old upper joint tail, and the new upper pure tail. -/
theorem angular_absolute_tail_after_coarsening
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (μ' : Measure Y) [SigmaFinite μ']
    (κ : Measure I) [SigmaFinite κ]
    (obs : Ω → X) (hobs : Measurable obs) (ang : Ω → I) (hang : Measurable ang)
    (q : X → Y) (hq : Measurable q)
    (c lo hi U : ℝ≥0∞) (hscale : hi ≤ c * lo)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (H : X × I → ℝ≥0∞) (hH : Measurable H)
    (F : Y → ℝ≥0∞) (hF : Measurable F)
    (J : Y × I → ℝ≥0∞) (hJ : Measurable J)
    (hpure : ν.map obs = μ.withDensity f)
    (hjoint : ν.map (fun p => (obs p, ang p)) = (μ.prod κ).withDensity H)
    (hpure' : ν.map (q ∘ obs) = μ'.withDensity F)
    (hjoint' : ν.map (fun p => (q (obs p), ang p)) = (μ'.prod κ).withDensity J) :
    ν {p | 2 * c * U < J (q (obs p), ang p)} ≤
      2 * (ν {p | f (obs p) < lo} + ν {p | hi < H (obs p, ang p)}) +
      ν {p | U < F (q (obs p))} := by
  have hcoarse := angular_tail_after_coarsening ν μ μ' κ obs hobs ang hang q hq c
    f hf H hH F hF J hJ hpure hjoint hpure' hjoint'
  have hfine : ν {p | c * f (obs p) < H (obs p, ang p)} ≤
      ν {p | f (obs p) < lo} + ν {p | hi < H (obs p, ang p)} := by
    apply (measure_mono (fun p hp => ?_)).trans (measure_union_le _ _)
    by_cases hl : f (obs p) < lo
    · exact Or.inl hl
    · exact Or.inr ((hscale.trans (mul_le_mul' le_rfl (le_of_not_gt hl))).trans_lt hp)
  have hsub : {p | 2 * c * U < J (q (obs p), ang p)} ⊆
      {p | 2 * c * F (q (obs p)) < J (q (obs p), ang p)} ∪
        {p | U < F (q (obs p))} := by
    intro p hp
    by_cases hu : U < F (q (obs p))
    · exact Or.inr hu
    · exact Or.inl ((mul_le_mul' le_rfl (le_of_not_gt hu)).trans_lt hp)
  calc
    _ ≤ ν ({p | 2 * c * F (q (obs p)) < J (q (obs p), ang p)} ∪
        {p | U < F (q (obs p))}) := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans
      (add_le_add (hcoarse.trans (mul_le_mul' le_rfl hfine)) (le_refl _))

end General

/-- The native scalar observation at a smaller depth is an exact measurable
coarsening of the observation at a larger depth. -/
theorem obs_coarsening (B : ℝ) {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s)
    (p : Incidence) :
    obs B (δ N r) p = coarsenObservation N r s (obs B (δ N s) p) := by
  exact observation_factorization
    (fun z : Incidence => WithLp.toLp 2 ![z.2, (x z.1 z.2) 1, (x z.1 z.2) 2])
    (fun z : Incidence => B * (x z.1 z.2) 3) hN hrs p

end Submission.Obl.k4_balanced_native_packet_transport.CPF
