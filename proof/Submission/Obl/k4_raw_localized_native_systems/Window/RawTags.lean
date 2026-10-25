import Submission.Obl.k4_raw_localized_native_systems.Window.RawLaws
import Submission.Obl.k4_raw_localized_native_systems.Window.Tags

/- Adapted from this LOT tree, o197, session x0692, Window/Tags.lean,
   commit 89bdc88a, retaining raw graph coordinates and full witness masses. -/

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The earlier atlas with analytical witness events in place of reference events. -/
def rawAtlas (W : Atlas p k) (H : Fin W.C → Set Point) : Atlas p k :=
  { W with F := H }

def rawSupportSet (W : Atlas p k) (H : Fin W.C → Set Point) {C : ℕ}
    (Compat : Fin C → Fin W.C → Prop) (FC : Fin C → Set Point) (a : Fin C) : Set Point :=
  certSupport (rawAtlas W H) Compat FC a

def rawTag (W : Atlas p k) (H : Fin W.C → Set Point) {C : ℕ}
    (Compat : Fin C → Fin W.C → Prop) (d : Fin W.C) (a : Fin C) : Point → Fin W.C :=
  ctag (rawAtlas W H) Compat d a

theorem raw_tagged_domination (W : Atlas p k)
    (H : Fin W.C → Set Point) (hH : ∀ e, MeasurableSet (H e))
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (law : Fin C → Measure Point) (R : Fin C → ENNReal)
    (Compat : Fin C → Fin W.C → Prop) (hcw : ∀ a e, Compat a e → W.γ e = γC a)
    (hFC : ∀ a, MeasurableSet (FC a))
    (hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (hlaw : ∀ a, R a • law a ≤
      ENNReal.ofReal (p.ω k (γC a)) • (priorMass p k (γC a)).restrict (FC a))
    (d : Fin W.C) (e : Fin W.C) :
    (∑ a, R a • Measure.map (rawGraph) ((law a).restrict
        {q | q ∈ rawSupportSet W H Compat FC a ∧ rawTag W H Compat d a q = e})) ≤
      ENNReal.ofReal (p.ω k (W.γ e)) • rawLaw W H e := by
  classical
  have hF : ∀ e, MeasurableSet ((rawAtlas W H).F e) := hH
  set γ := W.γ e
  set X : Fin C → Set Point :=
    fun a => {q | q ∈ rawSupportSet W H Compat FC a ∧ rawTag W H Compat d a q = e} with hXdef
  have hX : ∀ a, MeasurableSet (X a) := fun a =>
    (measurableSet_certSupport (rawAtlas W H) Compat hF hFC a).inter
      (measurable_ctag (rawAtlas W H) Compat hF d a (measurableSet_singleton e))
  have hXsub : ∀ a, X a ⊆ {q | Compat a e ∧ q ∈ FC a ∧ q ∈ H e} := by
    intro a q hq
    obtain ⟨hsupp, htag⟩ := hq
    obtain ⟨hFCq, hc, hWF⟩ := ctag_spec (rawAtlas W H) Compat d hsupp
    change Compat a (rawTag W H Compat d a q) at hc
    change q ∈ H (rawTag W H Compat d a q) at hWF
    rw [htag] at hc hWF
    exact ⟨hc, hFCq, hWF⟩
  rw [rawLaw]
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.map_apply (measurable_rawGraph) hs, Measure.restrict_apply ((measurable_rawGraph) hs)]
  set Y := rawGraph ⁻¹' s with hYdef
  have hY : MeasurableSet Y := (measurable_rawGraph) hs
  have hterm : ∀ a, R a * (Measure.map (rawGraph) ((law a).restrict (X a))) s ≤
      if γC a = γ then ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ H e)) else 0 := by
    intro a
    rw [Measure.map_apply (measurable_rawGraph) hs, Measure.restrict_apply hY]
    by_cases hc : Compat a e
    · have hγ : γC a = γ := (hcw a e hc).symm
      rw [if_pos hγ]
      have h1 := hlaw a (Y ∩ X a)
      simp only [Measure.smul_apply, smul_eq_mul] at h1
      rw [Measure.restrict_apply (hY.inter (hX a))] at h1
      calc R a * (law a) (Y ∩ X a) ≤ ENNReal.ofReal (p.ω k (γC a)) *
            priorMass p k (γC a) (Y ∩ X a ∩ FC a) := h1
        _ ≤ ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ H e)) := by
            rw [hγ]
            refine mul_le_mul_right (measure_mono fun q hq => ?_) _
            have hqX : q ∈ X a := hq.1.2
            have := hXsub a hqX
            exact ⟨hq.2, hq.1.1, this.2.2⟩
    · have hempty : Y ∩ X a = ∅ := by
        ext q
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro _ hq
        exact hc (hXsub a hq).1
      rw [hempty, measure_empty, mul_zero]
      split_ifs <;> exact le_rfl.trans (by simp)
  calc ∑ a, R a * (Measure.map (rawGraph) ((law a).restrict (X a))) s
      ≤ ∑ a, (if γC a = γ then
          ENNReal.ofReal (p.ω k γ) * priorMass p k γ (FC a ∩ (Y ∩ H e)) else 0) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = ENNReal.ofReal (p.ω k γ) *
          ∑ a ∈ Finset.univ.filter (fun a => γC a = γ), priorMass p k γ (FC a ∩ (Y ∩ H e)) := by
        rw [← Finset.sum_filter, Finset.mul_sum]
    _ = ENNReal.ofReal (p.ω k γ) *
          priorMass p k γ (⋃ a ∈ Finset.univ.filter (fun a => γC a = γ), FC a ∩ (Y ∩ H e)) := by
        congr 1
        rw [measure_biUnion_finset]
        · intro a ha a' ha' hne
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at ha ha'
          exact ((hFCdisj a a' hne (ha.trans ha'.symm)).mono inter_subset_left inter_subset_left)
        · exact fun a _ => (hFC a).inter (hY.inter (hF e))
    _ ≤ ENNReal.ofReal (p.ω k γ) * priorMass p k γ (Y ∩ H e) := by
        gcongr
        intro q hq
        simp only [mem_iUnion] at hq
        obtain ⟨a, -, hqa⟩ := hq
        exact hqa.2


end
end Submission.Obl.k4_raw_localized_native_systems.Window
