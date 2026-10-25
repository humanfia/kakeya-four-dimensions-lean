/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/SampledPathMasks.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CommonMasks

/-! Exceptional events chosen on the ACTUAL sampled chart sequences.
A head event is indexed by its normalized child's sample and lives in the
original parent space at that sample. This permits chosen-atlas events
without extending them to unrelated original sample indices. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

def SampledEvents {p z : Code} (chain : RefinementChain p z) : Type :=
  match chain with
  | .nil _ => PUnit
  | .cons w _ tail =>
      ((k : ℕ) → Set (Fin (W p (w.sample k)) × State)) × tail.SampledEvents

def SampledEventsMeasurable {p z : Code} (chain : RefinementChain p z) :
    chain.SampledEvents → Prop :=
  match chain with
  | .nil _ => fun _ => True
  | .cons _ _ tail => fun events =>
      (∀ k, MeasurableSet (events.1 k)) ∧ tail.SampledEventsMeasurable events.2

def SampledEventsSmall {p z : Code} (chain : RefinementChain p z) :
    chain.SampledEvents → Prop :=
  match chain with
  | .nil _ => fun _ => True
  | @cons p q z _r _b _h w hp tail => fun events =>
      IsPowerSmall (N q) (fun k => worldMixture p (w.sample k) (events.1 k)) ∧
        tail.SampledEventsSmall events.2

def sampledBadSet {p z : Code} (chain : RefinementChain p z) :
    chain.SampledEvents → (k : ℕ) → Set (Fin (W z k) × State) :=
  match chain with
  | .nil _ => fun _ _ => ∅
  | .cons w hp tail => fun events k =>
      (RefinementChain.cons w hp tail).pullback k ⁻¹' events.1 (tail.sample k) ∪ tail.sampledBadSet events.2 k

def sampledExceptionMass {p z : Code} (chain : RefinementChain p z) :
    chain.SampledEvents → ℕ → ℝ≥0∞ :=
  match chain with
  | .nil _ => fun _ _ => 0
  | .cons w _ tail => fun events k =>
      worldMixture p (w.sample (tail.sample k)) (events.1 (tail.sample k)) +
        tail.sampledExceptionMass events.2 k

theorem measurableSet_sampledBadSet {p z : Code} (chain : RefinementChain p z)
    (events : chain.SampledEvents) (hm : chain.SampledEventsMeasurable events) (k : ℕ) :
    MeasurableSet (chain.sampledBadSet events k) := by
  induction chain with
  | nil => exact MeasurableSet.empty
  | cons w hp tail ih =>
    exact ((hm.1 _).preimage ((RefinementChain.cons w hp tail).measurable_pullback k)).union
      (ih events.2 hm.2)

/-- One complete-path reference factor charges every chosen sampled
head event to its unchanged original parent law. -/
theorem sampledBadSet_mass_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (events : chain.SampledEvents)
    (hm : chain.SampledEventsMeasurable events) (k : ℕ)
    (R : ℝ) (hR : chain.referenceFactor k ≤ R) :
    normalizedWorldMixture z k (chain.sampledBadSet events k) ≤
      ENNReal.ofReal R * chain.sampledExceptionMass events k := by
  induction chain with
  | nil => simp only [sampledBadSet, sampledExceptionMass, measure_empty, mul_zero, le_refl]
  | cons w hp tail ih =>
    change normalizedWorldMixture _ k
      (((RefinementChain.cons w hp tail).pullback k ⁻¹' events.1 (tail.sample k)) ∪
        tail.sampledBadSet events.2 k) ≤ ENNReal.ofReal R * (_ + _)
    calc
      _ ≤ normalizedWorldMixture _ k
          ((RefinementChain.cons w hp tail).pullback k ⁻¹' events.1 (tail.sample k)) +
          normalizedWorldMixture _ k (tail.sampledBadSet events.2 k) := measure_union_le _ _
      _ ≤ ENNReal.ofReal R * worldMixture _ _ (events.1 (tail.sample k)) +
          ENNReal.ofReal R * tail.sampledExceptionMass events.2 k := add_le_add
        ((RefinementChain.cons w hp tail).common_preimage_le hz k (hm.1 _) R hR)
        (ih hz events.2 hm.2 ((referenceFactor_tail_le w hp tail hz k).trans hR))
      _ = _ := (mul_add _ _ _).symm

theorem sampledExceptionMass_powerSmall {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (events : chain.SampledEvents) (hs : chain.SampledEventsSmall events) :
    IsPowerSmall (N z) (chain.sampledExceptionMass events) := by
  induction chain with
  | nil => exact ⟨1, by norm_num, Eventually.of_forall fun _ => zero_le⟩
  | @cons p q z _r _b _h w hp tail ih =>
    have hhead := hs.1.comp tail.sample tail.sample_strictMono.tendsto_atTop
    have hhead' : IsPowerSmall (N z) (fun k =>
        worldMixture p (w.sample (tail.sample k)) (events.1 (tail.sample k))) := by
      rw [show N q ∘ tail.sample = N z from funext fun k => (tail.resolution k).symm] at hhead
      exact hhead
    exact hhead'.add hz.1.2.1 (ih hz events.2 hs.2)

/-- All chosen chart-sequence exceptions remain power-small under the
SAME common final probability. -/
theorem sampledBadSet_powerSmall {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (events : chain.SampledEvents)
    (hm : chain.SampledEventsMeasurable events) (hs : chain.SampledEventsSmall events) :
    IsPowerSmall (N z) (fun k => normalizedWorldMixture z k (chain.sampledBadSet events k)) := by
  apply (Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower
    (fun k => (by linarith [hz.1.1 k])) (chain.referenceFactor_subpower hz)
      (chain.sampledExceptionMass_powerSmall hz events hs)).mono
  exact Eventually.of_forall fun k => chain.sampledBadSet_mass_le hz events hm k _ le_rfl

def sampledCore {p z : Code} (chain : RefinementChain p z)
    (events : chain.SampledEvents) (k : ℕ) : Set (Fin (W z k) × State) :=
  chain.pathSet k ∩ (chain.sampledBadSet events k)ᶜ

theorem measurableSet_sampledCore {p z : Code} (chain : RefinementChain p z)
    (events : chain.SampledEvents) (hm : chain.SampledEventsMeasurable events) (k : ℕ) :
    MeasurableSet (chain.sampledCore events k) :=
  (chain.measurableSet_pathSet k).inter (chain.measurableSet_sampledBadSet events hm k).compl

theorem sampledCore_mass_half {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (events : chain.SampledEvents) (hm : chain.SampledEventsMeasurable events)
    (k : ℕ) (hsmall : normalizedWorldMixture z k (chain.sampledBadSet events k) ≤
      ENNReal.ofReal (1 / 2 : ℝ)) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture z k (chain.sampledCore events k) := by
  let := normalizedWorldMixture_isProbability hz k
  have hcore : normalizedWorldMixture z k (chain.sampledCore events k) =
      normalizedWorldMixture z k (chain.sampledBadSet events k)ᶜ :=
    Measure.measure_inter_eq_of_ae (chain.pathSet_ae_normalized k)
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (1 : ℝ≥0∞) _ _ 1 (by norm_num) (by norm_num) ?_ hsmall
  rw [hcore, add_comm, measure_add_measure_compl (chain.measurableSet_sampledBadSet events hm k)]
  simp

/-- One measurable path mask removes all chosen sampled exceptions and
retains at least half the SAME path probability eventually. -/
theorem eventually_sampledCore_mass_half {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (events : chain.SampledEvents)
    (hm : chain.SampledEventsMeasurable events) (hs : chain.SampledEventsSmall events) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture z k (chain.sampledCore events k) := by
  obtain ⟨c, hc, hbound⟩ := chain.sampledBadSet_powerSmall hz events hm hs
  have hlim := (tendsto_rpow_neg_atTop hc).comp hz.1.2.1
  have hhalf : ∀ᶠ k in atTop, N z k ^ (-c) ≤ (1 / 2 : ℝ) :=
    hlim.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hbound, hhalf] with k hk hh
  exact chain.sampledCore_mass_half hz events hm k (hk.trans (ENNReal.ofReal_le_ofReal hh))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
