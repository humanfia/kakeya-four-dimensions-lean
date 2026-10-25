/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/CommonMasks.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathSupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SuffixReferences
import Submission.Obl.k4_dyadic_crop_typicality.Assembly
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

/-! Simultaneous exceptional-set removal in every original frame of one
finite measured path. Exceptional masses are charged to the original laws,
with one common path factor; no conditional reference law is changed. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

def badSet {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State)) (k : ℕ) :
    Set (Fin (W z k) × State) :=
  chain.pullback k ⁻¹' bad p (chain.sample k) ∪
    match chain with
    | .nil _ => ∅
    | .cons _ _ tail => tail.badSet bad k

def exceptionMass {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State)) (k : ℕ) : ℝ≥0∞ :=
  worldMixture p (chain.sample k) (bad p (chain.sample k)) +
    match chain with
    | .nil _ => 0
    | .cons _ _ tail => tail.exceptionMass bad k

theorem measurableSet_badSet {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hbad : ∀ q k, MeasurableSet (bad q k)) (k : ℕ) :
    MeasurableSet (chain.badSet bad k) := by
  induction chain with
  | nil p => simpa only [badSet, union_empty, sample, id_eq] using
      (hbad p k).preimage ((RefinementChain.nil p).measurable_pullback k)
  | cons w hp tail ih =>
    exact ((hbad _ _).preimage
      ((RefinementChain.cons w hp tail).measurable_pullback k)).union ih

theorem common_preimage_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {S : Set (Fin (W p (chain.sample k)) × State)}
    (hS : MeasurableSet S) (R : ℝ) (hR : chain.referenceFactor k ≤ R) :
    normalizedWorldMixture z k (chain.pullback k ⁻¹' S) ≤
      ENNReal.ofReal R * worldMixture p (chain.sample k) S := by
  rw [← Measure.map_apply (chain.measurable_pullback k) hS,
    ← chain.probability_eq_map_finalMixture k]
  calc
    _ ≤ (ENNReal.ofReal (chain.referenceFactor k) •
        worldMixture p (chain.sample k)) S := chain.probability_le_originalReference hz k S
    _ ≤ _ := by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl

/-- Union bound over the actual path's potential parents, charged to all
their predeletion original laws with the same reference factor. -/
theorem badSet_mass_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hbad : ∀ q k, MeasurableSet (bad q k)) (k : ℕ)
    (R : ℝ) (hR : chain.referenceFactor k ≤ R) :
    normalizedWorldMixture z k (chain.badSet bad k) ≤
      ENNReal.ofReal R * chain.exceptionMass bad k := by
  induction chain with
  | nil p => simpa only [badSet, exceptionMass, union_empty, add_zero] using
      (RefinementChain.nil p).common_preimage_le hz k (hbad p _) R hR
  | cons w hp tail ih =>
    change normalizedWorldMixture _ k
      (((RefinementChain.cons w hp tail).pullback k ⁻¹' bad _ _) ∪ tail.badSet bad k) ≤
        ENNReal.ofReal R * (_ + tail.exceptionMass bad k)
    calc
      _ ≤ normalizedWorldMixture _ k
          ((RefinementChain.cons w hp tail).pullback k ⁻¹' bad _ _) +
            normalizedWorldMixture _ k (tail.badSet bad k) := measure_union_le _ _
      _ ≤ ENNReal.ofReal R * worldMixture _ _ (bad _ _) +
          ENNReal.ofReal R * tail.exceptionMass bad k := add_le_add
        ((RefinementChain.cons w hp tail).common_preimage_le hz k (hbad _ _) R hR)
        (ih hz ((referenceFactor_tail_le w hp tail hz k).trans hR))
      _ = _ := (mul_add _ _ _).symm

theorem exceptionMass_powerSmall {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hbad : chain.AllSuffixes (fun q _ => IsPowerSmall (N q)
      (fun k => worldMixture q k (bad q k)))) :
    IsPowerSmall (N z) (chain.exceptionMass bad) := by
  induction chain with
  | nil p =>
    obtain ⟨c, hc, hsmall⟩ := hbad
    refine ⟨c, hc, ?_⟩
    filter_upwards [hsmall] with k hk
    change worldMixture p k (bad p k) + 0 ≤ _
    simpa only [add_zero] using hk
  | @cons p q z r b h w hp tail ih =>
    have hhead := hbad.1.comp (RefinementChain.cons w hp tail).sample
      (RefinementChain.cons w hp tail).sample_strictMono.tendsto_atTop
    have hhead' : IsPowerSmall (N z) (fun k =>
        worldMixture p ((RefinementChain.cons w hp tail).sample k)
          (bad p ((RefinementChain.cons w hp tail).sample k))) := by
      rw [show N p ∘ (RefinementChain.cons w hp tail).sample = N z from
        funext fun k => ((RefinementChain.cons w hp tail).resolution k).symm] at hhead
      exact hhead
    exact hhead'.add hz.1.2.1 (ih hz hbad.2)

/-- Power-small original pure/angular exceptions remain power-small under
the common path probability, simultaneously for all its potential parents. -/
theorem badSet_powerSmall {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hmeas : ∀ q k, MeasurableSet (bad q k))
    (hbad : chain.AllSuffixes (fun q _ => IsPowerSmall (N q)
      (fun k => worldMixture q k (bad q k)))) :
    IsPowerSmall (N z) (fun k => normalizedWorldMixture z k (chain.badSet bad k)) := by
  apply (Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower
    (fun k => (by linarith [hz.1.1 k])) (chain.referenceFactor_subpower hz)
      (chain.exceptionMass_powerSmall hz bad hbad)).mono
  exact Eventually.of_forall fun k => chain.badSet_mass_le hz bad hmeas k _ le_rfl

theorem eventually_badSet_mass_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hmeas : ∀ q k, MeasurableSet (bad q k))
    (hbad : chain.AllSuffixes (fun q _ => IsPowerSmall (N q)
      (fun k => worldMixture q k (bad q k)))) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k in atTop, normalizedWorldMixture z k (chain.badSet bad k) ≤ ENNReal.ofReal η := by
  obtain ⟨c, hc, hsmall⟩ := chain.badSet_powerSmall hz bad hmeas hbad
  have hlim := (tendsto_rpow_neg_atTop hc).comp hz.1.2.1
  have hη' : ∀ᶠ k in atTop, N z k ^ (-c) < η :=
    hlim.eventually (gt_mem_nhds hη)
  filter_upwards [hsmall, hη'] with k hk hpow
  exact hk.trans (ENNReal.ofReal_le_ofReal hpow.le)

def commonCore {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State)) (k : ℕ) :
    Set (Fin (W z k) × State) := chain.pathSet k ∩ (chain.badSet bad k)ᶜ

theorem measurableSet_commonCore {p z : Code} (chain : RefinementChain p z)
    (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hmeas : ∀ q k, MeasurableSet (bad q k)) (k : ℕ) :
    MeasurableSet (chain.commonCore bad k) :=
  (chain.measurableSet_pathSet k).inter (chain.measurableSet_badSet bad hmeas k).compl

theorem commonCore_mass_half {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hmeas : ∀ q k, MeasurableSet (bad q k)) (k : ℕ)
    (hsmall : normalizedWorldMixture z k (chain.badSet bad k) ≤ ENNReal.ofReal (1 / 2 : ℝ)) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture z k (chain.commonCore bad k) := by
  letI := normalizedWorldMixture_isProbability hz k
  have hcore : normalizedWorldMixture z k (chain.commonCore bad k) =
      normalizedWorldMixture z k (chain.badSet bad k)ᶜ :=
    Measure.measure_inter_eq_of_ae (chain.pathSet_ae_normalized k)
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (1 : ℝ≥0∞) _ _ 1 (by norm_num) (by norm_num) ?_ hsmall
  rw [hcore, add_comm, measure_add_measure_compl (chain.measurableSet_badSet bad hmeas k)]
  simp

/-- A single measurable original-path mask removes all fixed-stage
potential-parent exceptions while retaining at least half the probability. -/
theorem eventually_commonCore_mass_half {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (bad : (q : Code) → (k : ℕ) → Set (Fin (W q k) × State))
    (hmeas : ∀ q k, MeasurableSet (bad q k))
    (hbad : chain.AllSuffixes (fun q _ => IsPowerSmall (N q)
      (fun k => worldMixture q k (bad q k)))) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture z k (chain.commonCore bad k) := by
  filter_upwards [chain.eventually_badSet_mass_le hz bad hmeas hbad (1 / 2) (by norm_num)]
    with k hk
  exact chain.commonCore_mass_half hz bad hmeas k hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
