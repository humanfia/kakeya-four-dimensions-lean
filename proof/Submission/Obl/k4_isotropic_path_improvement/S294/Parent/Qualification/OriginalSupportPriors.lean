-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalSupportPriors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalSupportPriors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalSupportPriors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalSupportPriors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Lib.K4Homogenization.RetainedDuration

/-!
Original priors of groups that a trajectory visits for positive time.
These are measurable supporting sets, even when the projection of an
arbitrary incidence set is not known to be measurable. Their total prior
is charged to actual visits by one original trajectory.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4Homogenization
open scoped ENNReal

noncomputable section

def originalOccupationSupport {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) (G : X × T → ENNReal) : Set X :=
  {x | 0 < incidenceDuration τ G univ x}

theorem measurableSet_originalOccupationSupport {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (τ : Measure T) [SFinite τ]
    {G : X × T → ENNReal} (hG : Measurable G) :
    MeasurableSet (originalOccupationSupport τ G) :=
  measurableSet_lt measurable_const (measurable_incidenceDuration τ hG univ)

theorem exists_original_occupation {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) (G : X × T → ENNReal) (x : X)
    (hx : x ∈ originalOccupationSupport τ G) : ∃ t, G (x,t) ≠ 0 := by
  by_contra h
  have hz : (fun t => G (x,t)) = 0 := by
    funext t
    exact not_ne_iff.mp (fun ht => h ⟨t, ht⟩)
  have hd : incidenceDuration τ G univ x = 0 := by
    dsimp only [incidenceDuration]
    rw [Measure.restrict_univ, hz]
    exact lintegral_zero_fun
  exact (ne_of_gt hx) hd

/-- The preceding original incidence law gives zero mass to trajectories
with zero occupation, without replacing the original prior. -/
theorem original_occupation_support_null {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ENNReal} (hG : Measurable G) :
    (ν.prod τ).withDensity G ((originalOccupationSupport τ G)ᶜ ×ˢ univ) = 0 := by
  rw [duration_rectangle_mass ν τ hG
    (measurableSet_originalOccupationSupport τ hG).compl MeasurableSet.univ]
  apply setLIntegral_eq_zero (measurableSet_originalOccupationSupport τ hG).compl
  intro x hx
  exact le_antisymm (le_of_not_gt hx) zero_le

/-- Every later original submeasure is supported by these same positive
occupation trajectories. The support is taken before the later choice. -/
theorem ae_original_occupation_support {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ENNReal} (hG : Measurable G)
    (σ : Measure (X × T)) (K : ENNReal)
    (hσ : σ ≤ K • (ν.prod τ).withDensity G) :
    ∀ᵐ p ∂σ, p.1 ∈ originalOccupationSupport τ G := by
  apply ae_iff.mpr
  have heq : {p : X × T | ¬p.1 ∈ originalOccupationSupport τ G} =
      (originalOccupationSupport τ G)ᶜ ×ˢ univ := by ext p; simp
  rw [heq]
  apply le_antisymm _ zero_le
  calc
    _ ≤ (K • (ν.prod τ).withDensity G) ((originalOccupationSupport τ G)ᶜ ×ˢ univ) := hσ _
    _ = 0 := by rw [Measure.smul_apply, smul_eq_mul,
      original_occupation_support_null ν τ hG, mul_zero]

/-- A finite family of positive-occupation supporting priors costs only
the number of groups visited by each original trajectory. The sets can
overlap and the family need not partition the original prior. -/
theorem original_support_prior_budget {X T I : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) (τ : Measure T) [SFinite τ]
    (F : Finset I) (G : I → X × T → ENNReal) (hG : ∀ i ∈ F, Measurable (G i))
    (J : ENNReal)
    (hcount : ∀ᵐ x ∂ν,
      ((F.filter fun i => 0 < incidenceDuration τ (G i) univ x).card : ENNReal) ≤ J) :
    (∑ i ∈ F, ν (originalOccupationSupport τ (G i))) ≤ J * ν univ := by
  classical
  let B : I → X → ENNReal := fun i =>
    (originalOccupationSupport τ (G i)).indicator (fun _ => 1)
  have hB (i : I) (hi : i ∈ F) : Measurable (B i) :=
    measurable_const.indicator (measurableSet_originalOccupationSupport τ (hG i hi))
  have hmass (i : I) (hi : i ∈ F) :
      ν (originalOccupationSupport τ (G i)) = ∫⁻ x, B i x ∂ν := by
    dsimp only [B]
    rw [lintegral_indicator (measurableSet_originalOccupationSupport τ (hG i hi))]
    simp
  have hsum (x : X) : (∑ i ∈ F, B i x) =
      ((F.filter fun i => 0 < incidenceDuration τ (G i) univ x).card : ENNReal) := by
    simp only [B, Set.indicator_apply, originalOccupationSupport, mem_ofPred_eq]
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i ∈ F, ∫⁻ x, B i x ∂ν := Finset.sum_congr rfl hmass
    _ = ∫⁻ x, ∑ i ∈ F, B i x ∂ν := (lintegral_finsetSum F hB).symm
    _ ≤ ∫⁻ _x, J ∂ν := lintegral_mono_ae (hcount.mono fun x hx => by rw [hsum]; exact hx)
    _ = J * ν univ := by simp

open scoped Classical in
/-- Only the finite visit count uses existential time witnesses. The
supporting priors themselves remain the measurable positive-duration sets. -/
theorem original_support_prior_budget_of_visits {X T I : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) (τ : Measure T) [SFinite τ]
    (F : Finset I) (G : I → X × T → ENNReal) (hG : ∀ i ∈ F, Measurable (G i))
    (J : ENNReal)
    (hvisits : ∀ᵐ x ∂ν, ((F.filter fun i => ∃ t, G i (x,t) ≠ 0).card : ENNReal) ≤ J) :
    (∑ i ∈ F, ν (originalOccupationSupport τ (G i))) ≤ J * ν univ := by
  classical
  apply original_support_prior_budget ν τ F G hG J
  filter_upwards [hvisits] with x hx
  apply le_trans _ hx
  exact_mod_cast Finset.card_le_card (show
    (F.filter fun i => 0 < incidenceDuration τ (G i) univ x) ⊆
      F.filter (fun i => ∃ t, G i (x,t) ≠ 0) from by
    intro i hi
    obtain ⟨hiF, hipos⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiF, exists_original_occupation τ (G i) x hipos⟩)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
