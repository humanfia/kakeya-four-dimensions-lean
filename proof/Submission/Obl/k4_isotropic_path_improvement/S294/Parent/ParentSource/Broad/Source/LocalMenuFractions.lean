-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.LocalMenuFractions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/LocalMenuFractions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit bd47f7155191965c3a5725d07b90bd167e8ca56a,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/LocalMenuFractions.lean.
All earlier source attributions below are retained. -/
import Submission.Lib.K4StateFractionKeep
import Submission.Lib.K4ReferencePruning
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement

/-! # Keeping conditional breadth after a countable world partition

Only a bounded local menu of worlds may meet one original state. The
global world set can be infinite. Removing world-state parts below a
fixed fraction costs the local menu cardinality, while all later ratios
refer to the unchanged original state masses.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalMenuFractions
open MeasureTheory Set
open Submission.Lib.K4ReferencePruning
open Submission.Lib.K4StateFractionKeep
open Submission.Obl.k4_crop_angular_finite_tail
open scoped ENNReal
noncomputable section

variable {Ω I J : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J] [Countable I] [Countable J]

def keep (μ : Measure Ω) (state : Ω → I) (world : Ω → J) (f : ENNReal) : Set Ω :=
  referenceKeep μ (fun x => (world x,state x)) (fun q => μ (state ⁻¹' {q.2})) f

theorem measurableSet_keep (μ : Measure Ω) {state : Ω → I} (hs : Measurable state)
    {world : Ω → J} (hw : Measurable world) (f : ENNReal) :
    MeasurableSet (keep μ state world f) :=
  measurableSet_referenceKeep μ _ (hw.prodMk hs) _ f

theorem keep_world (μ : Measure Ω) (state : Ω → I) (world : Ω → J)
    (f : ENNReal) (j : J) :
    keep μ state world f ∩ world ⁻¹' {j} =
      fractionKeep μ state (world ⁻¹' {j}) f := by
  ext x
  have hfiber : (fun x => (world x,state x)) ⁻¹' {(world x,state x)} =
      world ⁻¹' {world x} ∩ state ⁻¹' {state x} := by
    ext y
    simp
  simp only [keep,referenceKeep,fractionKeep,goodStates,mem_inter_iff,mem_preimage,
    mem_singleton_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨hkeep,hworld⟩
    refine ⟨hworld,?_⟩
    rw [hfiber,hworld] at hkeep
    exact hkeep
  · rintro ⟨hworld,hkeep⟩
    refine ⟨?_,hworld⟩
    rw [hfiber,hworld]
    exact hkeep

/-- All the world parts are pruned at once. The cost depends on how many
worlds meet each state, rather than the total number of worlds. -/
theorem deletion_le (μ : Measure Ω) {state : Ω → I} (hs : Measurable state)
    {world : Ω → J} (_hw : Measurable world) (menu : I → Finset J)
    (hsupport : ∀ᵐ x ∂μ, world x∈menu (state x)) (M f : ENNReal)
    (hmenu : ∀ i, ((menu i).card:ENNReal) ≤ M) :
    μ (keep μ state world f)ᶜ ≤ (f*M)*μ univ := by
  classical
  let code := fun x => (world x,state x)
  let w := fun q : J×I => if q.1∈menu q.2 then μ (state ⁻¹' {q.2}) else 0
  have heq : keep μ state world f =ᵐ[μ] referenceKeep μ code w f := by
    filter_upwards [hsupport] with x hx
    simp only [keep,referenceKeep,mem_ofPred_eq,code,w,ite_eq_left hx]
  have hsum : (∑' q : J×I, w q) ≤ M*μ univ := by
    have hh := Submission.Obl.k4_scalar_graph_residual_discovery.listed_reference_sum_le
      menu (fun i => μ (state ⁻¹' {i})) M hmenu
    have htotal : (∑' i : I, μ (state ⁻¹' {i})) = μ univ := by
      simpa only [univ_inter] using (measure_eq_tsum_label μ hs MeasurableSet.univ).symm
    simpa only [w,htotal] using hh
  calc
    _ = μ (referenceKeep μ code w f)ᶜ := measure_congr heq.compl
    _ ≤ f*∑' q : J×I, w q := reference_light_mass_le μ code w f
    _ ≤ f*(M*μ univ) := mul_le_mul' le_rfl hsum
    _ = _ := by ring

/-- An arbitrary original per-state ratio passes to every retained world
with exactly the reciprocal fraction loss. -/
theorem state_ratio (μ : Measure Ω) (state : Ω → I) (world : Ω → J)
    {f : ENNReal} (hf0 : f≠0) (hftop : f≠∞) (j : J) (S : Set Ω) (η : ENNReal)
    (hη : ∀ i, μ (state ⁻¹' {i} ∩ S) ≤ η*μ (state ⁻¹' {i})) (i : I) :
    μ (keep μ state world f ∩ world ⁻¹' {j} ∩ state ⁻¹' {i} ∩ S) ≤
      (η/f)*μ (keep μ state world f ∩ world ⁻¹' {j} ∩ state ⁻¹' {i}) := by
  rw [keep_world]
  exact fractionKeep_state_ratio μ state (world ⁻¹' {j}) hf0 hftop S η hη i

/-- Ratios also hold on every measurable union of original states. -/
theorem union_ratio (μ : Measure Ω) {state : Ω → I} (hs : Measurable state)
    {world : Ω → J} (hw : Measurable world)
    {f : ENNReal} (hf0 : f≠0) (hftop : f≠∞) (j : J)
    {S : Set Ω} (hS : MeasurableSet S) (η : ENNReal)
    (hη : ∀ i, μ (state ⁻¹' {i} ∩ S) ≤ η*μ (state ⁻¹' {i})) (L : Set I) :
    μ (keep μ state world f ∩ world ⁻¹' {j} ∩ state ⁻¹' L ∩ S) ≤
      (η/f)*μ (keep μ state world f ∩ world ⁻¹' {j} ∩ state ⁻¹' L) := by
  rw [keep_world]
  exact fractionKeep_union_ratio μ hs (hw (measurableSet_singleton j)) hf0 hftop hS η hη L

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalMenuFractions
