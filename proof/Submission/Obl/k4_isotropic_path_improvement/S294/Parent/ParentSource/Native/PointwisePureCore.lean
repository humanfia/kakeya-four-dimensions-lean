-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PointwisePureCore, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PointwisePureCore.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PointwisePureCore.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PointwisePureCore.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniformPurePreparation

/-! At a depth supplied by the path, the uniform almost-everywhere pure
ceiling has a measurable pointwise representative. Passing to this core
leaves the entire restricted original law unchanged. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ ε : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)

theorem PreparedAngularPath.exists_pointwise_pure_core (hd : d.Valid)
    (hQ : Q.uniformPureCeiling ε)
    (J : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hJ : ∀ w, MeasurableSet (J w)) (hJE : ∀ w, J w ⊆ d.E k w)
    (hJbase : ∀ w, J w ⊆ Q.base w) {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ d.L) :
    ∃ J' : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (J' w)) ∧ (∀ w, J' w ⊆ J w) ∧
      (∀ w, (((d.ν k w).prod volume).restrict (J' w)) =
        (((d.ν k w).prod volume).restrict (J w))) ∧
      ∀ w z, z ∈ J' w → d.g k w r (obs (d.B k w) (δ (d.N k) r) z) ≤
        ENNReal.ofReal (d.N k ^ (-d.f r + τ + ε)) := by
  let Good := fun w => {z | d.g k w r (obs (d.B k w) (δ (d.N k) r) z) ≤
    ENNReal.ofReal (d.N k ^ (-d.f r + τ + ε))}
  have hGood (w : Fin (d.W k)) : MeasurableSet (Good w) := by
    have hg := (hd.2.2.2.2.2.2.2.2.2.1 k w r hr hrL).1
    have hobs : Measurable (obs (d.B k w) (δ (d.N k) r)) :=
      Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_pureObservation _ _
    exact measurableSet_le (hg.comp hobs) measurable_const
  have hfull (w : Fin (d.W k)) :
      ∀ᵐ z ∂(((d.ν k w).prod volume).restrict (J w)), z ∈ Good w := by
    apply hQ w (((d.ν k w).prod volume).restrict (J w))
      (Measure.restrict_mono_set ((d.ν k w).prod volume) (hJE w)) _ r hr hrL
    exact (ae_restrict_mem (hJ w)).mono fun z hz => hJbase w hz
  refine ⟨fun w => J w ∩ Good w, fun w => (hJ w).inter (hGood w),
    fun _ => inter_subset_left, ?_, fun _ _ hz => hz.2⟩
  intro w
  calc
    _ = (((d.ν k w).prod volume).restrict (J w)).restrict (Good w) := by
      rw [Measure.restrict_restrict (hGood w), inter_comm]
    _ = _ := Measure.restrict_eq_self_of_ae_mem (hfull w)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
