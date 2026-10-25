import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartPacketFloors

/-! Original whole-world packets may be included in the SAME simultaneous
floor pruning as all chart packets. They give a zero-or-positive mass
alternative for every normalized velocity palette. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

namespace PacketSample

/-- The original weights pay for the full worlds, independently of their
number, just as they pay for full assigned chart packets. -/
def worlds {p : Code} (hp : Exact p) (k : ℕ) : PacketSample p k where
  count := W p k
  world := id
  assignment _ := univ
  timeBlock _ := univ
  duration := 1
  measurable_assignment _ := MeasurableSet.univ
  measurable_timeBlock _ := MeasurableSet.univ
  budget := by
    have hν (g : Fin (W p k)) : ν p k g univ = 1 := by
      letI : IsProbabilityMeasure (ν p k g) := ((hp.2.1 k).2.2.2.1 g).1
      exact measure_univ
    simp only [id_eq, ENNReal.ofReal_one, mul_one, hν]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => (hp.2.1 k).2.1 g), (hp.2.1 k).2.2.1]
    norm_num

end PacketSample

namespace PacketFamily

def worlds {p z : Code} (hp : Exact p) (view : RefinementChain p z) : PacketFamily z :=
  ofSamples view (fun k => PacketSample.worlds hp (view.sample k))

end PacketFamily

/-- A common residual that misses a whole original world gives its
original within-world law zero mass, even if the original weight is zero. -/
theorem current_world_zero_of_cell_empty {p z : Code} (view : RefinementChain p z)
    (k : ℕ) (η : Measure (Fin (W z k) × State))
    (E : Set (Fin (W z k) × State)) (g : Fin (W p (view.sample k)))
    (hempty : E ∩ (view.pullback k ⁻¹' ({g} ×ˢ (univ : Set State))) = ∅) :
    view.submeasureWorldLaw k (η.restrict E) g = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [RefinementChain.submeasureWorldLaw, originalFibers, Measure.smul_apply,
    worldFiber_apply _ _ MeasurableSet.univ, RefinementChain.submeasureLaw,
    Measure.smul_apply, Measure.map_apply (view.measurable_pullback k)
      ((measurableSet_singleton g).prod MeasurableSet.univ),
    Measure.restrict_apply (((measurableSet_singleton g).prod MeasurableSet.univ).preimage
      (view.measurable_pullback k)), inter_comm, hempty, measure_empty]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Read the whole-world floor alternatives produced by the generic
simultaneous pruning theorem. No subsequent pruning is needed. -/
theorem current_world_floor_cases {p z : Code} (hp : Exact p) (hz : Exact z)
    (view : RefinementChain p z) (k : ℕ) (H : ℝ) (hH : 0 < H)
    (η : Measure (Fin (W z k) × State)) (hη : η ≤ normalizedWorldMixture z k)
    (E : Set (Fin (W z k) × State))
    (hfloors : ∀ i : (PacketFamily.worlds hp view).Index k,
      0 < ω p (view.sample k) ((PacketFamily.worlds hp view).world k i) →
      E ∩ (PacketFamily.worlds hp view).cell k i = ∅ ∨
        (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal ((PacketFamily.worlds hp view).duration k) *
          ν p (view.sample k) ((PacketFamily.worlds hp view).world k i)
            ((PacketFamily.worlds hp view).assignment k i) ≤
          view.submeasureWorldLaw k (η.restrict E) ((PacketFamily.worlds hp view).world k i)
            ((PacketFamily.worlds hp view).priorCell k i))
    (g : Fin (W p (view.sample k))) :
    view.submeasureWorldLaw k (η.restrict E) g = 0 ∨
      ENNReal.ofReal H⁻¹ ≤ view.submeasureWorldLaw k (η.restrict E) g univ := by
  by_cases hω : 0 < ω p (view.sample k) g
  · rcases hfloors g hω with hempty | hfloor
    · apply Or.inl
      apply current_world_zero_of_cell_empty view k η E g
      simpa only [PacketFamily.worlds, PacketFamily.ofSamples, PacketSample.worlds,
        PacketFamily.cell, PacketFamily.priorCell, id_eq, univ_prod_univ] using hempty
    · right
      have hν : ν p (view.sample k) g univ = 1 := by
        letI : IsProbabilityMeasure (ν p (view.sample k) g) :=
          ((hp.2.1 (view.sample k)).2.2.2.1 g).1
        exact measure_univ
      simpa only [PacketFamily.worlds, PacketFamily.ofSamples, PacketSample.worlds,
        PacketFamily.priorCell, id_eq, ENNReal.ofReal_one, mul_one, hν, univ_prod_univ,
        ENNReal.ofReal_inv_of_pos hH] using hfloor
  · left
    have hzero : ENNReal.ofReal (ω p (view.sample k) g) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hω)
    have hf := worldFiber_eq_zero_of_weight_zero
      (view.submeasureLaw_le_originalReference hz k
        ((Measure.restrict_le_self : η.restrict E ≤ η).trans hη)) g hzero
    rw [RefinementChain.submeasureWorldLaw, originalFibers, hf, smul_zero]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
