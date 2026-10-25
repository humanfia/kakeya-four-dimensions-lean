/-
Adapted from this LOT tree, obligation o093, session x0544, commit 8540c65b,
Submission/Obl/k4_scalar_critical_path_terminal/ReadoutSlices.lean.
The current law here uses each actual suffix's own original total mass;
all worlds still come from the SAME retained final law and pullback.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Interface
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SubmeasurePaths

/-! Exact original weighted slices of the actual common final law,
in the literal form required by the measured information-window theorem.
The right sides are expanded Info.tagSlice definitions, keeping this module
independent of the finite entropy library. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open MeasureTheory Set PathGeometry.PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Arbitrary dominated common residuals have these exact weighted
original-world slices. No normalization of the original worlds is made. -/
theorem weighted_submeasureWorldLaw_eq_tagSlice {p z : Code}
    (view : RefinementChain p z) (hz : Exact z) (k : ℕ)
    (P : Measure (Fin (W z k) × State)) (hP : P ≤ normalizedWorldMixture z k)
    (g : Fin (W p (view.sample k))) :
    ENNReal.ofReal (ω p (view.sample k) g) • view.submeasureWorldLaw k P g =
      view.originalLaw k univ •
        (P.restrict {a | (view.pullback k a).1 = g}).map (fun a => (view.pullback k a).2) := by
  have hsnd : Measurable (fun a => (view.pullback k a).2) :=
    measurable_snd.comp (view.measurable_pullback k)
  ext S hS
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [view.submeasureWorldLaw_weighted_apply hz k hP g hS,
    Measure.map_apply hsnd hS, Measure.restrict_apply (hS.preimage hsnd)]
  apply congrArg (fun A : Set (Fin (W z k) × State) => view.originalLaw k univ * P A)
  ext a
  simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq]
  exact and_comm

/-- In particular the selected original within-world laws of the common
core are exactly the slices of that common restricted probability. -/
theorem weighted_selectedWorldLaw_eq_tagSlice {p z : Code}
    (view : RefinementChain p z) (hz : Exact z) (k : ℕ)
    (E : Set (Fin (W z k) × State)) (g : Fin (W p (view.sample k))) :
    ENNReal.ofReal (ω p (view.sample k) g) • view.selectedWorldLaw k E g =
      ENNReal.ofReal ((view.originalLaw k univ).toReal) •
        (((normalizedWorldMixture z k).restrict E).restrict
          {a | (view.pullback k a).1 = g}).map (fun a => (view.pullback k a).2) := by
  have hmass : view.originalLaw k univ ≠ ∞ :=
    (view.originalLaw_mass_le_one hz k).trans_lt (by simp) |>.ne
  rw [ENNReal.ofReal_toReal hmass]
  exact weighted_submeasureWorldLaw_eq_tagSlice view hz k _ Measure.restrict_le_self g

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
