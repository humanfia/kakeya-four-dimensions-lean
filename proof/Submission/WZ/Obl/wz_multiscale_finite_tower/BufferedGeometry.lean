-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.BufferedGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Hierarchy
import Submission.WZ.Obl.wz_multiscale_finite_tower.GridCapacity

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_flat_factored_improvement (gridHull)

/-- A narrow tube controls its axis, and therefore every wider tube on that axis. -/
lemma tube_enlarge_from_axis {d r R : ℝ} (hd : 0 < d) {x v y w : Space}
    (h : Tube d x v ⊆ Tube r y w) : Tube R x v ⊆ Tube (r + R) y w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hqd : q ∈ Tube d x v := self_subset_thickening hd _ hq
  obtain ⟨z, hz, hqz⟩ := mem_thickening_iff.mp (h hqd)
  exact mem_thickening_iff.mpr ⟨z, hz, (dist_triangle p q z).trans_lt (by linarith)⟩

lemma buffered_tube_containment {d r R : ℝ} (hd : 0 < d) (hR : R ≤ r / 64)
    {x v y w : Space} (h : Tube d x v ⊆ Tube ((31 / 32) * r) y w) :
    Tube R x v ⊆ Tube ((63 / 64) * r) y w :=
  (tube_enlarge_from_axis hd h).trans (thickening_mono (by linarith) _)

lemma gridHull_mono_set {a : ℝ} (S : Finset (Fin 3 → ℤ)) {U V : Set Space}
    (h : U ⊆ V) : gridHull a S U ⊆ gridHull a S V := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  exact mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hz).1, q, h hq, hqz⟩, hpz⟩

/-- The spare radius around an axis accommodates a grid shadow without changing
the scale at which the local analytic hypothesis is used. -/
lemma buffered_gridHull_containment {a r : ℝ} (ha : 0 < a) (har : 2 * a ≤ r / 64)
    (S : Finset (Fin 3 → ℤ)) {U : Set Space} {y w : Space}
    (hU : U ⊆ Tube ((63 / 64) * r) y w) :
    gridHull a S U ⊆ Tube r y w :=
  (gridHull_mono_set S hU).trans ((gridHull_tube_subset ha S y w).trans
    (thickening_mono (by linarith) _))

end WangZahlLot.Obl.wz_multiscale_finite_tower
