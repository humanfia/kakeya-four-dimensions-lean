-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/GroupMass.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling.BaseFilling

/-!
# Mass of an intercept group from base filling

A core intercept group `Λ` of trajectories, with incidences that are broad in every base cell
and long in time (prior ceiling `θ Λ ≤ K M / w`), occupies at least `β (w/p)^3 / (A^2 K^9)`
base cells of side `p` (multilinear Kakeya in three base dimensions, `base_incidence_filling`
and `base_support_lower_bound`, adapted from o106/x0352).  If every observation cell (a base
cell together with a hidden bin) that carries counted mass carries at least `mcell`, and every
counted incidence in an observation cell meeting the core group belongs to the enlarged group
`G`, then `G` has counted mass at least `mcell` times the number of occupied base cells.  With
`mcell ≈ g p^3` the cell side cancels.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set
open Submission.Lib.K4ContinuousKakeya
open Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling
open scoped NNReal ENNReal

noncomputable section

/-- **Occupied cells carry the group.**  If distinct occupied base cells each contain an
observation cell of mass at least `mcell` inside `G`, then `G` has mass at least `mcell` times
the number of occupied base cells. -/
theorem mass_ge_card_mul_of_cells {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} (J : Finset ι) (O : ι → Set Ω) (G : Set Ω) (mcell : ℝ≥0∞)
    (hO : ∀ j ∈ J, O j ⊆ G) (hOm : ∀ j ∈ J, MeasurableSet (O j))
    (hdisj : (J : Set ι).PairwiseDisjoint O) (hmass : ∀ j ∈ J, mcell ≤ μ (O j)) :
    (J.card : ℝ≥0∞) * mcell ≤ μ G := by
  calc (J.card : ℝ≥0∞) * mcell = ∑ _j ∈ J, mcell := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ J, μ (O j) := Finset.sum_le_sum hmass
    _ = μ (⋃ j ∈ J, O j) := (measure_biUnion_finset hdisj hOm).symm
    _ ≤ μ G := measure_mono (Set.iUnion₂_subset hO)

/-- **Occupied base cells of a broad, long core group.**  The number of base cells occupied
by the core group is at least `β (w/p)^3 / (A^2 K^9)`, where `β = (ρ/2)^3/2 * c^3`,
`A = 8 C R^3`, the time spent by a trajectory in a cell is at most `K p`, and the prior of the
core group is at most `K M / w` with `M` its counted mass in the cells. -/
theorem occupied_cells_lower_bound {α : Type*} [MeasurableSpace α] {m : ℕ}
    (θ : Measure α) [IsFiniteMeasure θ] (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 3)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 3)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) (anchorBound : ℝ) (hanchor : ∀ l, ‖a l‖ ≤ anchorBound)
    (Λ : Set α) (hΛ : MeasurableSet Λ)
    (E : Fin m → Set (EuclideanSpace ℝ (Fin 3))) (hE : ∀ j, MeasurableSet (E j))
    (hdisj : Pairwise (Function.onFun Disjoint E)) (boxBound : ℝ)
    (hbox : ∀ j, E j ⊆ Metric.closedBall 0 boxBound)
    (p R C ρ c K w : ℝ) (hp : 0 < p) (hR : 0 < R) (hC : 0 ≤ C)
    (hMK : FiniteMK 3 C) (hρ : 0 < ρ) (hc : 0 ≤ c) (hK : 1 ≤ K) (hw : 0 < w)
    (hvol : ∀ j, volume (E j) = ENNReal.ofReal (p ^ 3))
    (hpush : ∀ j, (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤
      (K * p).toNNReal • θ.restrict Λ)
    (htube : ∀ j, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ x ∈ E j,
      x ∈ tube (R * p) (a ω.1) (e ω.1))
    (hbroad : ∀ j, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      c * inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} ≤
        (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).real
          {ω | ρ ≤ Metric.infDist (e ω.1) (V : Set _)})
    (M : ℝ) (hM : 0 < M)
    (hcover : M ≤ ∑ j, inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j})
    (hprior : θ.real Λ ≤ K * M / w) :
    ((ρ / 2) ^ 3 / 2 * c ^ 3) * (w / p) ^ 3 ≤ (m : ℝ) * (8 * C * R ^ 3) ^ 2 * K ^ 9 := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKp : 0 ≤ K * p := by positivity
  have hD : (0 : ℝ≥0) < (K * p).toNNReal := Real.toNNReal_pos.mpr (by positivity)
  have hfill := base_incidence_filling θ inc Φ hΦ a e ha he he1 anchorBound hanchor Λ hΛ E hE
    hdisj boxBound hbox p R C ρ c hp hR hC hMK hρ hc (K * p).toNNReal hD
    hvol hpush htube hbroad
  rw [Real.coe_toNNReal _ hKp] at hfill
  exact base_support_lower_bound (X := ∑ j, inc.real {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j})
    (V := θ.real Λ) (M := M) measureReal_nonneg (by positivity) hM hK0 hp hw (by positivity)
    ((div_le_self hM.le hK).trans hcover) hprior hfill

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
