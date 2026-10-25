-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.WindowClusterOrder.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.CurvatureOrder
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.TimeWindowCover

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- One contact orients all cross curvatures of two refined coefficient
clusters on the whole short window. -/
theorem window_cluster_curvature_order {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) {D δ η l u : ℝ}
    (hD : 0 < D) (hδ : δ < D/480) (hη : η < D/480)
    (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u-l ≤ 1/10000)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D/10000)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D/10000)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j))
    (hcontact : ∃ i ∈ A, ∃ j ∈ B, ∃ x ∈ Icc l u, NearContact δ η (g i) (g j) x) :
    (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
      D/120 ≤ deriv (deriv (g i)) t-deriv (deriv (g j)) t) ∨
    (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
      D/120 ≤ deriv (deriv (g j)) t-deriv (deriv (g i)) t) := by
  obtain ⟨i, hi, j, hj, x, hx, hc⟩ := hcontact
  have hsub : Icc l u ⊆ Icc (-1:ℝ) 1 := fun _ ht => ⟨hl.trans ht.1, ht.2.trans hu⟩
  have hclose : ∀ t ∈ Icc l u, |t-x| ≤ 1/10000 := by
    intro t ht
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
  obtain ⟨σ, hσ, hord⟩ := cluster_curvature_order hg hjet i j hD (hcross i hi j hj)
    hδ hη (convex_Icc l u).isPreconnected hsub hx hclose hc
  rcases hσ with rfl | rfl
  · left
    intro a ha b hb t ht
    simpa only [one_mul] using hord a b (hA a ha i hi) (hB b hb j hj) t ht
  · right
    intro a ha b hb t ht
    have hh := hord a b (hA a ha i hi) (hB b hb j hj) t ht
    linarith

/-- Diameter refinement controls curvature differences within each color. -/
theorem within_curvature_le_of_coefficient_diameter {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hjet : JetControlled q g) (A : Finset (Fin n)) {ρ : ℝ}
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ ρ) :
    ∀ i ∈ A, ∀ j ∈ A, ∀ t ∈ Icc (-1:ℝ) 1,
      |deriv (deriv (g i)) t-deriv (deriv (g j)) t| ≤ 19*ρ := by
  intro i hi j hj t ht
  have hh := (deriv2_le_jetDistance (g i) (g j) t).trans (hjet i j t ht).2
  linarith [hA i hi j hj]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
