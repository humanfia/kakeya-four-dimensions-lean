-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.TwoLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/TwoLevel.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.CommonCut

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/TwoLevel.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount)

/-- One side of a measurable fibrewise partition retains at least half the fine mass. -/
theorem half_mass_fibre_cut {n N : ℕ} (f : Fin n → Fin N) (U : Fin n → Set V)
    (D : Fin N → Set V) (hD : ∀ k, MeasurableSet (D k)) :
    O (1 / 2) * ∑ i, μ (U i) ≤ ∑ i, μ (U i ∩ D (f i)) ∨
      O (1 / 2) * ∑ i, μ (U i) ≤ ∑ i, μ (U i ∩ (D (f i))ᶜ) := by
  have hsplit : (∑ i, μ (U i ∩ D (f i))) + (∑ i, μ (U i ∩ (D (f i))ᶜ)) =
      ∑ i, μ (U i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => measure_inter_add_sdiff (U i) (hD (f i))
  have he : O (1 / 2) * (∑ i, μ (U i)) + O (1 / 2) * (∑ i, μ (U i)) =
      ∑ i, μ (U i) := by
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num [O]
  by_contra hn
  push Not at hn
  have hlt := ENNReal.add_lt_add hn.1 hn.2
  rw [he, hsplit] at hlt
  exact lt_irrefl _ hlt

/-- A factor-four multiplicity window is reduced to a common factor-two window
by one of two common cuts, at a cost of at most half the fine mass. -/
theorem two_level_fibre_cut {n N : ℕ} (f : Fin n → Fin N) (U : Fin n → Set V)
    {m : ℝ} (hm : 0 < m) (hU : ∀ i, MeasurableSet (U i))
    (hlevel : ∀ k p, p ∈ assignedFiber f U k →
      m / 2 ≤ fiberBodyCount f U k p ∧ fiberBodyCount f U k p ≤ 2 * m) :
    ∃ (m' : ℝ) (D : Fin N → Set V), 0 < m' ∧ m' ≤ m ∧
      (∀ k, MeasurableSet (D k)) ∧
      O (1 / 2) * ∑ i, μ (U i) ≤ ∑ i, μ (U i ∩ D (f i)) ∧
      ∀ k p, p ∈ assignedFiber f (fun i => U i ∩ D (f i)) k →
        m' ≤ fiberBodyCount f (fun i => U i ∩ D (f i)) k p ∧
        fiberBodyCount f (fun i => U i ∩ D (f i)) k p ≤ 2 * m' := by
  classical
  let A (k : Fin N) : Set V := {p | m ≤ fiberBodyCount f U k p}
  have hA (k : Fin N) : MeasurableSet (A k) := by
    apply measurableSet_le measurable_const
    exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hU i)
  rcases half_mass_fibre_cut f U A hA with hhigh | hlow
  · refine ⟨m, A, hm, le_rfl, hA, hhigh, ?_⟩
    intro k p hp
    have hp' : p ∈ assignedFiber f U k ∩ A k := by
      rwa [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_common_cut] at hp
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.fiberBodyCount_restrict,
      indicator_of_mem hp'.2]
    exact ⟨hp'.2, (hlevel k p hp'.1).2⟩
  · refine ⟨m / 2, (fun k => (A k)ᶜ), by positivity, by linarith,
      (fun k => (hA k).compl), hlow, ?_⟩
    intro k p hp
    have hp' : p ∈ assignedFiber f U k ∩ (A k)ᶜ := by
      rwa [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_common_cut
        f U (fun k => (A k)ᶜ) k] at hp
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.fiberBodyCount_restrict
      f U (fun k => (A k)ᶜ) k p, indicator_of_mem hp'.2]
    have hn : ¬ m ≤ fiberBodyCount f U k p := hp'.2
    exact ⟨(hlevel k p hp'.1).1, by linarith⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
