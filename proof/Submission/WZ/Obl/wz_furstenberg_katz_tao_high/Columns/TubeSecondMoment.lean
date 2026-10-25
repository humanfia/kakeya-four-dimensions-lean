-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.TubeSecondMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.WideStripSecondMoment
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.PrunedEnergy

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Transfer a pin incidence through a coarse tube assignment. The width
of the original class remains arbitrary. -/
theorem assigned_tube_incidence {p : E2} {j t : E2 × E2} {ι Δ : ℝ}
    (hp : ‖p‖ ≤ 4) (hj : ‖j.1‖ ≤ 4)
    (hpin : |inner ℝ (p - j.1) j.2| < ι)
    (hoff : |inner ℝ (j.1 - t.1) t.2| < 9 * Δ)
    (hangle : dist j.2 t.2 < Δ ∨ dist j.2 (-t.2) < Δ) :
    |inner ℝ (p - t.1) t.2| < ι + 17 * Δ := by
  have hnorm : ‖p - j.1‖ ≤ 8 := (norm_sub_le _ _).trans (by linarith)
  have hperturb : ∀ e : E2, |inner ℝ (p - j.1) e| < ι → ‖t.2 - e‖ < Δ →
      |inner ℝ (p - j.1) t.2| < ι + 8 * Δ := by
    intro e he hd
    have hh : |inner ℝ (p - j.1) (t.2 - e)| < 8 * Δ := by
      calc
        _ ≤ ‖p - j.1‖ * ‖t.2 - e‖ := abs_real_inner_le_norm _ _
        _ ≤ 8 * ‖t.2 - e‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ < 8 * Δ := by linarith
    have heq : inner ℝ (p - j.1) t.2 =
        inner ℝ (p - j.1) e + inner ℝ (p - j.1) (t.2 - e) := by
      rw [inner_sub_right]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_lt (by linarith)
  have hfirst : |inner ℝ (p - j.1) t.2| < ι + 8 * Δ := by
    rcases hangle with ha | ha
    · exact hperturb j.2 hpin (by simpa only [← dist_eq_norm, dist_comm] using ha)
    · exact hperturb (-j.2) (by simpa only [inner_neg_right, abs_neg] using hpin)
        (by simpa only [dist_eq_norm, sub_neg_eq_add, add_comm] using ha)
  have heq : p - t.1 = (p - j.1) + (j.1 - t.1) := by abel
  rw [heq, inner_add_left]
  exact (abs_add_le _ _).trans_lt (by linarith)

/-- Count occupied cells using one injectively assigned representative per
cell. The tubes may be any separated family, including a maximal family. -/
theorem tube_cells_second_moment {ι : Type*} [DecidableEq ι]
    (D J : Finset (E2 × E2)) (cls tube : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (point : ι → E2)
    (hP : P.Nonempty) (hinj : Set.InjOn point (↑(P.image cell) : Set ι))
    {r w C : ℝ} (hr : 0 < r) (hrw : r ≤ w) (hw2 : w ≤ 1 / 2) (hC : 0 ≤ C)
    (hpoint : ∀ c ∈ P.image cell, ‖point c‖ ≤ 4)
    (hFr : ∀ x ρ, r ≤ ρ →
      ((((P.image cell).image point).filter (fun y => y ∈ Metric.closedBall x ρ)).card : ℝ) ≤
        C * ρ * (P.image cell).card)
    (hT : ∀ t ∈ J.image tube, ‖t.1‖ ≤ 4 ∧ ‖t.2‖ = 1)
    (hsep : (J.image tube : Set (E2 × E2)).Pairwise
      (WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep r))
    (hinc : ∀ t ∈ J.image tube, ∀ c ∈ tubeCells D cls P cell J tube t,
      |inner ℝ (point c - t.1) t.2| < w)
    (K : ℕ) (hK : ((P.image cell).card : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ t ∈ J.image tube, ((tubeCells D cls P cell J tube t).card : ℝ) ^ 2) ≤
      64000 * (64 * w / r + 2) * (36 * w / r + 2) *
        C * (1 + Real.log (1 / w)) * (2 * K + 1) * ((P.image cell).card : ℝ) ^ 2 := by
  classical
  let Y := (P.image cell).image point
  have hcard : Y.card = (P.image cell).card := Finset.card_image_of_injOn hinj
  have hsub : ∀ t, tubeCells D cls P cell J tube t ⊆ P.image cell := by
    intro t c hc
    obtain ⟨j, hj, hcj⟩ := Finset.mem_biUnion.mp hc
    exact cellsHit_subset D cls P cell j hcj
  have hdeg : ∀ t ∈ J.image tube, (tubeCells D cls P cell J tube t).card ≤
      (Y.filter (fun y => |inner ℝ (y - t.1) t.2| < w)).card := by
    intro t ht
    have hmap : (tubeCells D cls P cell J tube t).image point ⊆
        Y.filter (fun y => |inner ℝ (y - t.1) t.2| < w) := by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem point (hsub t hc), hinc t ht c hc⟩
    have hh := Finset.card_le_card hmap
    rwa [Finset.card_image_of_injOn (hinj.mono (hsub t))] at hh
  have hh := wide_strip_second_moment hr hrw hw2 hC Y ((hP.image cell).image point)
    (by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
      exact hpoint c hc)
    (by simpa only [hcard] using hFr)
    (J.image tube) hT hsep K (by simpa only [hcard] using hK)
    (fun t => (tubeCells D cls P cell J tube t).card) hdeg
  simpa only [hcard] using hh

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
