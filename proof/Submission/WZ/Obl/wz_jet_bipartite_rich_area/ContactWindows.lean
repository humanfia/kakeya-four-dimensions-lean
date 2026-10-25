-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactWindows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGeometry

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- A contact persists across a short band around the reference graph.
The separate linear and quadratic scale conditions retain contacts whose
slope gap is larger than the natural square-root scale. -/
theorem contact_band_value_le {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (i a : Fin n) {δ κ D L w z u : ℝ}
    (_hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hupper : dist (q i) (q a) ≤ 2 * D)
    (hw : w ∈ Icc (-1 : ℝ) 1) (hz : z ∈ Icc (-1 : ℝ) 1)
    (htime : |z - w| ≤ L) (hwidth : |u - g a z| ≤ δ)
    (hc : NearContact (2 * δ) (4 * κ * D) (g i) (g a) w)
    (hlinear : κ * D * L ≤ δ) (hquadratic : D * L ^ 2 ≤ δ) :
    |u - g i z| ≤ 45 * δ := by
  have hvar := value_difference_near_contact hg hjet i a hz hw hc.2
  have hcoef : 19 * dist (q i) (q a) ≤ 38 * D := by linarith
  have hmon : (4 * κ * D + 19 * dist (q i) (q a) * |z - w|) * |z - w| ≤
      (4 * κ * D + 38 * D * L) * L := by
    apply mul_le_mul _ htime (abs_nonneg _) (by positivity)
    apply add_le_add le_rfl
    exact (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left htime (by positivity))
  have hgap : |g i z - g a z| ≤ 44 * δ := by
    have ht := abs_sub_le (g i z - g a z) (g i w - g a w) 0
    simp only [sub_zero] at ht
    have hbase := hc.1
    have hscaled : (4 * κ * D + 38 * D * L) * L ≤ 42 * δ := by
      nlinarith
    linarith
  have ht := abs_sub_le u (g a z) (g i z)
  rw [abs_sub_comm (g a z) (g i z)] at ht
  linarith

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
