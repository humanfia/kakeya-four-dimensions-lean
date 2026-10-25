-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripProjectionCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripProjectionGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem strip_transverse_projection_count {δ C d c t : ℝ} {a b e : Plane}
    {G T : Finset Plane} (hδ : 0 < δ) (hδt : δ ≤ t) (hC : 0 < C)
    (he : ‖e‖ = 1) (ha : ‖a‖ ≤ 4) (hA : 0 < |inner ℝ a e|)
    (hG : ClosedFiniteFrostman δ C G) (hTG : T ⊆ G) (hTne : T.Nonempty)
    (hdensity : d * (G.card : ℝ) ≤ (T.card : ℝ))
    (hstrip : ∀ x ∈ T, |inner ℝ x (perp e) - c| ≤ t) :
    CoverLower t ((fun x => inner ℝ a (x - b)) '' (↑T : Set Plane))
      (d * |inner ℝ a e| / (18 * C * t)) := by
  classical
  have ht : 0 < t := hδ.trans_le hδt
  have hAe : |inner ℝ a e| ≤ 4 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using ha)
  let R := 18 * t / |inner ℝ a e|
  have hR : 0 < R := by dsimp [R]; positivity
  have hδR : δ ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ hA).mpr
    nlinarith [mul_le_mul_of_nonneg_left hAe hδ.le]
  have hGpos : (0 : ℝ) < G.card := by
    exact_mod_cast Finset.card_pos.mpr (hTne.mono hTG)
  intro m cc hc
  have hcount : (T.card : ℝ) ≤ (m : ℝ) * (C * R * (G.card : ℝ)) := by
    apply card_le_cover_mul_fiber_bound T (fun x => inner ℝ a (x - b)) hc
    intro j
    apply hG.card_of_diameter ((Finset.filter_subset _ _).trans hTG) hC.le hR.le hδR
    intro x hx y hy
    obtain ⟨hxT, hxc⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyT, hyc⟩ := Finset.mem_filter.mp hy
    apply strip_dot_diameter he ha ht.le hA (hstrip x hxT) (hstrip y hyT)
    have hdist := dist_triangle_right (inner ℝ a (x - b)) (inner ℝ a (y - b)) (cc j)
    have hid : inner ℝ a (x - y) = inner ℝ a (x - b) - inner ℝ a (y - b) := by
      simp only [inner_sub_right]
      ring
    rw [hid, ← Real.dist_eq]
    exact hdist.trans (by linarith)
  have hd : d ≤ (m : ℝ) * (C * R) := by
    apply (mul_le_mul_iff_left₀ hGpos).mp
    calc d * (G.card : ℝ) ≤ (T.card : ℝ) := hdensity
      _ ≤ (m : ℝ) * (C * R * (G.card : ℝ)) := hcount
      _ = ((m : ℝ) * (C * R)) * (G.card : ℝ) := by ring
  calc d * |inner ℝ a e| / (18 * C * t) = d / (C * R) := by dsimp [R]; field_simp <;> ring
    _ ≤ (m : ℝ) := (div_le_iff₀ (mul_pos hC hR)).mpr (by nlinarith)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
