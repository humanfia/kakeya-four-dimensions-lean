-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormContain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSGeometry

/-!
# Containment of zoomed pieces

If a fine unit tube lies in a coarse unit tube of radius `ρ`, and the zoom centre is close to
the fine axis, then the zoomed piece of the fine tube lies in the zoomed piece of the coarse
tube thickened to radius `25 lam ρ`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

theorem foot_reverse {c z w : Space} (hw : ‖w‖ = 1) : foot c (z + w) (-w) = foot c z w := by
  have h1 : inner ℝ (c - (z + w)) (-w) = -(inner ℝ (c - z) w - 1) := by
    rw [inner_neg_right, show c - (z + w) = (c - z) - w by abel, inner_sub_left,
      real_inner_self_eq_norm_sq, hw]
    ring
  simp only [foot]
  rw [h1]
  module

theorem pieceStart_reverse {c z w : Space} (hw : ‖w‖ = 1) (lam : ℝ) :
    pieceStart c lam (z + w) (-w) = pieceStart c lam z w + w := by
  simp only [pieceStart, foot_reverse hw]
  module

theorem piece_reverse {c z w : Space} (hw : ‖w‖ = 1) (lam R : ℝ) :
    tube R (pieceStart c lam (z + w) (-w)) (-w) = tube R (pieceStart c lam z w) w := by
  rw [pieceStart_reverse hw, tube_reverse]

/-- A point of the zoomed piece is the zoom of a point on the original sub-segment, up to an
error of size `lam δ`. -/
theorem piece_point {c : Space} {lam δ : ℝ} (hlam : 0 < lam) {x v q : Space}
    (hq : q ∈ tube (lam * δ) (pieceStart c lam x v) v) :
    ∃ s : ℝ, |s| ≤ 1 / (2 * lam) ∧
      ‖q - lam • (x + (inner ℝ (c - x) v + s) • v - c)‖ < lam * δ := by
  obtain ⟨t, ht, hqt⟩ := mem_tube_iff.mp hq
  refine ⟨(t - 1 / 2) / lam, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hlam, div_le_div_iff₀ hlam (by positivity)]
    have : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    nlinarith [abs_nonneg (t - 1 / 2)]
  · have he : lam • (x + (inner ℝ (c - x) v + (t - 1 / 2) / lam) • v - c) =
        pieceStart c lam x v + t • v := by
      simp only [pieceStart, foot, add_smul, smul_add, smul_sub, smul_smul]
      rw [show lam * ((t - 1 / 2) / lam) = t - 1 / 2 by field_simp]
      module
    rwa [he]

/-- Same-orientation case of the containment of zoomed pieces. -/
theorem piece_subset_piece_aux {c : Space} {lam δ ρ r₁ : ℝ} (hlam : 0 < lam) (hδρ : δ ≤ ρ)
    {x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h0 : ‖x - z‖ ≤ 3 * ρ) (h1 : ‖x + v - (z + w)‖ ≤ 3 * ρ)
    (hτ : inner ℝ (c - x) v ∈ Icc (-r₁) (1 + r₁)) (hr₁ : r₁ + 1 / (2 * lam) ≤ 1)
    (hcx : ‖c - x‖ ≤ 2) :
    tube (lam * δ) (pieceStart c lam x v) v ⊆ tube (lam * (25 * ρ)) (pieceStart c lam z w) w := by
  intro q hq
  obtain ⟨s, hs, hqs⟩ := piece_point hlam hq
  have hρ0 : 0 ≤ ρ := by
    have := norm_nonneg (x - z); linarith
  set τx := inner ℝ (c - x) v with hτx
  set τz := inner ℝ (c - z) w with hτz
  set u := τx + s with hu
  have hu1 : u ∈ Icc (-1 : ℝ) 2 := by
    obtain ⟨hs1, hs2⟩ := abs_le.mp hs
    constructor <;> linarith [hτ.1, hτ.2]
  -- the point `b` of the coarse line at the same parameter
  have hab : ‖(x + u • v) - (z + u • w)‖ ≤ 9 * ρ := by
    have he : (x + u • v) - (z + u • w) = (1 - u) • (x - z) + u • (x + v - (z + w)) := by
      module
    rw [he]
    calc ‖(1 - u) • (x - z) + u • (x + v - (z + w))‖ ≤
          ‖(1 - u) • (x - z)‖ + ‖u • (x + v - (z + w))‖ := norm_add_le _ _
      _ = |1 - u| * ‖x - z‖ + |u| * ‖x + v - (z + w)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |1 - u| * (3 * ρ) + |u| * (3 * ρ) := by gcongr
      _ = (|1 - u| + |u|) * (3 * ρ) := by ring
      _ ≤ 3 * (3 * ρ) := by
          gcongr
          rcases le_total 0 u with h | h
          · rcases le_total u 1 with h' | h'
            · rw [abs_of_nonneg (by linarith), abs_of_nonneg h]; linarith
            · rw [abs_of_nonpos (by linarith), abs_of_nonneg h]; linarith [hu1.2]
          · rw [abs_of_nonneg (by linarith), abs_of_nonpos h]; linarith [hu1.1]
      _ = 9 * ρ := by ring
  have hvw : ‖v - w‖ ≤ 6 * ρ := by
    have he : v - w = (x + v - (z + w)) - (x - z) := by abel
    rw [he]
    calc ‖(x + v - (z + w)) - (x - z)‖ ≤ ‖x + v - (z + w)‖ + ‖x - z‖ := norm_sub_le _ _
      _ ≤ 6 * ρ := by linarith
  have hττ : |τx - τz| ≤ 15 * ρ := by
    have he : τx - τz = inner ℝ (c - x) (v - w) + inner ℝ (z - x) w := by
      rw [hτx, hτz, inner_sub_right]
      have : inner ℝ (c - z) w = inner ℝ (c - x) w - inner ℝ (z - x) w := by
        rw [← inner_sub_left]; congr 1; abel
      rw [this]; ring
    rw [he]
    calc |inner ℝ (c - x) (v - w) + inner ℝ (z - x) w| ≤
          |inner ℝ (c - x) (v - w)| + |inner ℝ (z - x) w| := abs_add_le _ _
      _ ≤ ‖c - x‖ * ‖v - w‖ + ‖z - x‖ * ‖w‖ := by
          gcongr
          · exact abs_real_inner_le_norm _ _
          · exact abs_real_inner_le_norm _ _
      _ ≤ 2 * (6 * ρ) + 3 * ρ * 1 := by
          gcongr
          · rw [norm_sub_rev]; exact h0
          · rw [hw]
      _ = 15 * ρ := by ring
  -- clamp the parameter into the coarse piece
  set h := 1 / (2 * lam) with hh
  have hh0 : 0 < h := by positivity
  set s' := max (-h) (min h (u - τz)) with hs'
  have hs'1 : |s'| ≤ h := by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hclamp : |u - τz - s'| ≤ |τx - τz| := by
    have hus : u - τz = s + (τx - τz) := by rw [hu]; ring
    obtain ⟨hs1, hs2⟩ := abs_le.mp hs
    rcases le_total (u - τz) (-h) with hlo | hlo
    · have : s' = -h := by
        rw [hs']; apply max_eq_left; exact (min_le_right _ _).trans hlo
      rw [this, abs_le]
      constructor <;> cases abs_le.mp (le_refl |τx - τz|) <;> linarith [neg_abs_le (τx - τz), le_abs_self (τx - τz)]
    · rcases le_total (u - τz) h with hhi | hhi
      · have : s' = u - τz := by
          rw [hs', min_eq_right hhi, max_eq_right hlo]
        rw [this, sub_self, abs_zero]; exact abs_nonneg _
      · have : s' = h := by
          rw [hs', min_eq_left hhi, max_eq_right (by linarith)]
        rw [this, abs_le]
        constructor <;> linarith [neg_abs_le (τx - τz), le_abs_self (τx - τz)]
  have hbb : ‖(z + u • w) - (z + (τz + s') • w)‖ ≤ 15 * ρ := by
    have he : (z + u • w) - (z + (τz + s') • w) = (u - τz - s') • w := by module
    rw [he, norm_smul, hw, mul_one, Real.norm_eq_abs]
    exact hclamp.trans hττ
  refine mem_tube_iff.mpr ⟨1 / 2 + lam * s', ⟨?_, ?_⟩, ?_⟩
  · have := (abs_le.mp hs'1).1
    have h2 : lam * h = 1 / 2 := by rw [hh]; field_simp
    nlinarith
  · have := (abs_le.mp hs'1).2
    have h2 : lam * h = 1 / 2 := by rw [hh]; field_simp
    nlinarith
  · have htarget : pieceStart c lam z w + (1 / 2 + lam * s') • w =
        lam • (z + (τz + s') • w - c) := by
      simp only [pieceStart, foot, hτz]
      module
    rw [htarget]
    have hsplit : q - lam • (z + (τz + s') • w - c) =
        (q - lam • (x + (τx + s) • v - c)) +
          lam • ((x + u • v) - (z + u • w) + ((z + u • w) - (z + (τz + s') • w))) := by
      rw [hu]; module
    rw [hsplit]
    calc ‖(q - lam • (x + (τx + s) • v - c)) +
          lam • ((x + u • v) - (z + u • w) + ((z + u • w) - (z + (τz + s') • w)))‖ ≤
          ‖q - lam • (x + (τx + s) • v - c)‖ +
            ‖lam • ((x + u • v) - (z + u • w) + ((z + u • w) - (z + (τz + s') • w)))‖ :=
          norm_add_le _ _
      _ < lam * δ + lam * (9 * ρ + 15 * ρ) := by
          apply add_lt_add_of_lt_of_le hqs
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hab hbb)
      _ ≤ lam * (25 * ρ) := by nlinarith

/-- The zoomed piece of a fine tube lies in the thickened zoomed piece of any unit tube
containing it. -/
theorem piece_subset_piece {c : Space} {lam δ ρ r₁ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ) {x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hT : tube δ x v ⊆ tube ρ z w)
    (hτ : inner ℝ (c - x) v ∈ Icc (-r₁) (1 + r₁)) (hr₁ : r₁ + 1 / (2 * lam) ≤ 1)
    (hcx : ‖c - x‖ ≤ 2) :
    tube (lam * δ) (pieceStart c lam x v) v ⊆ tube (lam * (25 * ρ)) (pieceStart c lam z w) w := by
  rcases endpoints_close hδ hv hw hT with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact piece_subset_piece_aux hlam hδρ hv hw h0 h1 hτ hr₁ hcx
  · rw [← piece_reverse hw]
    have hw' : ‖-w‖ = 1 := by rw [norm_neg, hw]
    exact piece_subset_piece_aux hlam hδρ hv hw' h0 (by simpa using h1) hτ hr₁ hcx

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
