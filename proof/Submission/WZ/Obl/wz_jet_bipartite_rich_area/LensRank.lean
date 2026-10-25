-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.LensRank.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.WindowLens

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- The rank of a width, with all widths below the resolution assigned rank
zero. A factor `B` in width gives at least one rank of separation. -/
noncomputable def lensWidthRank (B s w : ℝ) : ℕ := ⌊Real.logb B (w / s)⌋₊

theorem lensWidthRank_mono {B s w W : ℝ} (hB : 1 < B) (hs : 0 < s)
    (hw : 0 < w) (hwW : w ≤ W) : lensWidthRank B s w ≤ lensWidthRank B s W := by
  exact Nat.floor_mono (Real.logb_le_logb_of_le hB (div_pos hw hs)
    (div_le_div_of_nonneg_right hwW hs.le))

/-- A multiplicative separation above the resolution gives strict rank
separation. No upper bound on either width is needed. -/
theorem lensWidthRank_lt {B s w W : ℝ} (hB : 1 < B) (hs : 0 < s)
    (hsw : s ≤ w) (hgap : B * w < W) : lensWidthRank B s w < lensWidthRank B s W := by
  have hw : 0 < w := hs.trans_le hsw
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hx : 0 < w / s := div_pos hw hs
  have hnonneg : 0 ≤ Real.logb B (w / s) :=
    Real.logb_nonneg hB ((one_le_div hs).mpr hsw)
  have hscaled : B * (w / s) < W / s := by
    simpa only [mul_div_assoc] using div_lt_div_of_pos_right hgap hs
  have hlog := Real.logb_lt_logb hB (mul_pos hB0 hx) hscaled
  rw [Real.logb_mul hB0.ne' hx.ne', Real.logb_self_eq_one hB] at hlog
  have hfloor := Nat.floor_mono hlog.le
  rw [add_comm (1 : ℝ), Nat.floor_add_one hnonneg] at hfloor
  exact Nat.lt_of_succ_le hfloor

/-- A single top rank accommodates the pairs with fewer than two
crossings; the remaining ranks are logarithmic in the available width. -/
noncomputable def windowLensHeight (B s l u : ℝ) : ℕ := lensWidthRank B s (u - l) + 1

/-- A canonical symmetric rank for every curve pair in the window. -/
noncomputable def windowLensRank {n : ℕ} (g : Fin n → ℝ → ℝ) (B s l u : ℝ)
    (i j : Fin n) : ℕ := by
  classical
  exact if HasWindowLens g l u i j then lensWidthRank B s (windowLensWidth g l u i j)
    else windowLensHeight B s l u

theorem windowLensRank_symm {n : ℕ} (g : Fin n → ℝ → ℝ) (B s l u : ℝ) (i j : Fin n) :
    windowLensRank g B s l u i j = windowLensRank g B s l u j i := by
  classical
  simp only [windowLensRank, hasWindowLens_symm g l u i j, windowLensWidth_symm g l u i j]

theorem windowLensRank_lt_height_of_lens {n : ℕ} (g : Fin n → ℝ → ℝ)
    {B s l u : ℝ} (hB : 1 < B) (hs : 0 < s) (hlu : l ≤ u)
    (i j : Fin n) (h : HasWindowLens g l u i j) :
    windowLensRank g B s l u i j < windowLensHeight B s l u := by
  classical
  rw [windowLensRank, ite_eq_left h, windowLensHeight]
  suffices lensWidthRank B s (windowLensWidth g l u i j) ≤ lensWidthRank B s (u - l) by omega
  by_cases hw : 0 < windowLensWidth g l u i j
  · exact lensWidthRank_mono hB hs hw (windowLensWidth_le g hlu i j)
  · have heq : windowLensWidth g l u i j = 0 :=
      le_antisymm (le_of_not_gt hw) (windowLensWidth_nonneg g l u i j)
    simp only [heq, lensWidthRank, zero_div, Real.logb_zero, Nat.floor_zero]
    exact Nat.zero_le _

theorem windowLensRank_le_height {n : ℕ} (g : Fin n → ℝ → ℝ)
    {B s l u : ℝ} (hB : 1 < B) (hs : 0 < s) (hlu : l ≤ u) (i j : Fin n) :
    windowLensRank g B s l u i j ≤ windowLensHeight B s l u := by
  classical
  by_cases h : HasWindowLens g l u i j
  · exact (windowLensRank_lt_height_of_lens g hB hs hlu i j h).le
  · simp only [windowLensRank, ite_eq_right h]
    exact le_rfl

/-- Strict width contraction implies rank descent. A pair without two
crossings is already assigned the top rank and needs no width hypothesis. -/
theorem windowLensRank_lt_of_contraction {n : ℕ} (g : Fin n → ℝ → ℝ)
    {B s l u : ℝ} (hB : 1 < B) (hs : 0 < s) (hlu : l ≤ u)
    (i k j m : Fin n) (hchild : HasWindowLens g l u j m)
    (hwidth : s ≤ windowLensWidth g l u j m)
    (hcontract : HasWindowLens g l u i k →
      B * windowLensWidth g l u j m < windowLensWidth g l u i k) :
    windowLensRank g B s l u j m < windowLensRank g B s l u i k := by
  classical
  by_cases hparent : HasWindowLens g l u i k
  · rw [windowLensRank, ite_eq_left hchild, windowLensRank, ite_eq_left hparent]
    exact lensWidthRank_lt hB hs hwidth (hcontract hparent)
  · conv_rhs => rw [windowLensRank, ite_eq_right hparent]
    exact windowLensRank_lt_height_of_lens g hB hs hlu j m hchild

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
