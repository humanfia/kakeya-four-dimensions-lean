-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.ScaledGridCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RealSeparatedCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CoverCounting
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridIteratedSums

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped Pointwise

/-- A contraction of a separated set retains a proportional number of
occupied cover balls. -/
theorem scaled_separated_cover_lower {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hu1 : u ≤ 1)
    (A : Finset ℝ) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    {m : ℕ} (cc : Fin m → ℝ)
    (hc : Covers δ ((fun a : ℝ => u * a) '' (↑A : Set ℝ)) cc) :
    u * (A.card : ℝ) ≤ 4 * (m : ℝ) := by
  classical
  have hf (j : Fin m) :
      ((A.filter (fun a => dist (u * a) (cc j) ≤ δ)).card : ℝ) ≤ 4 / u := by
    let S := A.filter (fun a => dist (u * a) (cc j) ≤ δ)
    have hball (a : ℝ) (ha : a ∈ S) : dist a (cc j / u) ≤ δ / u := by
      have hd : dist (u * a) (cc j) = u * dist a (cc j / u) := by
        rw [Real.dist_eq, Real.dist_eq]
        calc
          |u * a - cc j| = |u * (a - cc j / u)| := by congr 1; field_simp
          _ = |u| * |a - cc j / u| := abs_mul _ _
          _ = u * |a - cc j / u| := by rw [abs_of_pos hu]
      have hh := (Finset.mem_filter.mp ha).2
      rw [hd] at hh
      apply (le_div_iff₀ hu).mpr
      nlinarith
    have hh := real_separated_ball_card hδ (by positivity : 0 ≤ δ / u) S
      (fun a ha b hb hne => hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hne) hball
    have hm := mul_le_mul_of_nonneg_right hh hu.le
    have hid : (2 * (δ / u) + 2 * δ) * u = (2 + 2 * u) * δ := by field_simp <;> ring
    rw [hid] at hm
    apply (le_div_iff₀ hu).mpr
    have hmul : ((S.card : ℝ) * u) * δ ≤ 4 * δ := by
      nlinarith [mul_le_mul_of_nonneg_right hu1 hδ.le]
    exact (mul_le_mul_iff_left₀ hδ).mp hmul
  have hh := card_le_cover_mul_fiber_bound A (fun a : ℝ => u * a) hc hf
  have hm := mul_le_mul_of_nonneg_left hh hu.le
  have hid : u * ((m : ℝ) * (4 / u)) = 4 * (m : ℝ) := by field_simp
  rwa [hid] at hm

/-- Grid entropy loses at most the contraction factor, up to four. -/
theorem scaled_grid_card_lower {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) (hu1 : u ≤ 1)
    (A : Finset ℝ) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    u * (A.card : ℝ) ≤ 4 * (((A.image (fun a => u * a)).image (realGridIndex δ)).card : ℝ) := by
  classical
  obtain ⟨m, cc, hc, hm⟩ := cover_of_grid_nsmul_sub_nsmul hδ (A.image (fun a => u * a)) 1 0
  simp only [one_nsmul, zero_nsmul, sub_zero] at hc hm
  norm_num only at hc
  have hh := scaled_separated_cover_lower hδ hu hu1 A hsep cc (by
    simpa only [Finset.coe_image, one_mul] using hc)
  simpa only [hm] using hh

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
