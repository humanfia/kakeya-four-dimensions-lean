-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.LowRangeGeom.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Bushes

/-!
# Geometry for the low range of the Furstenberg estimate

`normals_close_of_long_vector`: two unit normals both nearly orthogonal to a long
vector `v` are close up to sign.  `near_of_not_stripSep`: a label failing
separation with `j` in either order has its point near the line of `j` and its
normal near `± j.2`.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma normals_close_of_long_vector {v e f : E2} {a b lam : ℝ} (hlam : 0 < lam)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hv : lam ≤ ‖v‖)
    (hve : |inner ℝ v e| < a) (hvf : |inner ℝ v f| < b)
    (ha : (a / lam) ^ 2 ≤ 1 / 2) (hb : (b / lam) ^ 2 ≤ 1 / 2) :
    ‖e - f‖ ^ 2 < 3 * ((a + b) / lam) ^ 2 ∨ ‖e - -f‖ ^ 2 < 3 * ((a + b) / lam) ^ 2 := by
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le hlam hv
  set u : E2 := ‖v‖⁻¹ • v with hudef
  have hu : ‖u‖ = 1 := by rw [hudef, norm_smul, norm_inv, norm_norm]; field_simp
  have hcoef : ∀ g : E2, ∀ c : ℝ, |inner ℝ v g| < c → |inner ℝ g u| < c / lam := by
    intro g c hg
    rw [hudef, inner_smul_right, real_inner_comm, abs_mul, abs_inv, abs_norm]
    have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hg.le
    calc ‖v‖⁻¹ * |inner ℝ v g| ≤ lam⁻¹ * |inner ℝ v g| :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hlam hv) (abs_nonneg _)
      _ < lam⁻¹ * c := mul_lt_mul_of_pos_left hg (inv_pos.mpr hlam)
      _ = c / lam := by rw [inv_mul_eq_div]
  have hea := hcoef e a hve
  have hfb := hcoef f b hvf
  have hsq : ∀ g : E2, ∀ c : ℝ, |inner ℝ g u| < c / lam → (c / lam) ^ 2 ≤ 1 / 2 →
      (inner ℝ g u) ^ 2 ≤ 1 / 2 := by
    intro g c h1 h2
    have := abs_nonneg (inner ℝ g u)
    rw [← sq_abs]; nlinarith
  have hdiff : ∀ x y : ℝ, |x| < a / lam → |y| < b / lam → (x - y) ^ 2 < ((a + b) / lam) ^ 2 := by
    intro x y hx hy
    have h1 : |x - y| < (a + b) / lam := by
      calc |x - y| ≤ |x| + |y| := abs_sub _ _
        _ < a / lam + b / lam := add_lt_add hx hy
        _ = (a + b) / lam := by ring
    rw [← sq_abs]; exact pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero
  by_cases hside : 0 ≤ inner ℝ e (rot u) * inner ℝ f (rot u)
  · left
    have hc := frame_close hu he hf (hsq e a hea ha) (hsq f b hfb hb) hside
    have := hdiff _ _ hea hfb
    linarith
  · right
    have hnf : ‖-f‖ = 1 := by rw [norm_neg, hf]
    have hfb' : |inner ℝ (-f) u| < b / lam := by rw [inner_neg_left, abs_neg]; exact hfb
    have hside' : 0 ≤ inner ℝ e (rot u) * inner ℝ (-f) (rot u) := by
      rw [inner_neg_left]; nlinarith
    have hc := frame_close hu he hnf (hsq e a hea ha) (hsq (-f) b hfb' hb) hside'
    have := hdiff _ _ hea hfb'
    linarith

lemma near_of_not_stripSep {q j : E2 × E2} {r : ℝ} (hq4 : ‖q.1‖ ≤ 4) (hj4 : ‖j.1‖ ≤ 4)
    (h : q = j ∨ ¬ StripSep r q j ∨ ¬ StripSep r j q) (hr : 0 < r) :
    |inner ℝ (q.1 - j.1) j.2| < 9 * r ∧ (dist q.2 j.2 < r ∨ dist q.2 (-j.2) < r) := by
  have h8 : ‖q.1 - j.1‖ ≤ 8 := norm_le_eight_of_norm_le_four hq4 hj4
  rcases h with rfl | h | h
  · refine ⟨by simp; linarith, Or.inl (by simp; linarith)⟩
  · unfold StripSep at h
    push Not at h
    obtain ⟨hn, hoff⟩ := h
    have hn' : dist q.2 j.2 < r ∨ dist q.2 (-j.2) < r := by
      by_cases h1 : r ≤ dist q.2 j.2
      · exact Or.inr (hn h1)
      · exact Or.inl (not_le.mp h1)
    refine ⟨?_, hn'⟩
    rcases hn' with h2 | h2
    · have h2' : ‖q.2 - j.2‖ ≤ r := by simpa [dist_eq_norm] using h2.le
      have := inner_lt_of_close (e' := j.2) h8 hoff h2'
      linarith
    · have h2' : ‖q.2 - -j.2‖ ≤ r := by simpa [dist_eq_norm] using h2.le
      have := inner_lt_of_close (e' := -j.2) h8 hoff h2'
      rw [inner_neg_right, abs_neg] at this
      linarith
  · unfold StripSep at h
    push Not at h
    obtain ⟨hn, hoff⟩ := h
    refine ⟨?_, ?_⟩
    · rw [show q.1 - j.1 = -(j.1 - q.1) by abel, inner_neg_left, abs_neg]
      linarith
    · by_cases h1 : r ≤ dist j.2 q.2
      · right
        have := hn h1
        have heq : dist q.2 (-j.2) = dist j.2 (-q.2) := by
          rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
        rw [heq]; exact this
      · left; rw [dist_comm]; exact not_le.mp h1

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
