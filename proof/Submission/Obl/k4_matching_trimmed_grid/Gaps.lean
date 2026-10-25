import Submission.Obl.k4_matching_trimmed_grid.Basic

noncomputable section

namespace Submission.Obl.k4_matching_trimmed_grid

open Set

def margin (n J : ℕ) : ℝ := (1 / (n : ℝ)) / (J : ℝ)

lemma margin_pos {n J : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J) : 0 < margin n J := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  exact div_pos (div_pos zero_lt_one hnp) hJp

lemma margin_le_step {n J : ℕ} (hn : 1 ≤ n) (hJ : 1 ≤ J) :
    margin n J ≤ 1 / (n : ℝ) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  exact div_le_self (by positivity) hJr

lemma margin_le_radius {n J d : ℕ} {β : ℕ → ℝ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0) {x : ℝ} (hx : 1 / (n : ℝ) ≤ x) :
    margin n J ≤ radius J β x := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)).trans hx
  apply (div_le_iff₀ hJp).2
  have := (radius_lower hd hdJ hz hx0).2
  nlinarith

lemma remainder_gap {n J d : ℕ} {β : ℕ → ℝ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0) {x : ℝ} (hx : 1 / (n : ℝ) ≤ x)
    {j : ℕ} (hj : j ≤ J) :
    margin n J ≤ ((J : ℝ) + 1 - j) * radius J β x - accuracy J β j x := by
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ)).trans hx
  have ha := accuracy_le hd hdJ hz hj hx0
  have hr := margin_le_radius hn hJ hd hdJ hz hx
  nlinarith

lemma higher_gap {n J d m : ℕ} {β : ℕ → ℝ} (hn : 1 ≤ n) (hJ : 1 ≤ J)
    (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0) {y x : ℝ} (hy : 0 ≤ y)
    (hstep : 1 / (n : ℝ) ≤ x - y) (hay : Active J β m y) (hax : Active J β m x)
    {i : ℕ} (hi : 1 ≤ i) :
    margin n J ≤ accuracy J β (m + i) x + (i : ℝ) * radius J β x - β m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by have := hay.1; omega : m ≠ 0)
  have hJp : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hxy : y ≤ x := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hmx := (eq_div_iff hm0).1 hax.radius_eq
  have hmy := (eq_div_iff hm0).1 hay.radius_eq
  have hdiff : 0 ≤ radius J β x - radius J β y :=
    sub_nonneg.mpr (radius_mono (β := β) hJ hxy)
  have hmJ : (m : ℝ) ≤ J := by exact_mod_cast hay.2.1
  have hbig := mul_nonneg (sub_nonneg.mpr hmJ) hdiff
  have hmarg : margin n J ≤ radius J β x - radius J β y := by
    apply (div_le_iff₀ hJp).2
    nlinarith
  have ha := le_accuracy hd hdJ hz (m + i) ⟨hy, hxy⟩
  have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hmul := mul_nonneg (by linarith : (0 : ℝ) ≤ (i : ℝ) - 1) hdiff
  push_cast at ha
  nlinarith

lemma beta_lt_two_of_active {J d m : ℕ} {β : ℕ → ℝ}
    (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (ha : Active J β m x) : β m < 2 := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast ha.1
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have he := (eq_div_iff hm0).1 ha.radius_eq
  have hl := radius_lower hd hdJ hz hx.le
  have hr : 0 < radius J β x := by
    by_contra hn
    have : radius J β x = 0 := le_antisymm (le_of_not_gt hn) hl.1
    rw [this, mul_zero] at hl
    linarith [hl.2]
  have hmul := mul_pos (by linarith : (0 : ℝ) < m) hr
  nlinarith

end Submission.Obl.k4_matching_trimmed_grid
