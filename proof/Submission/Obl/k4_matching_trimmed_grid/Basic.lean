import Mathlib

noncomputable section

namespace Submission.Obl.k4_matching_trimmed_grid

open Set

def line (β : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ := (x - β j) / (j : ℝ)

def radius (J : ℕ) (β : ℕ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun j => line β j x) '' Icc 1 J)

def accuracy (J : ℕ) (β : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  sSup ((fun t : ℝ => t - (j : ℝ) * radius J β t) '' Icc 0 x)

def Active (J : ℕ) (β : ℕ → ℝ) (m : ℕ) (x : ℝ) : Prop :=
  1 ≤ m ∧ m ≤ J ∧ ∀ j, 1 ≤ j → j ≤ J → j ≠ m → line β j x < line β m x

variable {J : ℕ} {β : ℕ → ℝ}

lemma line_le_radius {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) (x : ℝ) :
    line β j x ≤ radius J β x := by
  apply le_csSup
  · exact (Set.finite_Icc 1 J).image _ |>.bddAbove
  · exact mem_image_of_mem _ ⟨hj, hjJ⟩

lemma radius_le (hJ : 1 ≤ J) {x b : ℝ}
    (h : ∀ j, 1 ≤ j → j ≤ J → line β j x ≤ b) : radius J β x ≤ b := by
  apply csSup_le
  · exact ⟨line β 1 x, mem_image_of_mem _ ⟨le_rfl, hJ⟩⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact h j hj.1 hj.2

lemma radius_max (hJ : 1 ≤ J) (x : ℝ) :
    ∃ m, 1 ≤ m ∧ m ≤ J ∧ radius J β x = line β m x := by
  have hn : ((fun j => line β j x) '' Icc 1 J).Nonempty :=
    ⟨line β 1 x, mem_image_of_mem _ ⟨le_rfl, hJ⟩⟩
  obtain ⟨m, hm, he⟩ := hn.csSup_mem ((Set.finite_Icc 1 J).image _)
  exact ⟨m, hm.1, hm.2, he.symm⟩

lemma Active.radius_eq {m : ℕ} {x : ℝ} (h : Active J β m x) :
    radius J β x = line β m x := by
  apply le_antisymm
  · apply radius_le (h.1.trans h.2.1)
    intro j hj hjJ
    by_cases he : j = m
    · simp [he]
    · exact (h.2.2 j hj hjJ he).le
  · exact line_le_radius h.1 h.2.1 x

lemma radius_zero (hJ : 1 ≤ J)
    (hβ : ∀ j, 1 ≤ j → j ≤ J → 0 ≤ β j)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ J ∧ β j = 0) : radius J β 0 = 0 := by
  apply le_antisymm
  · apply radius_le hJ
    intro j hj hjJ
    exact div_nonpos_of_nonpos_of_nonneg (by simpa using neg_nonpos.mpr (hβ j hj hjJ))
      (Nat.cast_nonneg j)
  · obtain ⟨j, hj, hjJ, he⟩ := hz
    simpa [line, he] using line_le_radius (β := β) hj hjJ 0

lemma radius_mono (hJ : 1 ≤ J) : Monotone (radius J β) := by
  intro x y hxy
  apply radius_le hJ
  intro j hj hjJ
  exact (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg j)).trans
    (line_le_radius hj hjJ y)

lemma radius_sub_le (hJ : 1 ≤ J) {x y : ℝ} (hxy : x ≤ y) :
    radius J β y - radius J β x ≤ y - x := by
  suffices radius J β y ≤ radius J β x + (y - x) by linarith
  apply radius_le hJ
  intro j hj hjJ
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0 : ℝ) < j := by linarith
  have hline := line_le_radius (β := β) hj hjJ x
  have hstep : (y - x) / (j : ℝ) ≤ y - x := by
    apply (div_le_iff₀ hjp).2
    nlinarith
  have he : line β j y = line β j x + (y - x) / (j : ℝ) := by
    unfold line
    ring
  linarith

lemma radius_lower {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ radius J β x ∧ x ≤ (J : ℝ) * radius J β x := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hline : x / (d : ℝ) ≤ radius J β x := by
    simpa [line, hz] using line_le_radius (β := β) hd hdJ x
  have hr : 0 ≤ radius J β x := (div_nonneg hx hdp.le).trans hline
  have hxd : x ≤ (d : ℝ) * radius J β x := by
    have := (div_le_iff₀ hdp).1 hline
    nlinarith
  have hdJr : (d : ℝ) ≤ J := by exact_mod_cast hdJ
  exact ⟨hr, hxd.trans (mul_le_mul_of_nonneg_right hdJr hr)⟩

lemma accuracy_bdd {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    (j : ℕ) (x : ℝ) :
    BddAbove ((fun t : ℝ => t - (j : ℝ) * radius J β t) '' Icc 0 x) := by
  refine ⟨x, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hr := (radius_lower hd hdJ hz ht.1).1
  have hp := mul_nonneg (Nat.cast_nonneg j) hr
  linarith [ht.2]

lemma le_accuracy {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    (j : ℕ) {x t : ℝ} (ht : t ∈ Icc 0 x) :
    t - (j : ℝ) * radius J β t ≤ accuracy J β j x := by
  exact le_csSup (accuracy_bdd hd hdJ hz j x) (mem_image_of_mem _ ht)

lemma accuracy_le {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    {j : ℕ} (hjJ : j ≤ J) {x : ℝ} (hx : 0 ≤ x) :
    accuracy J β j x ≤ ((J : ℝ) - j) * radius J β x := by
  have hJ := hd.trans hdJ
  apply csSup_le
  · exact ⟨0 - (j : ℝ) * radius J β 0, mem_image_of_mem _ ⟨le_rfl, hx⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have htJ := (radius_lower hd hdJ hz ht.1).2
    have hmono := radius_mono (β := β) hJ ht.2
    have hjr : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hmul := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hjr)
    nlinarith

lemma Active.between {m : ℕ} {a b x : ℝ} (ha : Active J β m a)
    (hb : Active J β m b) (hx : x ∈ Icc a b) : Active J β m x := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro j hj hjJ hne
  have hla := ha.2.2 j hj hjJ hne
  have hlb := hb.2.2 j hj hjJ hne
  unfold line at *
  simp only [div_eq_mul_inv] at *
  by_cases hs : 0 ≤ (m : ℝ)⁻¹ - (j : ℝ)⁻¹
  · have := mul_nonneg (sub_nonneg.mpr hx.1) hs
    nlinarith
  · have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hx.2)
    nlinarith

lemma active_of_no_crossings (hJ : 1 ≤ J) {a b : ℝ} (hab : a ≤ b)
    (hne : ∀ m, 1 ≤ m → m ≤ J → ∀ j, 1 ≤ j → j ≤ J → j ≠ m →
      ∀ x ∈ Icc a b, line β j x ≠ line β m x) :
    ∃ m, ∀ x ∈ Icc a b, Active J β m x := by
  obtain ⟨m, hm, hmJ, he⟩ := radius_max (β := β) hJ a
  have ha : Active J β m a := by
    refine ⟨hm, hmJ, ?_⟩
    intro j hj hjJ hjm
    have hl := line_le_radius (β := β) hj hjJ a
    rw [he] at hl
    exact hl.lt_of_ne (hne m hm hmJ j hj hjJ hjm a ⟨le_rfl, hab⟩)
  refine ⟨m, ?_⟩
  intro x hx
  refine ⟨hm, hmJ, ?_⟩
  intro j hj hjJ hjm
  by_contra hnlt
  have hstart : 0 < line β m a - line β j a := sub_pos.mpr (ha.2.2 j hj hjJ hjm)
  have hend : line β m x - line β j x ≤ 0 := by linarith
  have hc : ContinuousOn (fun t => line β m t - line β j t) (Icc a x) := by
    unfold line
    fun_prop
  obtain ⟨y, hy, hey⟩ := intermediate_value_Icc' hx.1 hc ⟨hend, hstart.le⟩
  have hyab : y ∈ Icc a b := ⟨hy.1, hy.2.trans hx.2⟩
  exact hne m hm hmJ j hj hjJ hjm y hyab (by linarith)

end Submission.Obl.k4_matching_trimmed_grid
