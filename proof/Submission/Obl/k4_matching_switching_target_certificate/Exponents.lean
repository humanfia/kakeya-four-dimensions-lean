import Submission.Obl.k4_matching_trimmed_grid.Basic

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set
open Submission.Obl.k4_matching_trimmed_grid

variable {J v : ℕ} {β : ℕ → ℝ}

/-- Before a line is active, the radius grows no faster than that line. -/
lemma radius_sub_le_active {a b : ℝ} (hab : a ≤ b)
    (hv : 1 ≤ v) (hvJ : v ≤ J) (hb : radius J β b = line β v b) :
    (v : ℝ) * (radius J β b - radius J β a) ≤ b - a := by
  have hvp : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have ha := line_le_radius (β := β) hv hvJ a
  have he : (v : ℝ) * radius J β b = b - β v := by
    rw [hb, line, mul_div_cancel₀ _ hvp.ne']
  have ha' : a - β v ≤ (v : ℝ) * radius J β a := by
    simpa [mul_comm] using (div_le_iff₀ hvp).mp ha
  nlinarith

/-- The low-jet accuracies are attained at the current level on an active piece. -/
lemma accuracy_eq_active {a : ℝ} (ha : 0 ≤ a) (hv : 1 ≤ v) (hvJ : v ≤ J)
    (hr : radius J β a = line β v a) {j : ℕ} (hj : j ≤ v) :
    accuracy J β j a = a - (j : ℝ) * radius J β a := by
  have hbound : ∀ t ∈ Icc (0 : ℝ) a,
      t - (j : ℝ) * radius J β t ≤ a - (j : ℝ) * radius J β a := by
    intro t ht
    have hrad := radius_sub_le_active ht.2 hv hvJ hr
    have hmono := radius_mono (β := β) (hv.trans hvJ) ht.2
    have hjr : (j : ℝ) ≤ v := by exact_mod_cast hj
    have hmul := mul_nonneg (sub_nonneg.mpr hjr) (sub_nonneg.mpr hmono)
    nlinarith
  have hmem : a - (j : ℝ) * radius J β a ∈
      (fun t : ℝ => t - (j : ℝ) * radius J β t) '' Icc 0 a :=
    mem_image_of_mem _ ⟨ha, le_rfl⟩
  apply le_antisymm
  · exact csSup_le ⟨_, hmem⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hbound t ht)
  · exact le_csSup ⟨_, by rintro _ ⟨t, ht, rfl⟩; exact hbound t ht⟩ hmem

lemma accuracy_active_order {a : ℝ} (ha : 0 ≤ a) (hv : 1 ≤ v) (hvJ : v ≤ J)
    (hr : radius J β a = line β v a) : accuracy J β v a = β v := by
  rw [accuracy_eq_active ha hv hvJ hr le_rfl, hr, line]
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  rw [mul_div_cancel₀ _ hv0]
  ring

lemma accuracy_mono {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    (j : ℕ) : MonotoneOn (accuracy J β j) (Ici 0) := by
  intro a ha b hb hab
  exact csSup_le_csSup (accuracy_bdd hd hdJ hz j b)
    ⟨_, mem_image_of_mem _ ⟨le_rfl, ha⟩⟩
    (image_mono (Icc_subset_Icc_right hab))

/-- All translated bin errors are bounded by the error at their output jet order. -/
lemma accuracy_translation {d : ℕ} (hd : 1 ≤ d) (hdJ : d ≤ J) (hz : β d = 0)
    {a : ℝ} (ha : 0 ≤ a) (j i : ℕ) :
    accuracy J β j a ≤ accuracy J β (j + i) a + (i : ℝ) * radius J β a := by
  apply csSup_le
  · exact ⟨_, mem_image_of_mem _ ⟨le_rfl, ha⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hacc := le_accuracy hd hdJ hz (j + i) ht
    have hmono := radius_mono (β := β) (hd.trans hdJ) ht.2
    have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg i)
    push_cast at hacc
    linarith

lemma accuracy_le_beta {j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) {a : ℝ} (ha : 0 ≤ a) :
    accuracy J β j a ≤ β j := by
  apply csSup_le
  · exact ⟨_, mem_image_of_mem _ ⟨le_rfl, ha⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hjp : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hline := (div_le_iff₀ hjp).mp (line_le_radius (β := β) hj hjJ t)
    linarith

/-- Increment of a low-jet accuracy while the same line remains active. -/
lemma accuracy_active_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hv : 1 ≤ v) (hvJ : v ≤ J) (hra : radius J β a = line β v a)
    (hrb : radius J β b = line β v b) {j : ℕ} (hj : j ≤ v) :
    accuracy J β j b - accuracy J β j a = (1 - (j : ℝ) / (v : ℝ)) * (b - a) := by
  rw [accuracy_eq_active hb hv hvJ hrb hj, accuracy_eq_active ha hv hvJ hra hj,
    hrb, hra, line, line]
  ring

end Submission.Obl.k4_matching_switching_target_certificate
