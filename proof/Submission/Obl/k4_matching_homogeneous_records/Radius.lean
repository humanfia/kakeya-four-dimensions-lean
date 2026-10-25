import Mathlib

namespace Submission.Obl.k4_matching_homogeneous_records

open Set

noncomputable def radius (J : ℕ) (β : ℕ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun j : ℕ => (a - β j) / (j : ℝ)) '' Icc 1 J)

noncomputable def accuracy (J : ℕ) (β : ℕ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  sSup ((fun x : ℝ => x - (j : ℝ) * radius J β x) '' Icc 0 a)

lemma radius_bdd (J : ℕ) (β : ℕ → ℝ) (a : ℝ) :
    BddAbove ((fun j : ℕ => (a - β j) / (j : ℝ)) '' Icc 1 J) :=
  ((finite_Icc 1 J).image _).bddAbove

lemma radius_le {J : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J) {a b : ℝ}
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ J → (a - β j) / (j : ℝ) ≤ b) :
    radius J β a ≤ b := by
  apply csSup_le (⟨_, mem_image_of_mem _ (show 1 ∈ Icc 1 J from ⟨le_rfl, hJ⟩)⟩)
  rintro _ ⟨j, hj, rfl⟩
  exact h j hj.1 hj.2

lemma line_le_radius {J j : ℕ} {β : ℕ → ℝ} (hj : 1 ≤ j) (hjJ : j ≤ J) (a : ℝ) :
    (a - β j) / (j : ℝ) ≤ radius J β a :=
  le_csSup (radius_bdd J β a) (mem_image_of_mem _ ⟨hj, hjJ⟩)

lemma radius_mono {J : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J) : Monotone (radius J β) := by
  intro a b hab
  apply radius_le hJ
  intro j hj hjJ
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hab _) (by positivity)).trans
    (line_le_radius hj hjJ b)

lemma radius_zero {D J : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hb : ∀ j, 1 ≤ j → j ≤ J → 0 ≤ β j)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ D ∧ β j = 0) : radius J β 0 = 0 := by
  obtain ⟨j, hj, hjD, hj0⟩ := hz
  apply le_antisymm
  · apply radius_le (hj.trans (hjD.trans hDJ))
    intro i hi hiJ
    exact div_nonpos_of_nonpos_of_nonneg (by simpa using neg_nonpos.mpr (hb i hi hiJ))
      (by positivity)
  · simpa [hj0] using line_le_radius (β := β) hj (hjD.trans hDJ) 0

lemma radius_nonneg {D J : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ D ∧ β j = 0) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ radius J β a := by
  obtain ⟨j, hj, hjD, hj0⟩ := hz
  exact (by rw [hj0, sub_zero]; positivity : 0 ≤ (a - β j) / (j : ℝ)).trans
    (line_le_radius hj (hjD.trans hDJ) a)

lemma radius_le_self {J : ℕ} {β : ℕ → ℝ} (hJ : 1 ≤ J)
    (hb : ∀ j, 1 ≤ j → j ≤ J → 0 ≤ β j) {a : ℝ} (ha : 0 ≤ a) :
    radius J β a ≤ a := by
  apply radius_le hJ
  intro j hj hjJ
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < j)).2
  nlinarith [hb j hj hjJ]

lemma self_le_mul_radius {D J : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ D ∧ β j = 0) {a : ℝ} (ha : 0 ≤ a) :
    a ≤ (D : ℝ) * radius J β a := by
  have hr := radius_nonneg hDJ hz ha
  obtain ⟨j, hj, hjD, hj0⟩ := hz
  have hl := (div_le_iff₀ (by positivity : (0 : ℝ) < j)).1
    (line_le_radius (β := β) hj (hjD.trans hDJ) a)
  rw [hj0, sub_zero] at hl
  have hjD' : (j : ℝ) ≤ D := by exact_mod_cast hjD
  nlinarith

lemma accuracy_bdd {D J : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ D ∧ β j = 0) (j : ℕ) (a : ℝ) :
    BddAbove ((fun x : ℝ => x - (j : ℝ) * radius J β x) '' Icc 0 a) := by
  refine ⟨a, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := radius_nonneg hDJ hz hx.1
  have : 0 ≤ (j : ℝ) * radius J β x := by positivity
  linarith [hx.2]

lemma accuracy_le {J : ℕ} {β : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (j : ℕ)
    (h : ∀ x ∈ Icc 0 a, x - (j : ℝ) * radius J β x ≤ b) : accuracy J β j a ≤ b := by
  apply csSup_le (⟨_, mem_image_of_mem _ (show 0 ∈ Icc 0 a from ⟨le_rfl, ha⟩)⟩)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma accuracy_nonneg {D J : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hb : ∀ j, 1 ≤ j → j ≤ J → 0 ≤ β j)
    (hz : ∃ j, 1 ≤ j ∧ j ≤ D ∧ β j = 0) (j : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ accuracy J β j a := by
  have h := le_csSup (accuracy_bdd hDJ hz j a)
    (mem_image_of_mem (fun x : ℝ => x - (j : ℝ) * radius J β x)
      (show 0 ∈ Icc 0 a from ⟨le_rfl, ha⟩))
  simpa [accuracy, radius_zero hDJ hb hz] using h

lemma accuracy_zero_order {J : ℕ} {β : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    accuracy J β 0 a = a := by
  simp only [accuracy, Nat.cast_zero, zero_mul, sub_zero, image_id']
  exact csSup_Icc ha

lemma accuracy_le_gap {J j : ℕ} {β : ℕ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hj : 1 ≤ j) (hjJ : j ≤ J) : accuracy J β j a ≤ β j := by
  apply accuracy_le ha
  intro x hx
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < j)).1
    (line_le_radius (β := β) hj hjJ x)
  nlinarith

lemma accuracy_translate {J j i : ℕ} {β : ℕ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hji : 1 ≤ j + i) (hjiJ : j + i ≤ J) :
    accuracy J β j a ≤ β (j + i) + (i : ℝ) * radius J β a := by
  have hJ : 1 ≤ J := hji.trans hjiJ
  apply accuracy_le ha
  intro x hx
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (j + i : ℕ))).1
    (line_le_radius (β := β) hji hjiJ x)
  have hm := mul_le_mul_of_nonneg_left (radius_mono (β := β) hJ hx.2) (by positivity : (0 : ℝ) ≤ i)
  push_cast at h
  nlinarith

lemma accuracy_remainder {D J j : ℕ} {β : ℕ → ℝ} (hDJ : D ≤ J)
    (hz : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0) {a : ℝ} (ha : 0 ≤ a) (hj : j ≤ J) :
    accuracy J β j a ≤ ((J + 1 : ℕ) - (j : ℝ)) * radius J β a := by
  obtain ⟨i, hi, hiD, hi0⟩ := hz
  have hz' : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0 := ⟨i, hi, hiD, hi0⟩
  have hJ : 1 ≤ J := hi.trans (hiD.trans hDJ)
  apply accuracy_le ha
  intro x hx
  have hself := self_le_mul_radius hDJ hz' hx.1
  have hr := radius_nonneg hDJ hz' hx.1
  have hD' : (D : ℝ) ≤ J + 1 := by exact_mod_cast (Nat.le_succ_of_le hDJ)
  have hj' : (j : ℝ) ≤ J := by exact_mod_cast hj
  have hm := mul_le_mul_of_nonneg_left (radius_mono (β := β) hJ hx.2)
    (show (0 : ℝ) ≤ (J + 1 : ℕ) - (j : ℝ) by push_cast; linarith)
  push_cast at hm ⊢
  nlinarith

end Submission.Obl.k4_matching_homogeneous_records
