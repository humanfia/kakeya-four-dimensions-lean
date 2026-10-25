import Mathlib

namespace Submission.Obl.k4_eligibility_sign_description

/-- Both weak and strict positivity use the same finite interval test. -/
def Positive (strict : Bool) (x : ℝ) : Prop := if strict then 0 < x else 0 ≤ x

lemma positive_mono {strict : Bool} {x y : ℝ} (h : Positive strict x) (hxy : x ≤ y) :
    Positive strict y := by
  cases strict <;> simp only [Positive, Bool.false_eq_true, ↓reduceIte] at * <;> linarith

lemma positive_mul_iff (strict : Bool) {a x : ℝ} (ha : 0 < a) :
    Positive strict (a * x) ↔ Positive strict x := by
  cases strict <;> simp [Positive, mul_pos_iff_of_pos_left ha, mul_nonneg_iff_of_pos_left ha]

/-- Positivity of a quadratic on a closed interval is a six-sign condition. -/
theorem quadratic_positive_iff (strict : Bool) (A B C l r : ℝ) (hlr : l ≤ r) :
    (∀ t ∈ Set.Icc l r, Positive strict (A * t ^ 2 + B * t + C)) ↔
    Positive strict (A * l ^ 2 + B * l + C) ∧
    Positive strict (A * r ^ 2 + B * r + C) ∧
    (A ≤ 0 ∨ 0 ≤ 2 * A * l + B ∨ 2 * A * r + B ≤ 0 ∨
      Positive strict (4 * A * C - B ^ 2)) := by
  constructor
  · intro h
    refine ⟨h l ⟨le_rfl, hlr⟩, h r ⟨hlr, le_rfl⟩, ?_⟩
    by_cases hA : A ≤ 0
    · exact Or.inl hA
    by_cases hL : 0 ≤ 2 * A * l + B
    · exact Or.inr (Or.inl hL)
    by_cases hR : 2 * A * r + B ≤ 0
    · exact Or.inr (Or.inr (Or.inl hR))
    have hA' : 0 < A := lt_of_not_ge hA
    have h2A : 0 < 2 * A := by positivity
    have hv : -B / (2 * A) ∈ Set.Icc l r := by
      constructor
      · apply (le_div_iff₀ h2A).2
        linarith
      · apply (div_le_iff₀ h2A).2
        linarith
    have heq : 4 * A * (A * (-B / (2 * A)) ^ 2 + B * (-B / (2 * A)) + C) =
        4 * A * C - B ^ 2 := by
      field_simp
      <;> ring
    have hpos := (positive_mul_iff strict (show 0 < 4 * A by positivity)).2
      (h _ hv)
    rw [heq] at hpos
    exact Or.inr (Or.inr (Or.inr hpos))
  · rintro ⟨hL, hR, htest⟩ t ⟨hlt, htr⟩
    by_cases hA : A ≤ 0
    · have hbound : min (A * l ^ 2 + B * l + C) (A * r ^ 2 + B * r + C) ≤
          A * t ^ 2 + B * t + C := by
        by_cases heq : l = r
        · have ht : t = l := by linarith
          simp [ht, heq]
        have hlen : 0 < r - l := sub_pos.mpr (lt_of_le_of_ne hlr heq)
        have hminL := min_le_left (A * l ^ 2 + B * l + C) (A * r ^ 2 + B * r + C)
        have hminR := min_le_right (A * l ^ 2 + B * l + C) (A * r ^ 2 + B * r + C)
        have h1 := mul_nonneg (sub_nonneg.mpr htr) (sub_nonneg.mpr hminL)
        have h2 := mul_nonneg (sub_nonneg.mpr hlt) (sub_nonneg.mpr hminR)
        have h3 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hA)
          (mul_nonneg (sub_nonneg.mpr hlt) (sub_nonneg.mpr htr))) hlen.le
        apply (mul_le_mul_iff_right₀ hlen).mp
        nlinarith only [h1, h2, h3]
      apply positive_mono (x := min (A * l ^ 2 + B * l + C) (A * r ^ 2 + B * r + C))
        _ hbound
      rcases le_total (A * l ^ 2 + B * l + C) (A * r ^ 2 + B * r + C) with h | h
      · simpa [min_eq_left h] using hL
      · simpa [min_eq_right h] using hR
    have hA' : 0 < A := lt_of_not_ge hA
    rcases htest with hbad | hdL | hdR | hdisc
    · exact False.elim (hA hbad)
    · apply positive_mono hL
      have h1 := mul_nonneg hA'.le (sq_nonneg (t - l))
      have h2 := mul_nonneg (sub_nonneg.mpr hlt) hdL
      nlinarith only [h1, h2]
    · apply positive_mono hR
      have h1 := mul_nonneg hA'.le (sq_nonneg (t - r))
      have h2 := mul_nonneg (sub_nonneg.mpr htr) (neg_nonneg.mpr hdR)
      nlinarith only [h1, h2]
    · apply (positive_mul_iff strict (show 0 < 4 * A by positivity)).1
      apply positive_mono hdisc
      nlinarith only [sq_nonneg (2 * A * t + B)]

end Submission.Obl.k4_eligibility_sign_description
