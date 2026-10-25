import Mathlib

namespace Submission.Obl.k4_contact_time_rate_rigidity

/-- Two separated contact lines in a fine horizontal row locate the coarse pivot. -/
theorem pivot_bound {b₀ b₁ : Fin 6 → ℝ} {t c₃ c₄ z H q g e δ : ℝ}
    (hδ : 0 < δ) (hsep : δ ≤ |b₀ 3 - b₁ 3|)
    (hcontact₀ : |b₀ 4 + b₀ 0| ≤ e)
    (hcontact₁ : |b₁ 4 + b₁ 0| ≤ e)
    (hrow₀ : |b₀ 4 - c₃ - c₄ * b₀ 3| ≤ H * g)
    (hrow₁ : |b₁ 4 - c₃ - c₄ * b₁ 3| ≤ H * g)
    (hz₀ : |b₀ 0 + t * b₀ 3 - z| ≤ H * q)
    (hz₁ : |b₁ 0 + t * b₁ 3 - z| ≤ H * q) :
    |t - c₄| ≤ (2 * H * q + 2 * H * g + 2 * e) / δ := by
  have heq₀ : |b₀ 0 + c₃ + c₄ * b₀ 3| ≤ e + H * g := by
    calc
      _ = |(b₀ 4 + b₀ 0) - (b₀ 4 - c₃ - c₄ * b₀ 3)| := by congr 1; ring
      _ ≤ |b₀ 4 + b₀ 0| + |b₀ 4 - c₃ - c₄ * b₀ 3| := abs_sub _ _
      _ ≤ _ := add_le_add hcontact₀ hrow₀
  have heq₁ : |b₁ 0 + c₃ + c₄ * b₁ 3| ≤ e + H * g := by
    calc
      _ = |(b₁ 4 + b₁ 0) - (b₁ 4 - c₃ - c₄ * b₁ 3)| := by congr 1; ring
      _ ≤ |b₁ 4 + b₁ 0| + |b₁ 4 - c₃ - c₄ * b₁ 3| := abs_sub _ _
      _ ≤ _ := add_le_add hcontact₁ hrow₁
  have hprod : |t - c₄| * |b₀ 3 - b₁ 3| ≤ 2 * H * q + 2 * H * g + 2 * e := by
    rw [← abs_mul]
    calc
      _ = |((b₀ 0 + t * b₀ 3 - z) - (b₁ 0 + t * b₁ 3 - z)) -
          ((b₀ 0 + c₃ + c₄ * b₀ 3) - (b₁ 0 + c₃ + c₄ * b₁ 3))| := by
        congr 1; ring
      _ ≤ (|b₀ 0 + t * b₀ 3 - z| + |b₁ 0 + t * b₁ 3 - z|) +
          (|b₀ 0 + c₃ + c₄ * b₀ 3| + |b₁ 0 + c₃ + c₄ * b₁ 3|) :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) (abs_sub _ _))
      _ ≤ _ := by linarith
  apply (le_div_iff₀ hδ).mpr
  exact (mul_le_mul_of_nonneg_left hsep (abs_nonneg _)).trans hprod

/-- The fine width and the contact error are smaller than the coarse transverse width. -/
theorem time_radius_le {K q g e δ : ℝ} (hK : 1 ≤ K) (hq₀ : 0 ≤ q)
    (hg : 0 ≤ g) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hq : q ≤ K * g) (he : e ≤ g) :
    q + (2 * K * q + 2 * K * g + 2 * e) / δ ≤ 7 * K ^ 2 * g / δ := by
  have hK₀ : 0 ≤ K := by linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hKg : K * g ≤ K ^ 2 * g := mul_le_mul_of_nonneg_right hKK hg
  have hqδ : q * δ ≤ K ^ 2 * g :=
    (mul_le_of_le_one_right hq₀ hδ₁).trans (hq.trans hKg)
  have he' : e ≤ K ^ 2 * g := by
    exact he.trans ((le_mul_of_one_le_left hg hK).trans hKg)
  have hq' : 2 * K * q ≤ 2 * K ^ 2 * g := by
    have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * K by positivity)
    nlinarith only [hh]
  calc
    _ = (q * δ + 2 * K * q + 2 * K * g + 2 * e) / δ := by
      field_simp
      ring
    _ ≤ _ := (div_le_div_iff_of_pos_right hδ).mpr (by linarith)

end Submission.Obl.k4_contact_time_rate_rigidity
