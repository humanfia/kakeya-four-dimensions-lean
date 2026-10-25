import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

/-- Values at the three unit interpolation nodes bound all univariate coefficients. -/
theorem unit_coefficients_le {a b c E : ℝ}
    (h : ∀ t ∈ Icc (-1 : ℝ) 1, |a + b * t + c * t ^ 2| ≤ E) :
    |a| ≤ E ∧ |b| ≤ E ∧ |c| ≤ 2 * E := by
  have h0 := h 0 (by norm_num)
  have hp := h 1 (by norm_num)
  have hm := h (-1) (by norm_num)
  norm_num only [mul_zero, mul_one, zero_pow (by decide : 2 ≠ 0), one_pow,
    neg_one_sq, add_zero, mul_neg, neg_mul, one_mul] at h0 hp hm
  rcases abs_le.mp hp with ⟨hp₁, hp₂⟩
  rcases abs_le.mp hm with ⟨hm₁, hm₂⟩
  rcases abs_le.mp h0 with ⟨h0₁, h0₂⟩
  exact ⟨h0, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Unordered separated interpolation nodes suffice to control a unit interval. -/
theorem quad_eval_le_of_separated {a b c E H w x₀ x₁ x₂ : ℝ}
    (hw : 0 < w) (hH : 0 ≤ H)
    (hx₀ : |x₀| ≤ H) (hx₁ : |x₁| ≤ H) (hx₂ : |x₂| ≤ H)
    (h01 : w ≤ |x₀ - x₁|) (h02 : w ≤ |x₀ - x₂|)
    (h12 : w ≤ |x₁ - x₂|)
    (h₀ : |a + b * x₀ + c * x₀ ^ 2| ≤ E)
    (h₁ : |a + b * x₁ + c * x₁ ^ 2| ≤ E)
    (h₂ : |a + b * x₂ + c * x₂ ^ 2| ≤ E)
    (x : ℝ) (hx : |x| ≤ 1) :
    |a + b * x + c * x ^ 2| ≤ 3 * E * ((1 + H) / w) ^ 2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans h₀
  have hne01 : x₀ - x₁ ≠ 0 := abs_pos.mp (hw.trans_le h01)
  have hne02 : x₀ - x₂ ≠ 0 := abs_pos.mp (hw.trans_le h02)
  have hne12 : x₁ - x₂ ≠ 0 := abs_pos.mp (hw.trans_le h12)
  have hne10 : x₁ - x₀ ≠ 0 := by simpa [sub_eq_zero] using Ne.symm (sub_ne_zero.mp hne01)
  have hne20 : x₂ - x₀ ≠ 0 := by simpa [sub_eq_zero] using Ne.symm (sub_ne_zero.mp hne02)
  have hne21 : x₂ - x₁ ≠ 0 := by simpa [sub_eq_zero] using Ne.symm (sub_ne_zero.mp hne12)
  let p : ℝ → ℝ := fun t => a + b * t + c * t ^ 2
  have hlag : p x =
      p x₀ * ((x - x₁) * (x - x₂) / ((x₀ - x₁) * (x₀ - x₂))) +
      p x₁ * ((x - x₀) * (x - x₂) / ((x₁ - x₀) * (x₁ - x₂))) +
      p x₂ * ((x - x₀) * (x - x₁) / ((x₂ - x₀) * (x₂ - x₁))) := by
    dsimp [p]
    field_simp
    ring
  have hdist : ∀ z : ℝ, |z| ≤ H → |x - z| ≤ 1 + H := by
    intro z hz
    exact (abs_sub _ _).trans (add_le_add hx hz)
  have hfac : ∀ u v r s : ℝ, |u| ≤ 1 + H → |v| ≤ 1 + H →
      w ≤ |r| → w ≤ |s| →
      |u * v / (r * s)| ≤ ((1 + H) / w) ^ 2 := by
    intro u v r s hu hv hr hs
    rw [abs_div, abs_mul, abs_mul, div_pow,
      div_le_div_iff₀ (mul_pos (hw.trans_le hr) (hw.trans_le hs)) (by positivity)]
    calc
      |u| * |v| * w ^ 2 ≤ (1 + H) * (1 + H) * w ^ 2 := by gcongr
      _ ≤ (1 + H) ^ 2 * (|r| * |s|) := by
        rw [sq, sq]
        gcongr
  have h10 : w ≤ |x₁ - x₀| := by simpa only [abs_sub_comm] using h01
  have h20 : w ≤ |x₂ - x₀| := by simpa only [abs_sub_comm] using h02
  have h21 : w ≤ |x₂ - x₁| := by simpa only [abs_sub_comm] using h12
  have t₀ := hfac _ _ _ _ (hdist _ hx₁) (hdist _ hx₂) h01 h02
  have t₁ := hfac _ _ _ _ (hdist _ hx₀) (hdist _ hx₂) h10 h12
  have t₂ := hfac _ _ _ _ (hdist _ hx₀) (hdist _ hx₁) h20 h21
  change |p x| ≤ _
  rw [hlag]
  calc
    _ ≤ |p x₀| * |(x - x₁) * (x - x₂) / ((x₀ - x₁) * (x₀ - x₂))| +
        |p x₁| * |(x - x₀) * (x - x₂) / ((x₁ - x₀) * (x₁ - x₂))| +
        |p x₂| * |(x - x₀) * (x - x₁) / ((x₂ - x₀) * (x₂ - x₁))| := by
      simp only [← abs_mul]
      exact abs_add_three _ _ _
    _ ≤ E * ((1 + H) / w) ^ 2 + E * ((1 + H) / w) ^ 2 +
        E * ((1 + H) / w) ^ 2 := by gcongr
    _ = 3 * E * ((1 + H) / w) ^ 2 := by ring

/-- Three velocity samples bound all coefficients of their quadratic. -/
theorem quad_coefficients_le_of_separated {a b c E H w x₀ x₁ x₂ : ℝ}
    (hw : 0 < w) (hH : 0 ≤ H)
    (hx₀ : |x₀| ≤ H) (hx₁ : |x₁| ≤ H) (hx₂ : |x₂| ≤ H)
    (h01 : w ≤ |x₀ - x₁|) (h02 : w ≤ |x₀ - x₂|)
    (h12 : w ≤ |x₁ - x₂|)
    (h₀ : |a + b * x₀ + c * x₀ ^ 2| ≤ E)
    (h₁ : |a + b * x₁ + c * x₁ ^ 2| ≤ E)
    (h₂ : |a + b * x₂ + c * x₂ ^ 2| ≤ E) :
    |a| ≤ 6 * E * ((1 + H) / w) ^ 2 ∧
    |b| ≤ 6 * E * ((1 + H) / w) ^ 2 ∧
    |c| ≤ 6 * E * ((1 + H) / w) ^ 2 := by
  have h := unit_coefficients_le (fun t ht =>
    quad_eval_le_of_separated hw hH hx₀ hx₁ hx₂ h01 h02 h12 h₀ h₁ h₂ t
      (abs_le.mpr ht))
  exact ⟨by linarith [abs_nonneg a], by linarith [abs_nonneg b], by linarith⟩

/-- Two separated samples bound both coefficients of an affine polynomial. -/
theorem affine_coefficients_le_of_separated {a b D R x₀ x₁ : ℝ}
    (hR : 1 ≤ R) (hx₀ : |x₀| ≤ R)
    (hsep : 1 ≤ R * |x₀ - x₁|)
    (h₀ : |a + b * x₀| ≤ D) (h₁ : |a + b * x₁| ≤ D) :
    |a| ≤ 3 * D * R ^ 2 ∧ |b| ≤ 3 * D * R ^ 2 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans h₀
  have hR0 : 0 ≤ R := by linarith
  have hdiff : |b| * |x₀ - x₁| ≤ 2 * D := by
    calc
      _ = |(a + b * x₀) - (a + b * x₁)| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |a + b * x₀| + |a + b * x₁| := abs_sub _ _
      _ ≤ 2 * D := by linarith
  have hb : |b| ≤ 2 * D * R := by
    calc
      _ ≤ |b| * (R * |x₀ - x₁|) := by nlinarith [abs_nonneg b]
      _ = (|b| * |x₀ - x₁|) * R := by ring
      _ ≤ (2 * D) * R := mul_le_mul_of_nonneg_right hdiff hR0
  have ha : |a| ≤ D + 2 * D * R ^ 2 := by
    calc
      _ = |(a + b * x₀) - b * x₀| := by congr 1; ring
      _ ≤ |a + b * x₀| + |b| * |x₀| := by simpa only [abs_mul] using abs_sub (a + b * x₀) (b * x₀)
      _ ≤ D + (2 * D * R) * R := by gcongr
      _ = D + 2 * D * R ^ 2 := by ring
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  constructor
  · nlinarith [mul_nonneg hD (sub_nonneg.mpr hR2)]
  · calc
      _ ≤ 2 * D * R := hb
      _ ≤ 3 * D * R ^ 2 := by nlinarith [mul_nonneg hD (by nlinarith : 0 ≤ R ^ 2 - R)]

/-- A quadratic small on three separated lines is small on the entire unit box.
The same parameter bounds the affine data and reciprocal velocity separation. -/
theorem three_lines_bound {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R) (b v : Fin 3 → ℝ)
    (hb : ∀ i, |b i| ≤ R) (hv : ∀ i, |v i| ≤ R)
    (hsep : ∀ i j, i ≠ j → 1 ≤ R * |v i - v j|)
    (hline : ∀ i, ∀ t ∈ Icc (-1 : ℝ) 1, |f t (b i + v i * t)| ≤ E)
    (t y : ℝ) (ht : |t| ≤ 1) (hy : |y| ≤ 1) :
    |f t y| ≤ 4000 * E * R ^ 9 := by
  obtain ⟨c, hc⟩ := hf
  have hR0 : 0 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hunit (i : Fin 3) :
      |c 0 + c 2 * b i + c 5 * (b i) ^ 2| ≤ E ∧
      |c 1 + c 2 * v i + c 4 * b i + 2 * c 5 * b i * v i| ≤ E ∧
      |c 3 + c 4 * v i + c 5 * (v i) ^ 2| ≤ 2 * E := by
    apply unit_coefficients_le
    intro s hs
    convert hline i s hs using 1
    congr 1
    rw [hc]
    ring
  have hs (i j : Fin 3) (hij : i ≠ j) : R⁻¹ ≤ |v i - v j| := by
    rw [inv_eq_one_div, div_le_iff₀ hRpos]
    nlinarith [hsep i j hij]
  have hlead := quad_coefficients_le_of_separated (inv_pos.mpr hRpos) hR0
    (hv 0) (hv 1) (hv 2) (hs 0 1 (by decide)) (hs 0 2 (by decide))
    (hs 1 2 (by decide)) (hunit 0).2.2 (hunit 1).2.2 (hunit 2).2.2
  have hscale : ((1 + R) / R⁻¹) ^ 2 ≤ 4 * R ^ 4 := by
    rw [div_inv_eq_mul]
    calc
      _ ≤ (2 * R ^ 2) ^ 2 := by gcongr 1; nlinarith
      _ = 4 * R ^ 4 := by ring
  let K := 48 * E * R ^ 4
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hEK : E ≤ K := by
    have hRp : 1 ≤ R ^ 4 := one_le_pow₀ hR
    dsimp [K]
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hRp)]
  have hleadK : |c 3| ≤ K ∧ |c 4| ≤ K ∧ |c 5| ≤ K := by
    have hbd : 6 * (2 * E) * ((1 + R) / R⁻¹) ^ 2 ≤ K := by
      calc
        _ ≤ 6 * (2 * E) * (4 * R ^ 4) := by gcongr
        _ = K := by dsimp [K]; ring
    exact ⟨hlead.1.trans hbd, hlead.2.1.trans hbd, hlead.2.2.trans hbd⟩
  let D := 4 * K * R ^ 2
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hlinear (i : Fin 3) : |c 1 + c 2 * v i| ≤ D := by
    calc
      _ = |(c 1 + c 2 * v i + c 4 * b i + 2 * c 5 * b i * v i) -
          c 4 * b i - 2 * c 5 * b i * v i| := by congr 1; ring
      _ ≤ |c 1 + c 2 * v i + c 4 * b i + 2 * c 5 * b i * v i| +
          |c 4| * |b i| + 2 * |c 5| * |b i| * |v i| := by
        calc
          _ ≤ |c 1 + c 2 * v i + c 4 * b i + 2 * c 5 * b i * v i| +
              |c 4 * b i| + |2 * c 5 * b i * v i| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_three (c 1 + c 2 * v i + c 4 * b i + 2 * c 5 * b i * v i)
                (-(c 4 * b i)) (-(2 * c 5 * b i * v i))
          _ = _ := by norm_num [abs_mul]
      _ ≤ E + K * R + 2 * K * R * R := by
        gcongr <;> first | exact (hunit i).2.1 | exact hleadK.2.1 | exact hleadK.2.2 | exact hb i | exact hv i
      _ ≤ D := by
        have hR2 : R ≤ R ^ 2 := by nlinarith
        have h1R2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
        dsimp [D]
        nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hR2),
          mul_nonneg hK0 (sub_nonneg.mpr h1R2)]
  have hlin := affine_coefficients_le_of_separated hR (hv 0)
    (hsep 0 1 (by decide)) (hlinear 0) (hlinear 1)
  let B := 625 * E * R ^ 9
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hp49 : R ^ 4 ≤ R ^ 9 := pow_le_pow_right₀ hR (by decide)
  have hp69 : R ^ 6 ≤ R ^ 9 := pow_le_pow_right₀ hR (by decide)
  have hp89 : R ^ 8 ≤ R ^ 9 := pow_le_pow_right₀ hR (by decide)
  have hp19 : 1 ≤ R ^ 9 := one_le_pow₀ hR
  have hKB : K ≤ B := by dsimp [K, B]; nlinarith [mul_nonneg hE (sub_nonneg.mpr hp49)]
  have hlinB : 3 * D * R ^ 2 ≤ B := by
    dsimp [D, K, B]
    have : 0 ≤ E * (R ^ 9 - R ^ 8) := mul_nonneg hE (sub_nonneg.mpr hp89)
    nlinarith
  have hcoeff : ∀ i, |c i| ≤ B := by
    intro i
    fin_cases i
    · change |c 0| ≤ B
      calc
        _ = |(c 0 + c 2 * b 0 + c 5 * (b 0) ^ 2) - c 2 * b 0 -
            c 5 * (b 0) ^ 2| := by congr 1; ring
        _ ≤ |c 0 + c 2 * b 0 + c 5 * (b 0) ^ 2| + |c 2| * |b 0| +
            |c 5| * |b 0| ^ 2 := by
          have hh := abs_add_three (c 0 + c 2 * b 0 + c 5 * (b 0) ^ 2)
            (-(c 2 * b 0)) (-(c 5 * (b 0) ^ 2))
          simp only [abs_neg] at hh
          simpa only [sub_eq_add_neg, abs_mul, abs_pow] using hh
        _ ≤ E + (3 * D * R ^ 2) * R + K * R ^ 2 := by
          gcongr
          · exact (hunit 0).1
          · exact hlin.2
          · exact hb 0
          · exact hleadK.2.2
          · exact hb 0
        _ ≤ B := by
          dsimp [B, D, K]
          nlinarith [mul_nonneg hE (sub_nonneg.mpr hp69),
            mul_nonneg hE (sub_nonneg.mpr hp19)]
    · exact hlin.1.trans hlinB
    · exact hlin.2.trans hlinB
    · exact hleadK.1.trans hKB
    · exact hleadK.2.1.trans hKB
    · exact hleadK.2.2.trans hKB
  rw [hc]
  calc
    _ ≤ |c 0| + |c 1| * |t| + |c 2| * |y| + |c 3| * |t| ^ 2 +
        |c 4| * (|t| * |y|) + |c 5| * |y| ^ 2 := by
      calc
        _ ≤ |c 0| + |c 1 * t| + |c 2 * y| + |c 3 * t ^ 2| +
            |c 4 * (t * y)| + |c 5 * y ^ 2| := by
          exact (abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add
                ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)
        _ = _ := by simp only [abs_mul, abs_pow]
    _ ≤ B + B * 1 + B * 1 + B * 1 ^ 2 + B * (1 * 1) + B * 1 ^ 2 := by gcongr <;> apply hcoeff
    _ ≤ 4000 * E * R ^ 9 := by dsimp [B]; nlinarith [mul_nonneg hE (pow_nonneg hR0 9)]

/-- If a quadratic is large somewhere on the unit box, its small line restrictions
have velocities in two intervals of radius `R⁻¹`. -/
theorem bad_quadratic_velocity_cover {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    {E R : ℝ} (hE : 0 ≤ E) (hR : 1 ≤ R) (S : Set (ℝ × ℝ))
    (hbound : ∀ q ∈ S, |q.1| ≤ R ∧ |q.2| ≤ R)
    (hline : ∀ q ∈ S, ∀ t ∈ Icc (-1 : ℝ) 1, |f t (q.1 + q.2 * t)| ≤ E)
    (hlarge : ∃ t y : ℝ, |t| ≤ 1 ∧ |y| ≤ 1 ∧ 4000 * E * R ^ 9 < |f t y|) :
    ∃ v₀ v₁ : ℝ, ∀ q ∈ S, |q.2 - v₀| < R⁻¹ ∨ |q.2 - v₁| < R⁻¹ := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hS
    by_cases hone : ∀ q ∈ S, |q.2 - q₀.2| < R⁻¹
    · exact ⟨q₀.2, q₀.2, fun q hq => Or.inl (hone q hq)⟩
    push Not at hone
    obtain ⟨q₁, hq₁, hsep01⟩ := hone
    refine ⟨q₀.2, q₁.2, ?_⟩
    intro q₂ hq₂
    by_contra h
    push Not at h
    obtain ⟨t, y, ht, hy, hbig⟩ := hlarge
    have hRpos : 0 < R := by linarith
    have hconvert (z : ℝ) (hz : R⁻¹ ≤ |z|) : 1 ≤ R * |z| := by
      rw [inv_eq_one_div, div_le_iff₀ hRpos] at hz
      nlinarith
    have h01 : 1 ≤ R * |q₀.2 - q₁.2| := by
      rw [abs_sub_comm]
      exact hconvert _ hsep01
    have h02 : 1 ≤ R * |q₀.2 - q₂.2| := by
      rw [abs_sub_comm]
      exact hconvert _ h.1
    have h12 : 1 ≤ R * |q₁.2 - q₂.2| := by
      rw [abs_sub_comm]
      exact hconvert _ h.2
    have hsmall := three_lines_bound hf hE hR
      ![q₀.1, q₁.1, q₂.1] ![q₀.2, q₁.2, q₂.2]
      (by intro i; fin_cases i <;> simp <;>
        first | exact (hbound q₀ hq₀).1 | exact (hbound q₁ hq₁).1 | exact (hbound q₂ hq₂).1)
      (by intro i; fin_cases i <;> simp <;>
        first | exact (hbound q₀ hq₀).2 | exact (hbound q₁ hq₁).2 | exact (hbound q₂ hq₂).2)
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> try { norm_num at hij } <;> norm_num
        all_goals first | exact h01 | exact h02 | exact h12 |
          simpa only [abs_sub_comm] using h01 | simpa only [abs_sub_comm] using h02 |
          simpa only [abs_sub_comm] using h12)
      (by
        intro i s hs
        fin_cases i
        · exact hline q₀ hq₀ s hs
        · exact hline q₁ hq₁ s hs
        · exact hline q₂ hq₂ s hs)
      t y ht hy
    exact (not_lt_of_ge hsmall) hbig
  · exact ⟨0, 0, fun q hq => (hS ⟨q, hq⟩).elim⟩

/-- Independent affine changes of the two coordinates preserve quadratic form. -/
theorem isQuad2_affine_rescale {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f)
    (a b c d : ℝ) : IsQuad2 (fun t y => f (a + b * t) (c + d * y)) := by
  obtain ⟨k, hk⟩ := hf
  refine ⟨![k 0 + k 1 * a + k 2 * c + k 3 * a ^ 2 + k 4 * (a * c) + k 5 * c ^ 2,
    k 1 * b + 2 * k 3 * a * b + k 4 * b * c,
    k 2 * d + k 4 * a * d + 2 * k 5 * c * d,
    k 3 * b ^ 2, k 4 * b * d, k 5 * d ^ 2], ?_⟩
  intro t y
  norm_num [Matrix.cons_val]
  rw [hk]
  ring

set_option maxHeartbeats 800000 in
/-- The three-line estimate in physical time and spatial coordinates. -/
theorem three_lines_centered_box_bound (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : Q.totalDegree ≤ 2) {q E H w m c : ℝ}
    (hq : 0 < q) (hE : 0 ≤ E) (hH : 1 ≤ H) (hw : 0 < w) (hw1 : w ≤ 1)
    (α β : Fin 3 → ℝ) (hβ : ∀ i, |β i| ≤ H)
    (hα : ∀ i, |α i + β i * m - c| ≤ H * q)
    (hsep : ∀ i j, i ≠ j → w ≤ |β i - β j|)
    (hline : ∀ i, ∀ t : ℝ, |t - m| ≤ q / 2 →
      |MvPolynomial.eval ![t, α i + t * β i] Q| ≤ E)
    (t z : ℝ) (ht : |t - m| ≤ q / 2) (hz : |z - c| ≤ q) :
    |MvPolynomial.eval ![t, z] Q| ≤ 2048000 * E * H ^ 9 / w ^ 9 := by
  let R := 2 * H / w
  have hH0 : 0 ≤ H := by linarith
  have hR : 1 ≤ R := by dsimp [R]; rw [le_div_iff₀ hw]; linarith
  have hHR : H ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ hw]
    nlinarith [mul_nonneg hH0 (sub_nonneg.mpr hw1)]
  let f : ℝ → ℝ → ℝ := fun s y =>
    MvPolynomial.eval ![m + (q / 2) * s, c + q * y] Q
  have hf : IsQuad2 f := isQuad2_affine_rescale (isQuad2_eval Q hQ) m (q / 2) c q
  let b : Fin 3 → ℝ := fun i => (α i + β i * m - c) / q
  let v : Fin 3 → ℝ := fun i => β i / 2
  have hb : ∀ i, |b i| ≤ R := by
    intro i
    apply le_trans _ hHR
    dsimp [b]
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    exact hα i
  have hv : ∀ i, |v i| ≤ R := by
    intro i
    apply le_trans _ hHR
    dsimp [v]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    linarith [hβ i]
  have hs : ∀ i j, i ≠ j → 1 ≤ R * |v i - v j| := by
    intro i j hij
    have habs : |v i - v j| = |β i - β j| / 2 := by
      dsimp [v]
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs]
    dsimp [R]
    have hsep' := hsep i j hij
    have hh : w ≤ H * |β i - β j| := by
      nlinarith [abs_nonneg (β i - β j)]
    apply (le_of_eq (by simp only [div_self (ne_of_gt hw)] : (1 : ℝ) = w / w)).trans
    calc
      w / w ≤ (H * |β i - β j|) / w := (div_le_div_iff_of_pos_right hw).mpr hh
      _ = 2 * H / w * (|β i - β j| / 2) := by ring
  have hl : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, |f s (b i + v i * s)| ≤ E := by
    intro i s hs
    have htime : |m + (q / 2) * s - m| ≤ q / 2 := by
      calc
        _ = (q / 2) * |s| := by rw [add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
        _ ≤ (q / 2) * 1 := by gcongr; exact abs_le.mpr hs
        _ = q / 2 := mul_one _
    have hspace : c + q * (b i + v i * s) = α i + (m + (q / 2) * s) * β i := by
      dsimp [b, v]
      field_simp
      ring
    dsimp [f]
    rw [hspace]
    exact hline i (m + (q / 2) * s) htime
  have htime : |(t - m) / (q / 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos (show 0 < q / 2 by positivity), div_le_one (show 0 < q / 2 by positivity)]
    exact ht
  have hspace : |(z - c) / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hq, div_le_one hq]
    exact hz
  have hmain := three_lines_bound hf hE hR b v hb hv hs hl
    ((t - m) / (q / 2)) ((z - c) / q) htime hspace
  have heval : f ((t - m) / (q / 2)) ((z - c) / q) = MvPolynomial.eval ![t, z] Q := by
    have htime : m + q / 2 * ((t - m) / (q / 2)) = t := by field_simp; ring
    have hspace : c + q * ((z - c) / q) = z := by field_simp; ring
    dsimp [f]
    rw [htime, hspace]
  rw [heval] at hmain
  have hconstant : 4000 * E * R ^ 9 = 2048000 * E * H ^ 9 / w ^ 9 := by
    dsimp [R]
    rw [div_pow, mul_pow]
    norm_num
    ring
  exact hmain.trans_eq hconstant

/-- Absolute-value formulation of the unit-box three-line estimate. -/
theorem three_line_bound (f : ℝ → ℝ → ℝ) (hf : IsQuad2 f)
    {R E : ℝ} (hR : 1 ≤ R) (hE : 0 ≤ E) (b v : Fin 3 → ℝ)
    (hb : ∀ i, |b i| ≤ R) (hv : ∀ i, |v i| ≤ R)
    (hsep : ∀ i j, i ≠ j → 1 ≤ R * |v i - v j|)
    (hline : ∀ i t, |t| ≤ 1 → |f t (b i + v i * t)| ≤ E) :
    ∀ t y, |t| ≤ 1 → |y| ≤ 1 → |f t y| ≤ 4000 * E * R ^ 9 := by
  intro t y ht hy
  exact three_lines_bound hf hE hR b v hb hv hsep
    (fun i s hs => hline i s (abs_le.mpr hs)) t y ht hy

end Submission.Obl.k4_scalar_angular_pair_agreement
