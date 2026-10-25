import Submission.Obl.k4_wide_three_layer_scalar_inputs.QuadraticOffsets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.OffsetFreezing
import Submission.Obl.k4_wide_three_layer_scalar_inputs.StripEnlargement
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Keys

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial
open Inherited.Native Inherited.MatchGML2D Inherited.CompareSheets
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- A norm bound for the actual difference over a key domain is a
coefficient ball at that domain's own hidden accuracy. -/
theorem sheet_key_difference_coefficients {G H : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (hH : H.totalDegree ≤ 2)
    {a χ m q t₀ W : ℝ} (ha : 0 < a) (κ : Fin 3 → ℤ)
    (hbound : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![t₀ + q * τ, domY χ m q κ τ y] G -
        eval ![t₀ + q * τ, domY χ m q κ τ y] H| ≤ W) :
    ∀ e, |sheetKeyCoeff G a χ m q t₀ κ e - sheetKeyCoeff H a χ m q t₀ κ e| ≤
      8 * (W / a) := by
  apply quadratic_difference_coefficients
  intro τ hτ y hy
  rw [← quad2_eq, ← quad2_eq, quad2_sheetKeyCoeff hG, quad2_sheetKeyCoeff hH,
    ← sub_div, abs_div, abs_of_pos ha]
  exact div_le_div_of_nonneg_right (hbound τ hτ y hy) ha.le

/-- One label in a key places its entire key box inside a fixed
constant enlargement of its original long strip. -/
theorem key_tube_of_label {α : Type} [MeasurableSpace α] {b : α → Fin 6 → ℝ}
    {χ m q t₀ D u ζ : ℝ} {κ : Fin 3 → ℤ} {l : α}
    (hm : 0 < m) (hD : 0 < D) (hmD : m ≤ D) (ht₀ : t₀ ∈ Icc (0 : ℝ) 1)
    (hκ : slotKey b χ m t₀ l = κ)
    (hintercept : |b l 1 - u| ≤ D)
    (hvelocity : |b l 4 + (κ 1 : ℝ) * χ| ≤ ζ) (hζ : ζ ≤ D / 4) :
    ∀ τ : ℝ, ∀ y ∈ Icc (-1 : ℝ) 1,
      |domY χ m q κ τ y - u + (t₀ + q * τ) * ((κ 1 : ℝ) * χ)| ≤ 8 * D := by
  intro τ y hy
  have hstart := label_Y_eq (q := q) hm.ne' hκ 0
  simp only [mul_zero, add_zero, zero_mul] at hstart
  have heq : domY χ m q κ τ y - u + (t₀ + q * τ) * ((κ 1 : ℝ) * χ) =
      (b l 1 - u) + t₀ * (b l 4 + (κ 1 : ℝ) * χ) +
        2 * m * (y - sliceY b m t₀ l) := by
    have hstart' : b l 1 + t₀ * b l 4 = domY χ m q κ 0 (sliceY b m t₀ l) := hstart
    calc _ = (b l 1 + t₀ * b l 4) - u + t₀ * ((κ 1 : ℝ) * χ) +
          2 * m * (y - sliceY b m t₀ l) := by rw [hstart']; unfold domY; ring
      _ = _ := by ring
  have hyabs : |y| ≤ 1 := abs_le.mpr hy
  have hs := sliceY_mem b m t₀ l
  have hsabs : |sliceY b m t₀ l| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have ht : |t₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht₀.1, ht₀.2]
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hvelocity
  have hys : |y - sliceY b m t₀ l| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  have htime : |t₀ * (b l 4 + (κ 1 : ℝ) * χ)| ≤ ζ := by
    rw [abs_mul]
    exact (mul_le_mul ht hvelocity (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have htrans : |2 * m * (y - sliceY b m t₀ l)| ≤ 4 * m := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * m)]
    nlinarith
  rw [heq]
  calc _ ≤ |(b l 1 - u) + t₀ * (b l 4 + (κ 1 : ℝ) * χ)| +
        |2 * m * (y - sliceY b m t₀ l)| := abs_add_le _ _
    _ ≤ D + ζ + 4 * m := by
      exact add_le_add ((abs_add_le _ _).trans (add_le_add hintercept htime)) htrans
    _ ≤ 8 * D := by linarith

/-- Freeze a difference on a whole key box at its fixed corner. The
long norm is supplied before any source/target intersection is selected. -/
theorem difference_freezes_on_key {G H : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (hH : H.totalDegree ≤ 2)
    {χ m q t₀ D u E : ℝ} (hD : 0 < D) (hm : 0 < m) (hq : 0 < q)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1) (κ : Fin 3 → ℤ)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u - t * ((κ 1 : ℝ) * χ) + D * w] (G - H)| ≤ E)
    (htube : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |domY χ m q κ τ y - u + (t₀ + q * τ) * ((κ 1 : ℝ) * χ)| ≤ D) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![t₀ + q * τ, domY χ m q κ τ y] (G - H) -
        eval ![t₀, domY χ m q κ 0 0] (G - H)| ≤ 32 * E * (q + 2 * m / D) := by
  intro τ hτ y hy
  have hdeg : (G - H).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub G H).trans (max_le hG hH)
  apply moving_strip_freezing (G - H) hdeg hD hnorm
    (ht₀ := ⟨hunit.1, by linarith [hunit.2]⟩)
    (ht := ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩)
    (hY₀ := by simpa using htube 0 ⟨le_rfl, zero_le_one⟩ 0 (by norm_num))
    (hY := htube τ hτ y hy)
  · rw [show t₀ + q * τ - t₀ = q * τ by ring, abs_mul,
      abs_of_pos hq, abs_of_nonneg hτ.1]
    nlinarith [hτ.2]
  · have heq : domY χ m q κ τ y - domY χ m q κ 0 0 +
        (κ 1 : ℝ) * χ * (t₀ + q * τ - t₀) = 2 * m * y := by unfold domY; ring
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * m)]
    have hyabs : |y| ≤ 1 := abs_le.mpr hy
    nlinarith

/-- The whole key may lie in the fixed enlarged long strip. Enlargement
changes only the absolute constant in the variation estimate. -/
theorem difference_freezes_on_enlarged_key {G H : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (hH : H.totalDegree ≤ 2)
    {χ m q t₀ D u E : ℝ} (hD : 0 < D) (hm : 0 < m) (hq : 0 < q) (hE : 0 ≤ E)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1) (κ : Fin 3 → ℤ)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u - t * ((κ 1 : ℝ) * χ) + D * w] (G - H)| ≤ E)
    (htube : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |domY χ m q κ τ y - u + (t₀ + q * τ) * ((κ 1 : ℝ) * χ)| ≤ 8 * D) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |eval ![t₀ + q * τ, domY χ m q κ τ y] (G - H) -
        eval ![t₀, domY χ m q κ 0 0] (G - H)| ≤ 98304 * E * (q + m / D) := by
  have hdeg : (G - H).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub G H).trans (max_le hG hH)
  have hnorm' := moving_strip_enlarged_norm (G - H) hdeg hE hD (by norm_num : (1 : ℝ) ≤ 8)
    (u := u) (v := -((κ 1 : ℝ) * χ)) (by
      intro t ht w hw
      convert hnorm t ht w hw using 4 <;> ring)
  intro τ hτ y hy
  have h := difference_freezes_on_key hG hH (D := 8 * D) (by positivity) hm hq hunit κ
    (E := 48 * E * 8 ^ 2) (by
      intro t ht w hw
      convert hnorm' t ht w hw using 4 <;> ring) htube τ hτ y hy
  calc _ ≤ 32 * (48 * E * 8 ^ 2) * (q + 2 * m / (8 * D)) := h
    _ = 98304 * E * (q + m / (4 * D)) := by field_simp; ring
    _ ≤ 98304 * E * (q + m / D) := by gcongr <;> linarith

/-- A retained common sample bounds the corner offset in the coarse
physical units. Only the earlier marginal floors will be used to count it. -/
theorem key_offset_bound_from_label {α : Type} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} {l : α} {G H : MvPolynomial (Fin 2) ℝ}
    (hG : G.totalDegree ≤ 2) (hH : H.totalDegree ≤ 2)
    {χ m q t₀ D u E ζ t X Ecoarse Efine : ℝ} {κ : Fin 3 → ℤ}
    (hD : 0 < D) (hm : 0 < m) (hmD : m ≤ D) (hq : 0 < q) (hE : 0 ≤ E)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1) (ht : t ∈ Icc t₀ (t₀ + q))
    (hκ : slotKey b χ m t₀ l = κ) (hintercept : |b l 1 - u| ≤ D)
    (hvelocity : |b l 4 + (κ 1 : ℝ) * χ| ≤ ζ) (hζ : ζ ≤ D / 4)
    (hsmall : q * ζ ≤ m / 2)
    (hnorm : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![τ, u - τ * ((κ 1 : ℝ) * χ) + D * w] (G - H)| ≤ E)
    (hcoarse : |X - eval ![t, b l 1 + t * b l 4] H| ≤ Ecoarse)
    (hfine : |X - eval ![t, b l 1 + t * b l 4] G| ≤ Efine) :
    |eval ![t₀, domY χ m q κ 0 0] (G - H)| ≤
      Ecoarse + Efine + 98304 * E * (q + m / D) := by
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hvelocity
  have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨hunit.1.trans ht.1, ht.2.trans hunit.2⟩
  have ht₀ : t₀ ∈ Icc (0 : ℝ) 1 := ⟨hunit.1, by linarith [hunit.2]⟩
  have ht0abs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [htunit.1, htunit.2]
  have hdt : |t - t₀| ≤ q := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hpoint : |b l 1 + t * b l 4 - u + t * ((κ 1 : ℝ) * χ)| ≤ 8 * D := by
    have heq : b l 1 + t * b l 4 - u + t * ((κ 1 : ℝ) * χ) =
        (b l 1 - u) + t * (b l 4 + (κ 1 : ℝ) * χ) := by ring
    rw [heq]
    have htime : |t * (b l 4 + (κ 1 : ℝ) * χ)| ≤ ζ := by
      rw [abs_mul]
      exact (mul_le_mul ht0abs hvelocity (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact ((abs_add_le _ _).trans (add_le_add hintercept htime)).trans (by linarith)
  have hstart := label_Y_eq (q := q) hm.ne' hκ 0
  simp only [mul_zero, add_zero, zero_mul] at hstart
  have htrans : |(b l 1 + t * b l 4 - domY χ m q κ 0 0) +
      (κ 1 : ℝ) * χ * (t - t₀)| ≤ 2 * m := by
    have heq : (b l 1 + t * b l 4 - domY χ m q κ 0 0) +
        (κ 1 : ℝ) * χ * (t - t₀) =
        2 * m * sliceY b m t₀ l + (t - t₀) * (b l 4 + (κ 1 : ℝ) * χ) := by
      have hstart' := hstart
      unfold domY at hstart' ⊢
      nlinarith only [hstart']
    have hs := sliceY_mem b m t₀ l
    have hsabs : |sliceY b m t₀ l| ≤ 3 / 4 := by
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    have h1 : |2 * m * sliceY b m t₀ l| ≤ 3 * m / 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * m)]
      nlinarith
    have h2 : |(t - t₀) * (b l 4 + (κ 1 : ℝ) * χ)| ≤ q * ζ := by
      rw [abs_mul]
      exact mul_le_mul hdt hvelocity (abs_nonneg _) hq.le
    rw [heq]
    exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans (by linarith)
  have hdeg : (G - H).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub G H).trans (max_le hG hH)
  have hnorm' := moving_strip_enlarged_norm (G - H) hdeg hE hD (by norm_num : (1 : ℝ) ≤ 8)
    (u := u) (v := -((κ 1 : ℝ) * χ)) (by
      intro τ hτ w hw
      convert hnorm τ hτ w hw using 4 <;> ring)
  have hcorner : |domY χ m q κ 0 0 - u + t₀ * ((κ 1 : ℝ) * χ)| ≤ 8 * D := by
    simpa using key_tube_of_label hm hD hmD ht₀ hκ hintercept hvelocity hζ 0 0 (by norm_num)
  have hfreeze := moving_strip_freezing (G - H) hdeg (D := 8 * D) (by positivity)
    (E := 48 * E * 8 ^ 2) (by
      intro τ hτ w hw
      convert hnorm' τ hτ w hw using 4 <;> ring) ht₀ htunit hcorner hpoint hdt htrans
  have hfreeze' : |eval ![t, b l 1 + t * b l 4] G - eval ![t, b l 1 + t * b l 4] H -
      eval ![t₀, domY χ m q κ 0 0] (G - H)| ≤ 98304 * E * (q + m / D) := by
    simp only [map_sub] at hfreeze ⊢
    calc _ ≤ 32 * (48 * E * 8 ^ 2) * (q + 2 * m / (8 * D)) := hfreeze
      _ = 98304 * E * (q + m / (4 * D)) := by field_simp; ring
      _ ≤ 98304 * E * (q + m / D) := by gcongr <;> linarith
  exact frozen_offset_bound hcoarse hfine hfreeze'

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
