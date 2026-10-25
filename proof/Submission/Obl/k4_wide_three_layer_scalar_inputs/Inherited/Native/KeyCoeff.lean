/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/KeyCoeff.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortCaps

set_option autoImplicit false

/-!
# Normalized key coefficients: bounds

Coefficients of a quadratic bounded by `S` on `[0,1] × [-1,1]` are at most `8 S`
(accepted `quadratic_coefficients_bound`); this bounds the key coefficients of block graphs and
projected sheets.  Also the affine coefficients of a true block are bounded from one of its
labels.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem quadCoeff_bound {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) {S : ℝ}
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |f t y| ≤ S) :
    ∀ e, |quadCoeff f e| ≤ 8 * S := by
  apply quadratic_coefficients_bound
  intro t ht y hy
  have := quad2_quadCoeff hf t y
  rw [← quad2_eq, this]
  exact hS t ht y hy

/-- Values of a strip quadratic with coefficients `≤ H` at `|t| ≤ 1`, `|η| ≤ 2`. -/
theorem abs_quad2_le_two {F : Fin 6 → ℝ} {H : ℝ} (hF : ∀ k, |F k| ≤ H) {t η : ℝ}
    (ht : |t| ≤ 1) (hη : |η| ≤ 2) : |quad2 F t η| ≤ 11 * H := by
  have hH : 0 ≤ H := (abs_nonneg _).trans (hF 0)
  have h1 : |F 1 * t| ≤ H := by
    rw [abs_mul]; nlinarith [abs_nonneg (F 1), abs_nonneg t, hF 1]
  have h2 : |F 2 * η| ≤ 2 * H := by
    rw [abs_mul]; nlinarith [abs_nonneg (F 2), abs_nonneg η, hF 2]
  have h3 : |F 3 * t ^ 2| ≤ H := by
    rw [abs_mul, abs_pow]
    have : |t| ^ 2 ≤ 1 := by nlinarith [abs_nonneg t]
    nlinarith [abs_nonneg (F 3), hF 3, sq_nonneg |t|]
  have h4 : |F 4 * (t * η)| ≤ 2 * H := by
    rw [abs_mul, abs_mul]
    have : |t| * |η| ≤ 2 := by nlinarith [abs_nonneg t, abs_nonneg η]
    nlinarith [abs_nonneg (F 4), hF 4, mul_nonneg (abs_nonneg t) (abs_nonneg η)]
  have h5 : |F 5 * η ^ 2| ≤ 4 * H := by
    rw [abs_mul, abs_pow]
    have : |η| ^ 2 ≤ 4 := by nlinarith [abs_nonneg η]
    nlinarith [abs_nonneg (F 5), hF 5, sq_nonneg |η|]
  have h0 := hF 0
  unfold quad2
  calc |F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2 + F 4 * (t * η) + F 5 * η ^ 2|
      ≤ |F 0| + |F 1 * t| + |F 2 * η| + |F 3 * t ^ 2| + |F 4 * (t * η)| + |F 5 * η ^ 2| := by
        have := abs_add_le (F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2 + F 4 * (t * η)) (F 5 * η ^ 2)
        have := abs_add_le (F 0 + F 1 * t + F 2 * η + F 3 * t ^ 2) (F 4 * (t * η))
        have := abs_add_le (F 0 + F 1 * t + F 2 * η) (F 3 * t ^ 2)
        have := abs_add_le (F 0 + F 1 * t) (F 2 * η)
        have := abs_add_le (F 0) (F 1 * t)
        linarith
    _ ≤ 11 * H := by linarith

/-- **Block key coefficients.**  On the key domain `|Z| ≤ Zb`, `|Y| ≤ Yb`. -/
theorem blockKeyCoeff_bound {F : MvPolynomial (Fin 4) ℝ} {Lc : Fin 4 → ℝ}
    (hF : HorizontalForm F Lc) {Lb : ℝ} (hLb : ∀ e, |Lc e| ≤ Lb)
    {a χ m q t₀ Zb Yb : ℝ} (ha : 0 < a) (κ : Fin 3 → ℤ)
    (ht : ∀ τ ∈ Icc (0 : ℝ) 1, |t₀ + q * τ| ≤ 1)
    (hZ : ∀ τ ∈ Icc (0 : ℝ) 1, |domZ χ κ (t₀ + q * τ)| ≤ Zb)
    (hY : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1, |domY χ m q κ τ y| ≤ Yb) :
    ∀ e, |blockKeyCoeff F a χ m q t₀ κ e| ≤ 8 * (Lb * (2 + Zb + Yb) / a) := by
  apply quadCoeff_bound (isQuad2_blockKey hF a χ m q t₀ κ)
  intro τ hτ y hy
  have hL : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
  rw [blockGraph_eq hF, abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  have h1 := ht τ hτ
  have h2 := hZ τ hτ
  have h3 := hY τ hτ y hy
  have hZb : 0 ≤ Zb := (abs_nonneg _).trans h2
  have hYb : 0 ≤ Yb := (abs_nonneg _).trans h3
  calc |Lc 0 + Lc 1 * (t₀ + q * τ) + Lc 2 * domZ χ κ (t₀ + q * τ) + Lc 3 * domY χ m q κ τ y|
      ≤ |Lc 0| + |Lc 1| * |t₀ + q * τ| + |Lc 2| * |domZ χ κ (t₀ + q * τ)| +
          |Lc 3| * |domY χ m q κ τ y| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        have := abs_add_le (Lc 0 + Lc 1 * (t₀ + q * τ) + Lc 2 * domZ χ κ (t₀ + q * τ))
          (Lc 3 * domY χ m q κ τ y)
        have := abs_add_le (Lc 0 + Lc 1 * (t₀ + q * τ)) (Lc 2 * domZ χ κ (t₀ + q * τ))
        have := abs_add_le (Lc 0) (Lc 1 * (t₀ + q * τ))
        linarith
    _ ≤ Lb + Lb * 1 + Lb * Zb + Lb * Yb := by
        gcongr
        · exact hLb 0
        · exact hLb 1
        · exact hLb 2
        · exact hLb 3
    _ ≤ Lb * (2 + Zb + Yb) := by nlinarith

/-- **Sheet key coefficients.**  The key domain lies in the doubled strip of the sheet. -/
theorem sheetKeyCoeff_bound {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    {y₀ v D H : ℝ} (hD : 0 < D) (hH : ∀ k', |sheetCoeff G y₀ v D k'| ≤ H)
    {a χ m q t₀ : ℝ} (ha : 0 < a) (κ : Fin 3 → ℤ)
    (ht : ∀ τ ∈ Icc (0 : ℝ) 1, |t₀ + q * τ| ≤ 1)
    (hη : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |etaFun y₀ v D (t₀ + q * τ) (domY χ m q κ τ y)| ≤ 2) :
    ∀ e, |sheetKeyCoeff G a χ m q t₀ κ e| ≤ 8 * (11 * H / a) := by
  apply quadCoeff_bound (isQuad2_sheetKey hG a χ m q t₀ κ)
  intro τ hτ y hy
  rw [abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  rw [← quad2_sheetCoeff_etaFun hG hD.ne']
  exact abs_quad2_le_two hH (ht τ hτ) (hη τ hτ y hy)

/-- **Affine coefficients of a true block**, from one label of the block. -/
theorem block_affine_bound {Lc : Fin 4 → ℝ} {K Λ a Xb x₁ x₂ x₃ t : ℝ}
    (hK : 1 ≤ K) (hΛ : 1 ≤ Λ) (hXb : 1 ≤ Xb) (ht : 0 ≤ t ∧ t ≤ 1) (hKa : K * a ≤ 1)
    (h3 : |Lc 3| ≤ K * Λ) (h12 : |Lc 1 - x₁ * Lc 3| + |Lc 2 + t * Lc 3| ≤ K * Λ)
    (hx₁ : |x₁| ≤ Xb) (hx₂ : |x₂| ≤ Xb) (hx₃ : |x₃| ≤ Xb)
    (hfit : |x₃ - (Lc 0 + Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂)| ≤ K * a) :
    ∀ e, |Lc e| ≤ 12 * Xb ^ 2 * (K * Λ) := by
  have hKΛ : 1 ≤ K * Λ := by nlinarith
  have hXb2 : Xb ≤ Xb ^ 2 := by nlinarith
  have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hp1 := (abs_nonneg (Lc 2 + t * Lc 3))
  have hp2 := (abs_nonneg (Lc 1 - x₁ * Lc 3))
  have b2 : |Lc 2| ≤ 2 * (K * Λ) := by
    calc |Lc 2| = |(Lc 2 + t * Lc 3) - t * Lc 3| := by ring_nf
      _ ≤ |Lc 2 + t * Lc 3| + |t * Lc 3| := abs_sub _ _
      _ = |Lc 2 + t * Lc 3| + |t| * |Lc 3| := by rw [abs_mul]
      _ ≤ K * Λ + 1 * (K * Λ) := by
          gcongr
          linarith
      _ = 2 * (K * Λ) := by ring
  have b1 : |Lc 1| ≤ 2 * Xb * (K * Λ) := by
    calc |Lc 1| = |(Lc 1 - x₁ * Lc 3) + x₁ * Lc 3| := by ring_nf
      _ ≤ |Lc 1 - x₁ * Lc 3| + |x₁ * Lc 3| := abs_add_le _ _
      _ = |Lc 1 - x₁ * Lc 3| + |x₁| * |Lc 3| := by rw [abs_mul]
      _ ≤ K * Λ + Xb * (K * Λ) := by
          gcongr
          linarith
      _ ≤ 2 * Xb * (K * Λ) := by nlinarith
  have b0 : |Lc 0| ≤ 12 * Xb ^ 2 * (K * Λ) := by
    have e : Lc 0 = x₃ - (Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂) -
        (x₃ - (Lc 0 + Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂)) := by ring
    rw [e]
    have t1 : |Lc 1 * t| ≤ 2 * Xb * (K * Λ) := by
      rw [abs_mul]; nlinarith [abs_nonneg (Lc 1), abs_nonneg t]
    have t2 : |Lc 2 * x₁| ≤ 2 * (K * Λ) * Xb := by
      rw [abs_mul]; exact mul_le_mul b2 hx₁ (abs_nonneg _) (by linarith)
    have t3 : |Lc 3 * x₂| ≤ (K * Λ) * Xb := by
      rw [abs_mul]; exact mul_le_mul h3 hx₂ (abs_nonneg _) (by linarith)
    calc |x₃ - (Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂) -
          (x₃ - (Lc 0 + Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂))|
        ≤ |x₃| + (|Lc 1 * t| + |Lc 2 * x₁| + |Lc 3 * x₂|) + K * a := by
          have := abs_sub (x₃ - (Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂))
            (x₃ - (Lc 0 + Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂))
          have := abs_sub x₃ (Lc 1 * t + Lc 2 * x₁ + Lc 3 * x₂)
          have := abs_add_le (Lc 1 * t + Lc 2 * x₁) (Lc 3 * x₂)
          have := abs_add_le (Lc 1 * t) (Lc 2 * x₁)
          linarith
      _ ≤ Xb + (2 * Xb * (K * Λ) + 2 * (K * Λ) * Xb + (K * Λ) * Xb) + 1 := by
          gcongr
      _ ≤ 12 * Xb ^ 2 * (K * Λ) := by nlinarith
  intro e
  fin_cases e
  · exact b0
  · exact b1.trans (by nlinarith)
  · exact b2.trans (by nlinarith)
  · exact h3.trans (by nlinarith)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
