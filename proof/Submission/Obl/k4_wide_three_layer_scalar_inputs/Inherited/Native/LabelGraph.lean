/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/LabelGraph.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.KeyCoeff

set_option autoImplicit false

/-!
# A label of a key follows the key graphs of its block and of its pieces

For a label of key `κ` (slot start `t₀`, slot length `q`) with transverse velocity defect
`|b₄ + b₀| ≤ ζ`, at every normalized time `τ ∈ [0,1]` its hidden value is within
* `W + Lb (2χ + q(ζ+χ))` of `a · quad2 (blockKeyCoeff F …) τ y` when the block fit holds with
  error `W` (`block_label_graph`),
* `W + 7 H q (ζ + χ) / (4 D)` of `a · quad2 (sheetKeyCoeff G …) τ y` when the sheet fit holds
  with error `W` (`sheet_label_graph`),
where `y = sliceY` is the label's slice coordinate.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The transverse velocity defect of a key label. -/
theorem key_velocity_defect {b : α → Fin 6 → ℝ} {χ m t₀ ζ : ℝ} (hχ : 0 < χ) {l : α}
    {κ : Fin 3 → ℤ} (hκ : slotKey b χ m t₀ l = κ) (hζ : |b l 4 + b l 0| ≤ ζ) :
    |b l 4 + (κ 1 : ℝ) * χ| ≤ ζ + χ := by
  have hb0 := label_b0_near hχ hκ
  calc |b l 4 + (κ 1 : ℝ) * χ| = |(b l 4 + b l 0) - (b l 0 - (κ 1 : ℝ) * χ)| := by ring_nf
    _ ≤ |b l 4 + b l 0| + |b l 0 - (κ 1 : ℝ) * χ| := abs_sub _ _
    _ ≤ ζ + χ := add_le_add hζ hb0

/-- The transverse position of a key label against the key motion, during the slot. -/
theorem key_Y_near {b : α → Fin 6 → ℝ} {χ m q t₀ ζ : ℝ} (hχ : 0 < χ) (hm : m ≠ 0) (hq : 0 ≤ q)
    {l : α} {κ : Fin 3 → ℤ} (hκ : slotKey b χ m t₀ l = κ) (hζ : |b l 4 + b l 0| ≤ ζ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    |b l 1 + (t₀ + q * τ) * b l 4 - domY χ m q κ τ (sliceY b m t₀ l)| ≤ q * (ζ + χ) := by
  rw [label_Y_eq hm hκ τ]
  have hd := key_velocity_defect hχ hκ hζ
  have e : domY χ m q κ τ (sliceY b m t₀ l) + q * τ * (b l 4 + (κ 1 : ℝ) * χ) -
      domY χ m q κ τ (sliceY b m t₀ l) = q * τ * (b l 4 + (κ 1 : ℝ) * χ) := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hτ.1]
  have : q * τ ≤ q := by nlinarith [hτ.2]
  calc q * τ * |b l 4 + (κ 1 : ℝ) * χ| ≤ q * |b l 4 + (κ 1 : ℝ) * χ| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ ≤ q * (ζ + χ) := mul_le_mul_of_nonneg_left hd hq

/-- **Block graph along a key label.** -/
theorem block_label_graph {b : α → Fin 6 → ℝ} {χ m q t₀ ζ a W Lb : ℝ} (hχ : 0 < χ) (hm : m ≠ 0)
    (hq : 0 ≤ q) (ha : 0 < a) {F : MvPolynomial (Fin 4) ℝ} {Lc : Fin 4 → ℝ}
    (hF : HorizontalForm F Lc) (hLb : ∀ e, |Lc e| ≤ Lb)
    {l : α} {κ : Fin 3 → ℤ} (hκ : slotKey b χ m t₀ l = κ) (hζ : |b l 4 + b l 0| ≤ ζ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hunit : t₀ + q * τ ∈ Icc (0 : ℝ) 1)
    (hfit : |MvPolynomial.eval ![t₀ + q * τ, b l 0 + (t₀ + q * τ) * b l 3,
      b l 1 + (t₀ + q * τ) * b l 4, b l 2 + (t₀ + q * τ) * b l 5] F| ≤ W) :
    |(b l 2 + (t₀ + q * τ) * b l 5) - a * quad2 (blockKeyCoeff F a χ m q t₀ κ) τ
      (sliceY b m t₀ l)| ≤ W + Lb * (2 * χ + q * (ζ + χ)) := by
  rw [quad2_blockKeyCoeff hF, mul_div_cancel₀ _ ha.ne', eval_horizontalForm hF] at *
  simp only [Matrix.cons_val] at hfit
  set t := t₀ + q * τ
  have hZ := label_Z_near (m := m) (t₀ := t₀) hχ hκ hunit
  have hY : |b l 1 + t * b l 4 - domY χ m q κ τ (sliceY b m t₀ l)| ≤ q * (ζ + χ) :=
    key_Y_near hχ hm hq hκ hζ hτ
  simp only [blockGraph_eq hF] at *
  have hL : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
  have e : b l 2 + t * b l 5 - (Lc 0 + Lc 1 * t + Lc 2 * domZ χ κ t +
      Lc 3 * domY χ m q κ τ (sliceY b m t₀ l)) =
      (b l 2 + t * b l 5 - (Lc 0 + Lc 1 * t + Lc 2 * (b l 0 + t * b l 3) +
        Lc 3 * (b l 1 + t * b l 4))) +
      (Lc 2 * (b l 0 + t * b l 3 - domZ χ κ t) +
        Lc 3 * (b l 1 + t * b l 4 - domY χ m q κ τ (sliceY b m t₀ l))) := by ring
  rw [e]
  have t2 : |Lc 2 * (b l 0 + t * b l 3 - domZ χ κ t)| ≤ Lb * (2 * χ) := by
    rw [abs_mul]; exact mul_le_mul (hLb 2) hZ (abs_nonneg _) hL
  have t3 : |Lc 3 * (b l 1 + t * b l 4 - domY χ m q κ τ (sliceY b m t₀ l))| ≤
      Lb * (q * (ζ + χ)) := by
    rw [abs_mul]; exact mul_le_mul (hLb 3) hY (abs_nonneg _) hL
  calc _ ≤ |b l 2 + t * b l 5 - (Lc 0 + Lc 1 * t + Lc 2 * (b l 0 + t * b l 3) +
        Lc 3 * (b l 1 + t * b l 4))| +
        |Lc 2 * (b l 0 + t * b l 3 - domZ χ κ t) +
          Lc 3 * (b l 1 + t * b l 4 - domY χ m q κ τ (sliceY b m t₀ l))| := abs_add_le _ _
    _ ≤ W + (Lb * (2 * χ) + Lb * (q * (ζ + χ))) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add t2 t3)
    _ = W + Lb * (2 * χ + q * (ζ + χ)) := by ring

/-- **Sheet graph along a key label.** -/
theorem sheet_label_graph {b : α → Fin 6 → ℝ} {χ m q t₀ ζ a W : ℝ} (hχ : 0 < χ) (hm : m ≠ 0)
    (hq : 0 ≤ q) (ha : 0 < a) {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    {y₀ v D H : ℝ} (hD : 0 < D) (hH : ∀ k', |sheetCoeff G y₀ v D k'| ≤ H)
    {l : α} {κ : Fin 3 → ℤ} (hκ : slotKey b χ m t₀ l = κ) (hζ : |b l 4 + b l 0| ≤ ζ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hunit : t₀ + q * τ ∈ Icc (0 : ℝ) 1)
    (hη : |etaFun y₀ v D (t₀ + q * τ) (b l 1 + (t₀ + q * τ) * b l 4)| ≤ 1)
    (hsmall : q * (ζ + χ) ≤ 4 * D)
    (hfit : |(b l 2 + (t₀ + q * τ) * b l 5) -
      MvPolynomial.eval ![t₀ + q * τ, b l 1 + (t₀ + q * τ) * b l 4] G| ≤ W) :
    |(b l 2 + (t₀ + q * τ) * b l 5) - a * quad2 (sheetKeyCoeff G a χ m q t₀ κ) τ
      (sliceY b m t₀ l)| ≤ W + 7 * H * (q * (ζ + χ)) / (4 * D) := by
  rw [quad2_sheetKeyCoeff hG, mul_div_cancel₀ _ ha.ne']
  set t := t₀ + q * τ
  have hY := key_Y_near hχ hm hq hκ hζ hτ
  set Y := b l 1 + t * b l 4
  set Y' := domY χ m q κ τ (sliceY b m t₀ l)
  have hval : MvPolynomial.eval ![t, Y] G - MvPolynomial.eval ![t, Y'] G =
      quad2 (sheetCoeff G y₀ v D) t (etaFun y₀ v D t Y) -
        quad2 (sheetCoeff G y₀ v D) t (etaFun y₀ v D t Y') := by
    rw [quad2_sheetCoeff_etaFun hG hD.ne', quad2_sheetCoeff_etaFun hG hD.ne']
  have hdη := etaFun_sub (y₀ := y₀) (v := v) hD t Y t Y'
  simp only [sub_self, abs_zero, mul_zero, add_zero] at hdη
  have hdη' : |etaFun y₀ v D t Y - etaFun y₀ v D t Y'| ≤ q * (ζ + χ) / (4 * D) :=
    hdη.trans (div_le_div_of_nonneg_right hY (by positivity))
  have hη' : |etaFun y₀ v D t Y'| ≤ 2 := by
    have : q * (ζ + χ) / (4 * D) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * D)]; linarith
    rw [abs_le] at hη hdη' ⊢
    constructor <;> linarith [hη.1, hη.2, hdη'.1, hdη'.2]
  have ht2 : |t| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith [hunit.1, hunit.2]
  have hlip := quad2_lipschitz (L := 2) hH (t := t) (t' := t)
    (η := etaFun y₀ v D t Y) (η' := etaFun y₀ v D t Y') ht2 ht2 (by linarith [hη]) hη'
  simp only [sub_self, abs_zero, zero_add] at hlip
  have e : (b l 2 + t * b l 5) - MvPolynomial.eval ![t, Y'] G =
      ((b l 2 + t * b l 5) - MvPolynomial.eval ![t, Y] G) +
        (MvPolynomial.eval ![t, Y] G - MvPolynomial.eval ![t, Y'] G) := by ring
  rw [e, hval]
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  calc _ ≤ |(b l 2 + t * b l 5) - MvPolynomial.eval ![t, Y] G| +
        |quad2 (sheetCoeff G y₀ v D) t (etaFun y₀ v D t Y) -
          quad2 (sheetCoeff G y₀ v D) t (etaFun y₀ v D t Y')| := abs_add_le _ _
    _ ≤ W + H * (1 + 3 * 2) * (q * (ζ + χ) / (4 * D)) :=
        add_le_add hfit (hlip.trans (by gcongr))
    _ = W + 7 * H * (q * (ζ + χ)) / (4 * D) := by ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
