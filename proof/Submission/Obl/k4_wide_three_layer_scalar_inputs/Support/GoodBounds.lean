import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Good
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.DeepVariation

set_option linter.unusedVariables false

/-!
# Bounds on good incidences of a compared block
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

namespace ComparedBlock

variable (CB : ComparedBlock cfg k s u v χ H)

theorem frame_q : CB.frame.q = ((2 : ℝ) ^ cfg.T k s)⁻¹ := rfl
theorem frame_t₀ : CB.frame.t₀ = ((cfg.j k s CB.i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s := rfl
theorem frame_c : CB.frame.c = cfg.c k s CB.i := rfl
theorem frame_g : CB.frame.g = cfg.N k ^ (-cfg.κ * s) := rfl
theorem frame_a : CB.frame.a = cfg.N k ^ (-s) := rfl
theorem frame_L : CB.frame.L = CB.L := rfl

theorem I_bounds {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ Data.I T j) :
    (j : ℝ) / (2 : ℝ) ^ T ≤ t ∧ t ≤ (j : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ := by
  simp only [Data.I, mem_Icc] at ht
  refine ⟨ht.1, ?_⟩
  have e : (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T = (j : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹ := by
    field_simp
  rw [← e]; exact ht.2

theorem I_subset_unit {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ Data.I T j) :
    0 ≤ t ∧ t ≤ 1 := by
  simp only [Data.I, mem_Icc] at ht
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ T := by
    have : (j : ℕ) + 1 ≤ 2 ^ T := j.isLt
    exact_mod_cast this
  constructor
  · exact le_trans (div_nonneg (Nat.cast_nonneg _) hT.le) ht.1
  · exact ht.2.trans ((div_le_one hT).mpr hj)

/-- Bounds for the normalized coordinates and the velocity of a good incidence. -/
theorem good_bounds (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) {p : α × ℝ} (hp : CB.Good p) :
    (0 ≤ CB.frame.zt p.2 ∧ CB.frame.zt p.2 ≤ 1) ∧
    |CB.frame.zZ (cfg.b k p.1) p.2| ≤ cfg.K k ∧
    |CB.frame.tr (cfg.b k p.1) p.2| ≤ cfg.K k ∧
    |CB.frame.resid (cfg.b k p.1) p.2| ≤ cfg.K k ∧
    |cfg.b k p.1 3 - cfg.c k s CB.i 1| ≤ 2 * cfg.K k := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
  have hg : 0 < cfg.N k ^ (-cfg.κ * s) := Real.rpow_pos_of_pos hN _
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  obtain ⟨l, t⟩ := p
  have hl := hp.B
  have ht := hp.I
  simp only at hl ht
  have hA : l ∈ cfg.A k s CB.i := (hB.sets CB.i).2.2 hl
  obtain ⟨hx, hy, -⟩ := hB.geom CB.i l hA t ht
  simp only [x_one, x_two] at hx hy
  have hfit := (hB.fit CB.i l hl t ht).1
  rw [eval_horizontalForm hL] at hfit
  simp only [Data.x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hfit
  obtain ⟨ht1, ht2⟩ := I_bounds ht
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [frame, Frame.zt, blockFrame]
    exact div_nonneg (by linarith) hq.le
  · simp only [frame, Frame.zt, blockFrame]
    rw [div_le_one hq]; linarith
  · simp only [frame, Frame.zZ, blockFrame]
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]; exact hx
  · simp only [frame, Frame.tr, blockFrame]
    rw [abs_div, abs_of_pos (mul_pos hq hg), div_le_iff₀ (mul_pos hq hg)]
    calc _ ≤ cfg.K k * ((2 : ℝ) ^ cfg.T k s)⁻¹ * cfg.N k ^ (-cfg.κ * s) := hy
      _ = _ := by ring
  · simp only [frame, Frame.resid, blockFrame]
    rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]; exact hfit
  · -- two times of the block interval
    have hjT : ((cfg.j k s CB.i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s ∈
        Data.I (cfg.T k s) (cfg.j k s CB.i) := by
      simp only [Data.I, mem_Icc]
      exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
    have hjT' : ((cfg.j k s CB.i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s + ((2 : ℝ) ^ cfg.T k s)⁻¹ ∈
        Data.I (cfg.T k s) (cfg.j k s CB.i) := by
      simp only [Data.I, mem_Icc]
      constructor
      · linarith
      · apply le_of_eq; field_simp
    obtain ⟨hx1, -, -⟩ := hB.geom CB.i l hA _ hjT
    obtain ⟨hx2, -, -⟩ := hB.geom CB.i l hA _ hjT'
    simp only [x_one] at hx1 hx2
    set t₀ := ((cfg.j k s CB.i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s
    set q := ((2 : ℝ) ^ cfg.T k s)⁻¹
    have hid : q * (cfg.b k l 3 - cfg.c k s CB.i 1) =
        (cfg.b k l 0 + (t₀ + q) * cfg.b k l 3 - cfg.c k s CB.i 0 - (t₀ + q) * cfg.c k s CB.i 1) -
        (cfg.b k l 0 + t₀ * cfg.b k l 3 - cfg.c k s CB.i 0 - t₀ * cfg.c k s CB.i 1) := by ring
    have h2 : q * |cfg.b k l 3 - cfg.c k s CB.i 1| ≤ q * (2 * cfg.K k) := by
      rw [← abs_of_pos hq, ← abs_mul, hid, abs_of_pos hq]
      calc _ ≤ |cfg.b k l 0 + (t₀ + q) * cfg.b k l 3 - cfg.c k s CB.i 0 - (t₀ + q) * cfg.c k s CB.i 1| +
            |cfg.b k l 0 + t₀ * cfg.b k l 3 - cfg.c k s CB.i 0 - t₀ * cfg.c k s CB.i 1| := abs_sub _ _
        _ ≤ cfg.K k * q + cfg.K k * q := add_le_add hx2 hx1
        _ = q * (2 * cfg.K k) := by ring
    exact le_of_mul_le_mul_left h2 hq

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
