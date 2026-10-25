/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeContactBox.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCoordinates
import Submission.Obl.k4_subcritical_corrected_scalar_charts.CommonHorizontalBox
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ScalarCellContact

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

theorem native_time_midpoint_gap (T : ℕ) (j : Fin (2 ^ T)) {t : ℝ} (ht : t ∈ I T j) :
    |t - (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹| ≤ ((2 : ℝ) ^ T)⁻¹ := by
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  simp only [I, mem_Icc, div_eq_mul_inv] at ht
  rw [abs_le]
  constructor <;> linarith

theorem native_midpoint_mem_unit (T : ℕ) (j : Fin (2 ^ T)) :
    (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹ ∈ Icc (0 : ℝ) 1 := by
  apply Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit T j
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  change ((j : ℕ) : ℝ) / (2 : ℝ) ^ T ≤ _ ∧ _ ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T
  constructor
  · simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (show ((j : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) + 1 / 2 by linarith) hq.le
  · simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (show ((j : ℕ) : ℝ) + 1 / 2 ≤ ((j : ℕ) : ℝ) + 1 by linarith) hq.le

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem NativeLevel.horizontal_box_mem (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s)) {l : α}
    (hl : l ∈ cfg.A k s i) {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    originalBase (cfg.b k l) t ∈ horizontalNativeBox (cfg.K k ^ 2) (cfg.timeLength k s)
      (cfg.nativeMidpoint k s i) (cfg.c k s i 0) (cfg.c k s i 1)
      (cfg.c k s i 2) (cfg.c k s i 3) (cfg.c k s i 4) := by
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hf := h.native_frame_bound a.assignments i l hl ht
  have hz := hf 1
  have hy := hf 2
  rw [atlasFrame_formula] at hz hy
  change |(cfg.b k l 0 + t * cfg.b k l 3 - cfg.c k s i 0 - t * cfg.c k s i 1) /
    cfg.timeLength k s| ≤ cfg.K k ^ 2 at hz
  change |(cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 - t * cfg.c k s i 3 -
    cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)) / cfg.timeLength k s ^ 2| ≤ cfg.K k ^ 2 at hy
  rw [abs_div, abs_of_pos hq] at hz
  rw [abs_div, abs_of_pos (sq_pos_of_pos hq)] at hy
  refine ⟨native_time_midpoint_gap _ _ ht, ?_, ?_⟩
  · change |cfg.b k l 0 + t * cfg.b k l 3 - (cfg.c k s i 0 + t * cfg.c k s i 1)| ≤ _
    convert (div_le_iff₀ hq).mp hz using 1 <;> congr 1 <;> ring
  · change |cfg.b k l 1 + t * cfg.b k l 4 - (cfg.c k s i 2 + t * cfg.c k s i 3 +
      cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3))| ≤ _
    convert (div_le_iff₀ (sq_pos_of_pos hq)).mp hy using 1 <;> congr 1 <;> ring

/-- A single scalar-cell contact forces the WHOLE original fitted native entry
into the common reference native box. Its original witness can then be counted. -/
theorem NativeLevel.reference_box_of_scalar_contact (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s)) {D σ χ pc qc v R : ℝ}
    (hD : 0 < D) (hσ : σ ≤ cfg.timeLength k s) (hDh : 3 * D ≤ cfg.timeLength k s)
    (hχD : χ ≤ D) (hnoise : χ + χ ≤ D * cfg.timeLength k s)
    (hv : |v| ≤ 3 * cfg.K k)
    {lc : α} {tc : ℝ} (hlc : lc ∈ cfg.B k s i) (htc : tc ∈ I (cfg.T k s) (cfg.j k s i))
    (hpc : |cfg.b k lc 0 - pc| ≤ D) (hvc : |cfg.b k lc 3 - v| ≤ χ)
    (hcontact : |cfg.b k lc 4 + cfg.b k lc 0| ≤ χ)
    (hR : |(cfg.b k lc 1 - qc) / D - 2 * tc * ((cfg.b k lc 0 - pc) / D) - R| ≤ σ) :
    ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i), ∀ e,
      |nativeFrame (cfg.timeLength k s) (cfg.nativeMidpoint k s i) pc (qc + D * R)
        v pc (cfg.nativeMidpoint k s i) (originalBase (cfg.b k l) t) e| ≤ 320 * cfg.K k ^ 4 := by
  let q := cfg.timeLength k s
  let τ := cfg.nativeMidpoint k s i
  have hq : 0 < q := by dsimp [q, timeLength]; positivity
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK2 : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ hK
  have hK4 : 1 ≤ cfg.K k ^ 4 := one_le_pow₀ hK
  have hKK2 : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hK24 : cfg.K k ^ 2 ≤ cfg.K k ^ 4 := by nlinarith [sq_nonneg (cfg.K k ^ 2 - 1)]
  have hτ : τ ∈ Icc (0 : ℝ) 1 := native_midpoint_mem_unit _ _
  have htc' : tc ∈ Icc (0 : ℝ) 1 := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit _ _ htc
  have htcτ : |tc - τ| ≤ q := native_time_midpoint_gap _ _ htc
  have hc := scalar_parameter_native_contact (cfg.b k lc) hD hq hσ hDh hχD hnoise
    htc' hτ htcτ hpc hvc hcontact hR
  have hplane : |cfg.c k s i 4 - τ| ≤ cfg.K k * q := by
    have hh := a.assignments.plane_center i
    dsimp [τ, nativeMidpoint]
    dsimp [q]
    linarith [abs_nonneg (cfg.c k s i 3 + cfg.c k s i 0 +
      (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s * cfg.c k s i 1)]
  have hhor : |cfg.c k s i 3 + cfg.c k s i 0 + τ * cfg.c k s i 1| ≤ cfg.K k * q := by
    have hh := a.assignments.plane_center i
    dsimp [τ, nativeMidpoint, q]
    linarith [abs_nonneg (cfg.c k s i 4 -
      (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s)]
  have hbox (l : α) (hl : l ∈ cfg.B k s i) (t : ℝ) (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
      originalBase (cfg.b k l) t ∈ horizontalNativeBox (4 * cfg.K k ^ 2) q τ
        (cfg.c k s i 0) (cfg.c k s i 1) (cfg.c k s i 2) (cfg.c k s i 3) (cfg.c k s i 4) := by
    have hh := a.horizontal_box_mem h i (a.assignments.fitted_subset i hl) ht
    exact ⟨hh.1, hh.2.1.trans (by dsimp [q]; nlinarith), hh.2.2.trans (by dsimp [q]; nlinarith)⟩
  intro l hl t ht e
  have hn := horizontal_box_common_from_contact (K := 4 * cfg.K k ^ 2)
    (by linarith) hq (by exact (a.assignments.coefficient_bound i 1).trans (by linarith))
    (hv.trans (by nlinarith)) (hplane.trans (by nlinarith)) (hhor.trans (by nlinarith))
    (hbox lc hlc tc htc) (hbox l hl t ht) hc.1 hc.2
  dsimp [originalBase] at hn
  fin_cases e
  · change |(t - τ) / q| ≤ 320 * cfg.K k ^ 4
    rw [abs_div, abs_of_pos hq]
    exact ((div_le_one hq).mpr (native_time_midpoint_gap _ _ ht)).trans (by linarith)
  · change |(cfg.b k l 0 + t * cfg.b k l 3 - (pc + t * v)) / q| ≤ 320 * cfg.K k ^ 4
    rw [abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    exact hn.1.trans (by nlinarith)
  · change |(cfg.b k l 1 + t * cfg.b k l 4 - ((qc + D * R) - t * pc) -
      τ * (cfg.b k l 0 + t * cfg.b k l 3 - (pc + t * v))) / q ^ 2| ≤ 320 * cfg.K k ^ 4
    rw [abs_div, abs_of_pos (sq_pos_of_pos hq)]
    apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    convert hn.2 using 1 <;> ring

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
