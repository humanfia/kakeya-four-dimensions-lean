/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeCoordinates.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFrame

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open Submission.Obl.k4_critical_intercept_concentration
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

/-- The original physical base of a trajectory incidence. -/
def originalBase (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

/-- The native coordinate frame associated to the actual frozen box coefficients. -/
def atlasFrame (h m : ℝ) (c : Fin 5 → ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  nativeFrame h m (c 0) (c 2 + c 4 * c 0) (c 1) (-c 3 - c 4 * c 1) (c 4) z

theorem atlasFrame_formula (h m : ℝ) (c : Fin 5 → ℝ) (z : Fin 3 → ℝ) :
    atlasFrame h m c z = ![(z 0 - m) / h,
      (z 1 - c 0 - z 0 * c 1) / h,
      (z 2 - c 2 - z 0 * c 3 - c 4 * z 1) / h ^ 2] := by
  ext i
  fin_cases i <;> simp [atlasFrame, nativeFrame] <;> ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def nativeMidpoint (cfg : Data α) (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  (((cfg.j k s i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s

/-- The true affine calibration sees an inverse-subpower box in normalized
native coordinates, with its original transverse h² scale. -/
theorem Prepared.native_frame_bound (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α)
    (hl : l ∈ cfg.A k s i) {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    ∀ e, |atlasFrame (cfg.timeLength k s) (cfg.nativeMidpoint k s i)
      (cfg.c k s i) (originalBase (cfg.b k l) t) e| ≤ cfg.K k ^ 2 := by
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hK2 : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hK21 : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ hK
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have ht' : ((cfg.j k s i : ℕ) : ℝ) * cfg.timeLength k s ≤ t ∧
      t ≤ (((cfg.j k s i : ℕ) : ℝ) + 1) * cfg.timeLength k s := by
    simpa only [I, timeLength, mem_Icc, div_eq_mul_inv] using ht
  have htime : |t - cfg.nativeMidpoint k s i| ≤ cfg.timeLength k s := by
    rw [abs_le]
    dsimp only [nativeMidpoint]
    constructor <;> linarith
  have hg : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.timeLength k s := by
    rw [h.horizontal_rate]
    exact (time_length_comparison (by linarith [h.scale k]) hKp a.time_lower a.time_upper).2
  have hz := (a.geometry i l hl t ht).1
  have hy := (a.geometry i l hl t ht).2.1
  have hy' : |cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 -
      t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)| ≤
      cfg.K k ^ 2 * cfg.timeLength k s ^ 2 := by
    apply (show |cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 -
        t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)| ≤
        cfg.K k * cfg.timeLength k s * cfg.N k ^ (-cfg.ℓ * s) from hy).trans
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ cfg.K k * cfg.timeLength k s by positivity)
    convert hh using 1 <;> ring
  intro e
  rw [atlasFrame_formula]
  fin_cases e
  · change |(t - cfg.nativeMidpoint k s i) / cfg.timeLength k s| ≤ cfg.K k ^ 2
    rw [abs_div, abs_of_pos hq]
    exact ((div_le_one hq).mpr htime).trans hK21
  · change |(cfg.b k l 0 + t * cfg.b k l 3 - cfg.c k s i 0 - t * cfg.c k s i 1) /
      cfg.timeLength k s| ≤ cfg.K k ^ 2
    rw [abs_div, abs_of_pos hq]
    exact ((div_le_iff₀ hq).mpr (by simpa [x] using hz)).trans hK2
  · change |(cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 - t * cfg.c k s i 3 -
      cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)) / cfg.timeLength k s ^ 2| ≤ cfg.K k ^ 2
    rw [abs_div, abs_of_pos (sq_pos_of_pos hq)]
    exact (div_le_iff₀ (sq_pos_of_pos hq)).mpr hy'

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
