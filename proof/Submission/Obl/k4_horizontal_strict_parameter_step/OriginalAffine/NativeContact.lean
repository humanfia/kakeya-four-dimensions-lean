/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeContact.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeGeometry
import Submission.Obl.k4_critical_derivative_evaluation_lists.GeoContactBoxes

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual midpoint of each dyadic child block is in unit time. -/
theorem original_timeCenter_mem_unit {k : ℕ} {s : ℝ} (i : Fin (cfg.n k s)) :
    cfg.originalTimeCenter k s i ∈ Icc (0 : ℝ) 1 := by
  have hI : cfg.originalTimeCenter k s i ∈ Data.I (cfg.T k s) (cfg.j k s i) := by
    simp only [originalTimeCenter, Data.I, Data.timeLength, mem_Icc, div_eq_mul_inv]
    have hq : (0 : ℝ) < ((2 : ℝ) ^ cfg.T k s)⁻¹ := by positivity
    constructor <;> nlinarith
  exact Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) hI

/-- The genuine atlas box is a horizontal true box at the square of the
original slack.  This retains its whole transverse q-squared domain. -/
theorem original_trueBox_subset_contactBox {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hℓ : cfg.ℓ = cfg.κ)
    (i : Fin (cfg.n k s)) :
    cfg.originalTrueBox k s i ⊆ horizontalTrueBox (cfg.c k s i)
      (cfg.originalTimeCenter k s i) (cfg.timeLength k s) (cfg.K k ^ 2) := by
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hgq : cfg.N k ^ (-cfg.ℓ * s) ≤ cfg.K k * cfg.timeLength k s := by
    rw [hℓ]
    exact (time_length_comparison hN hKp a.time_lower a.time_upper).2
  have hKK : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  intro z hz
  refine ⟨hz.1, hz.2.1.trans (mul_le_mul_of_nonneg_right hKK hq.le), ?_⟩
  apply hz.2.2.trans
  have hh := mul_le_mul_of_nonneg_left hgq (by positivity : 0 ≤ cfg.K k * cfg.timeLength k s)
  nlinarith [hh]

/-- One actual contact point locates the WHOLE original child box in a common
reference contact box.  The proof imports the accepted contact geometry; it
uses the original atlas and no critical-rate validity record. -/
theorem whole_original_child_common_box {k : ℕ} {s m D : ℝ}
    (a : cfg.AssignmentLevel k s) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (i : Fin (cfg.n k s))
    (hm : cfg.originalTimeCenter k s i = m) (p z₀ : Fin 3 → ℝ)
    (hv : |p 2| ≤ cfg.K k ^ 2) (hD : D ≤ cfg.timeLength k s ^ 2)
    (hz₀ : z₀ ∈ cfg.originalTrueBox k s i)
    (hcontactZ : |z₀ 1 - referenceZ p (z₀ 0)| ≤ cfg.K k ^ 2 * D)
    (hcontactY : |z₀ 2 - referenceY p (z₀ 0)| ≤ cfg.K k ^ 2 * D) :
    ∀ z ∈ cfg.originalTrueBox k s i,
      |z 0 - m| ≤ cfg.timeLength k s / 2 ∧
      |z 1 - referenceZ p m - p 2 * (z 0 - m)| ≤ 8 * cfg.K k ^ 2 * cfg.timeLength k s ∧
      |z 2 - referenceY p m - (-p 0 - m * p 2) * (z 0 - m) -
        m * (z 1 - referenceZ p m)| ≤ 32 * cfg.K k ^ 4 * cfg.timeLength k s ^ 2 := by
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold Data.timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hK2 : 1 ≤ cfg.K k ^ 2 := one_le_pow₀ hK
  have hKK : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have htime := cfg.original_timeCenter_mem_unit i
  rw [hm] at htime
  have hm1 : |m| ≤ 1 := by rw [abs_of_nonneg htime.1]; exact htime.2
  have hplane := a.plane_center i
  change |cfg.c k s i 3 + cfg.c k s i 0 +
      cfg.originalTimeCenter k s i * cfg.c k s i 1| +
    |cfg.c k s i 4 - cfg.originalTimeCenter k s i| ≤ cfg.K k * cfg.timeLength k s at hplane
  rw [hm] at hplane
  have hcenter : |cfg.c k s i 3 + cfg.c k s i 0 + m * cfg.c k s i 1| ≤
      cfg.K k ^ 2 * cfg.timeLength k s := by
    apply (le_add_of_nonneg_right (abs_nonneg _)).trans (hplane.trans ?_)
    exact mul_le_mul_of_nonneg_right hKK hq.le
  have htilt : |cfg.c k s i 4 - m| ≤ cfg.K k ^ 2 * cfg.timeLength k s := by
    apply (le_add_of_nonneg_left (abs_nonneg _)).trans (hplane.trans ?_)
    exact mul_le_mul_of_nonneg_right hKK hq.le
  have hsub : cfg.originalTrueBox k s i ⊆
      horizontalTrueBox (cfg.c k s i) m (cfg.timeLength k s) (cfg.K k ^ 2) := by
    rw [← hm]
    exact cfg.original_trueBox_subset_contactBox a hN hK hℓ i
  have hc := horizontalTrueBox_common_contact (cfg.c k s i) p z₀ m (cfg.timeLength k s)
    (cfg.K k ^ 2) D hq hq1 hK2 hD hm1 ((a.coefficient_bound i 1).trans hKK) hv
    hcenter htilt (hsub hz₀) hcontactZ hcontactY
  intro z hz
  obtain ⟨hZ, hY⟩ := hc z (hsub hz)
  refine ⟨by simpa only [hm] using hz.1, ?_, ?_⟩
  · convert hZ using 1
    congr 1
    simp only [referenceZ]
    ring
  · convert hY using 1
    · congr 1
      simp only [contactTransverse, referenceY, referenceZ]
      ring
    · ring

end NativeModel
end Submission.Obl.k4_horizontal_strict_parameter_step
