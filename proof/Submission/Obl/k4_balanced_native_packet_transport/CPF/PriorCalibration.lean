/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/PriorCalibration.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/PriorCalibration.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SaturationInterface

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped ENNReal

theorem Atlas.TrueAt.assigned_prior_floor {p : Data} {k M D : ℕ} {r : ℝ}
    {a : Atlas p k} (ha : a.TrueAt M D r) (b : Fin a.C) :
    ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / a.κ) ≤
      p.ν k (a.γ b) (a.A b) := by
  have hchart := ha.2.2.1 b
  have hfloor := hchart.2.2.2.2.2.2.2.2.2.2.2
  have hbound := hchart.incidence_mass_le_assigned (p.ν k (a.γ b))
  have hq0 : (2 : ENNReal) ^ a.T ≠ 0 := by positivity
  have hqtop : (2 : ENNReal) ^ a.T ≠ ⊤ := by finiteness
  have hqeq : (2 : ENNReal) ^ a.T = ENNReal.ofReal ((2 : ℝ) ^ a.T) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  calc
    _ = (2 : ENNReal) ^ a.T * ENNReal.ofReal
        (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / ((2 : ℝ) ^ a.T * a.κ)) := by
      rw [hqeq, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ (2 : ENNReal) ^ a.T * ((p.ν k (a.γ b)).prod volume) (a.F b) :=
      mul_le_mul' le_rfl hfloor
    _ ≤ (2 : ENNReal) ^ a.T *
        (((2 : ENNReal) ^ a.T)⁻¹ * p.ν k (a.γ b) (a.A b)) := mul_le_mul' le_rfl hbound
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel hq0 hqtop, one_mul]

/-- A saturated chart's FULL assigned prior is comparable to its physical
Jacobian times the original typical density, with exactly the allowed slack. -/
theorem Atlas.SaturatedAt.assigned_prior_calibration {p : Data} (hp : p.Valid)
    {k M D : ℕ} {r : ℝ} {a : Atlas p k} (ha : a.SaturatedAt M D r)
    (hκ : 1 ≤ a.κ) (b : Fin a.C) :
    0 < (p.ν k (a.γ b) (a.A b)).toReal ∧
      a.κ⁻¹ ≤ (p.ν k (a.γ b) (a.A b)).toReal /
        (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)|) ∧
      (p.ν k (a.γ b) (a.A b)).toReal /
        (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)|) ≤ a.κ := by
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hκ0 : 0 < a.κ := by linarith
  have hdet := (ha.1.2.2.1 b).1
  have hscale : 0 < p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| :=
    mul_pos (Real.rpow_pos_of_pos hN0 _) (abs_pos.mpr hdet)
  obtain ⟨_, _, _, _, _, _, _, _, ⟨Mb, Db, hb⟩, _⟩ := hp
  letI := ((hb k).2.2.2.1 (a.γ b)).1
  have hfinite : p.ν k (a.γ b) (a.A b) ≠ ⊤ := measure_ne_top _ _
  have hlo := ENNReal.toReal_mono hfinite (ha.1.assigned_prior_floor b)
  rw [ENNReal.toReal_ofReal (div_nonneg hscale.le hκ0.le)] at hlo
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ha.2.1 b)
  rw [ENNReal.toReal_ofReal (by positivity)] at hhi
  refine ⟨(div_pos hscale hκ0).trans_le hlo, ?_, ?_⟩
  · apply (le_div_iff₀ hscale).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hlo
  · apply (div_le_iff₀ hscale).mpr
    simpa only [mul_assoc] using hhi

end Submission.Obl.k4_balanced_native_packet_transport.CPF
