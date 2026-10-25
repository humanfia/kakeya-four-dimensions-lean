/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ObservedProcessDomination
import Submission.Lib.K4ChartLifting.Mass

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Normalizing a physical endpoint time cancels its block-length
factor in the original conditional density ceiling. -/
theorem normalize_control_time_ceiling {V : Type*} [MeasurableSpace V]
    (π : Measure V) [SigmaFinite π] (P : Measure (V × ℝ))
    (K D : ENNReal) (a h : ℝ) (hh : 0 < h)
    (hP : P ≤ (K * ((ENNReal.ofReal h)⁻¹ * D)) • π.prod (volume : Measure ℝ)) :
    P.map (Prod.map id (fun t : ℝ => (t-a)/h)) ≤
      (K * D) • π.prod (volume : Measure ℝ) := by
  have hf : Measurable (Prod.map (id : V → V) (fun t : ℝ => (t-a)/h)) := by fun_prop
  have hreference : (π.prod (volume : Measure ℝ)).map
      (Prod.map id (fun t : ℝ => (t-a)/h)) =
      ENNReal.ofReal h • π.prod (volume : Measure ℝ) := by
    rw [← Measure.map_prod_map π volume measurable_id (by fun_prop), Measure.map_id,
      Submission.Lib.K4ChartLifting.map_volume_affine a h hh, Measure.prod_smul_right]
  have hdom := Measure.map_mono hP hf
  rw [Measure.map_smul _ hf.aemeasurable, hreference, smul_smul] at hdom
  have hc : (K * ((ENNReal.ofReal h)⁻¹ * D)) * ENNReal.ofReal h = K * D := by
    calc
      _ = (K * D) * ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal h) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne'
        ENNReal.ofReal_ne_top, mul_one]
  simpa only [hc] using hdom

theorem normalized_time_mem_unit_interval {a h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Icc a (a+h)) : (t-a)/h ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr ht.1) hh.le
  · apply (div_le_one hh).mpr
    linarith [ht.2]

/-- Differences of normalized times are the signed physical durations
scaled by the actual positive block length. -/
theorem consecutiveTimeIncrements_normalized {n : ℕ}
    (a h start : ℝ) (t : Fin n → ℝ) (i : Fin n) :
    consecutiveTimeIncrements ((start-a)/h) (fun j => (t j-a)/h) i =
      consecutiveTimeIncrements start t i / h := by
  have hc (j : Fin (n+1)) :
      (Fin.cons ((start-a)/h) (fun i => (t i-a)/h) : Fin (n+1) → ℝ) j =
        ((Fin.cons start t : Fin (n+1) → ℝ) j-a)/h := by
    refine Fin.cases ?_ (fun k => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ]
  unfold consecutiveTimeIncrements
  rw [hc, hc]
  ring

theorem normalized_signed_durations_mem_unit_box {n : ℕ}
    (a h start : ℝ) (hh : 0 < h) (t : Fin n → ℝ)
    (hstart : start ∈ Icc a (a+h)) (ht : ∀ i, t i ∈ Icc a (a+h)) :
    consecutiveTimeIncrements ((start-a)/h) (fun i => (t i-a)/h) ∈
      Icc (-1 : Fin n → ℝ) 1 :=
  consecutiveTimeIncrements_mem_unit_box (normalized_time_mem_unit_interval hh hstart)
    (fun i => normalized_time_mem_unit_interval hh (ht i))

end Submission.Lib.K4PolynomialNorming
