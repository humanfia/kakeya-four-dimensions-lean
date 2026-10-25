/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockTime.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockTime.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUnitTime
import Submission.Obl.k4_horizon_chart_assembly.TimeTransport

/-! Exact original-law time normalization about an active block anchor. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

noncomputable def scalarIntervalTime (a : ℝ) : Measure ℝ :=
  volume.restrict (Icc a (a + 1))

theorem scalarIntervalTime_probability (a : ℝ) : IsProbabilityMeasure (scalarIntervalTime a) :=
  ⟨by simp only [scalarIntervalTime, Measure.restrict_apply_univ, Real.volume_Icc,
    add_sub_cancel_left, ENNReal.ofReal_one]⟩

theorem scalarIntervalTime_le_volume (a : ℝ) : scalarIntervalTime a ≤ volume :=
  Measure.restrict_le_self

theorem original_interval_time_swap_mass {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (a : ℝ) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc a (a + 1)) :
    ((scalarIntervalTime a).prod ν) (Prod.swap ⁻¹' E) = (ν.prod volume) E := by
  have hprod : (scalarIntervalTime a).prod ν =
      (volume.prod ν).restrict (Icc a (a + 1) ×ˢ univ) := by
    simpa only [scalarIntervalTime, Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := ν) (Icc a (a + 1)) univ)
  have hswap := congrArg (fun m : Measure (Λ × ℝ) => m E)
    (Measure.prod_swap (μ := (volume : Measure ℝ)) (ν := ν))
  rw [Measure.map_apply measurable_swap hE] at hswap
  rw [hprod, Measure.restrict_apply (hE.preimage measurable_swap),
    inter_eq_left.mpr (show Prod.swap ⁻¹' E ⊆ Icc a (a + 1) ×ˢ univ from
      fun q hq => ⟨(hunit hq).2, mem_univ _⟩)]
  exact hswap

theorem original_centered_block_mass {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (s anchor : ℝ) {H : ℝ} (hH : 0 < H)
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    ((scalarIntervalTime (-anchor)).prod ν)
      {q : ℝ × Λ | (q.2, s + H * anchor + H * q.1) ∈ E} =
        ENNReal.ofReal H⁻¹ * (ν.prod volume) E := by
  let F := Submission.Obl.k4_horizon_chart_assembly.timeLift (α := Λ) (s + H * anchor) H
  have hF : Measurable F :=
    Submission.Obl.k4_horizon_chart_assembly.measurable_timeLift _ _
  have hpre : F ⁻¹' E ⊆ univ ×ˢ Icc (-anchor) (-anchor + 1) := by
    intro q hq
    have h := (hblock hq).2
    change s ≤ s + H * anchor + H * q.2 ∧ s + H * anchor + H * q.2 ≤ s + H at h
    exact ⟨mem_univ _, by nlinarith [h.1], by nlinarith [h.2]⟩
  calc
    _ = (ν.prod volume) (F ⁻¹' E) := original_interval_time_swap_mass ν (-anchor) (hE.preimage hF) hpre
    _ = ((ν.prod volume).map F) E := (Measure.map_apply hF hE).symm
    _ = _ := by
      rw [Submission.Obl.k4_horizon_chart_assembly.map_timeLift_prod ν _ hH, Measure.smul_apply]
      rfl

theorem original_centered_block_real {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (s anchor : ℝ) {H : ℝ} (hH : 0 < H)
    {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hblock : E ⊆ univ ×ˢ Icc s (s + H)) :
    ((scalarIntervalTime (-anchor)).prod ν).real
      {q : ℝ × Λ | (q.2, s + H * anchor + H * q.1) ∈ E} =
        (ν.prod volume).real E / H := by
  have h := congrArg ENNReal.toReal (original_centered_block_mass ν s anchor hH hE hblock)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr hH).le,
    div_eq_mul_inv, mul_comm] using h

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
