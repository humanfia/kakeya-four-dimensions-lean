/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNormalRestriction.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNormalRestriction.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalData

/-! Original scalar-normal upper inputs persist under label deletion. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

namespace ScalarNormalHyp

theorem restrict_event {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsFiniteMeasure ν] {E R : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hR : MeasurableSet R) (hRE : R ⊆ E) :
    ScalarNormalHyp D ν R F S K ζ d := by
  refine ⟨hR, hRE.trans h.unit_time, fun p hp => h.coefficients p (hRE hp),
    h.row_measurable, h.row_bounded, ?_, ?_, h.support_AD, fun p hp => h.support_mem p (hRE hp), ?_⟩
  · exact fun p hp q hq => h.row_comparison p (hRE hp) q (hRE hq)
  · exact fun p hp q hq => h.residual_comparison p (hRE hp) q (hRE hq)
  · intro t a b r hr
    have hsub : {l | (l, t) ∈ R ∧ D.x l t ∈ Icc a (a + r) ∧ D.y l t ∈ Icc b (b + r)} ⊆
        {l | (l, t) ∈ E ∧ D.x l t ∈ Icc a (a + r) ∧ D.y l t ∈ Icc b (b + r)} :=
      fun l hl => ⟨hRE hl.1, hl.2⟩
    exact (measureReal_mono hsub (measure_ne_top ν _)).trans
      (h.spatial_cap t a b r hr)

theorem increase_constant {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K K' ζ d : ℝ}
    (h : ScalarNormalHyp D ν E F S K ζ d) (hζ : 0 < ζ) (hKK : K ≤ K') :
    ScalarNormalHyp D ν E F S K' ζ d := by
  refine ⟨h.event_measurable, h.unit_time, ?_, h.row_measurable,
    fun t => (h.row_bounded t).trans hKK, ?_, ?_, ?_, h.support_mem, ?_⟩
  · intro p hp
    have hb := h.coefficients p hp
    exact ⟨hb.1.trans hKK, hb.2.1.trans hKK, hb.2.2.1.trans hKK,
      hb.2.2.2.1.trans hKK, hb.2.2.2.2.trans hKK⟩
  · intro p hp q hq
    exact (h.row_comparison p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (add_nonneg (abs_nonneg _) hζ.le))
  · intro p hp q hq
    exact (h.residual_comparison p hp q hq).trans
      (mul_le_mul_of_nonneg_right hKK (by positivity))
  · intro t
    exact CellProofs.Assouad.mono_constant hζ (h.support_AD t) hKK
  · intro t a b r hr
    exact (h.spatial_cap t a b r hr).trans
      (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (hζ.le.trans hr) _))

end ScalarNormalHyp

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
