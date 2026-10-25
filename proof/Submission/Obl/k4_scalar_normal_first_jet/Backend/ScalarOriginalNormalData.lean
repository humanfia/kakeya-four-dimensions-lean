/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarOriginalNormalData.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarOriginalNormalData.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalInterface
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarVectorInterface
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarUnitTime

/-! Original measurable scalar data with active row bounds and half-open spatial caps. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

structure ScalarOriginalNormalData {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (ν : Measure Λ) (E : Set (Λ × ℝ))
    (F : ℝ → ℝ) (S : ℝ → Set ℝ) (K ζ d : ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  one_le : 1 ≤ K
  floor_pos : 0 < ζ
  event_measurable : MeasurableSet E
  unit_time : E ⊆ univ ×ˢ Icc (0 : ℝ) 1
  coefficients : ∀ p ∈ E, D.Bounded K p.1
  row_measurable : Measurable F
  row_bounded : ∀ p ∈ E, |F p.2| ≤ K
  dense : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  row_comparison : ∀ p ∈ E, ∀ q ∈ E, |F p.2 - F q.2| ≤ K * (|p.2 - q.2| + ζ)
  residual_comparison : ∀ p ∈ E, ∀ q ∈ E,
    |D.residual F p.1 p.2 - D.residual F q.1 q.2| ≤
      K * (‖(![p.2, D.x p.1 p.2, D.y p.1 p.2] : Fin 3 → ℝ) -
        ![q.2, D.x q.1 q.2, D.y q.1 q.2]‖ + ζ)
  support_AD : ∀ t, IntervalAD ζ d K (S t)
  support_mem : ∀ p ∈ E, D.scalar F p.1 p.2 ∈ S p.2
  spatial_cap : ∀ t a b q : ℝ, ζ ≤ q → q ≤ 1 →
    ν {l | (l, t) ∈ E ∧ D.x l t ∈ Ico a (a + q) ∧ D.y l t ∈ Ico b (b + q)} ≤
      ENNReal.ofReal (K * q ^ (1 + d))

namespace ScalarOriginalNormalData

theorem clipped_hyp {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d : ℝ}
    (h : ScalarOriginalNormalData D ν E F S K ζ d) (hd : 0 ≤ d) :
    ScalarNormalHyp D ν E (scalarClippedRow K F) S (4 * K) ζ d := by
  let : IsProbabilityMeasure ν := h.probability
  exact ScalarNormalHyp.of_half_open_active_row D ν E F S h.one_le h.floor_pos hd
    h.event_measurable h.unit_time h.coefficients h.row_measurable h.row_bounded h.row_comparison
    (D.residual_comparison_of_norm (zero_le_one.trans h.one_le) h.residual_comparison)
    h.support_AD h.support_mem h.spatial_cap

theorem dense_real {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)}
    {F : ℝ → ℝ} {S : ℝ → Set ℝ} {K ζ d : ℝ}
    (h : ScalarOriginalNormalData D ν E F S K ζ d) : K⁻¹ ≤ (ν.prod volume).real E := by
  let : IsProbabilityMeasure ν := h.probability
  have hfinite := original_unit_incidence_ne_top ν h.event_measurable h.unit_time
  have hreal := ENNReal.toReal_mono hfinite h.dense
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (zero_le_one.trans h.one_le))] using hreal

end ScalarOriginalNormalData

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
