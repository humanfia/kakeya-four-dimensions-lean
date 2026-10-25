/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/PureRecords.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.RecordSupport

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev pureRecordSupport {J : ℕ} (σ K R : ℝ) (c : Record J) : Set ObsSpace :=
  {p | |(c.2.2.2 : ℝ)| ≤ K + 1} ∩
    (recordBase σ R c ×ˢ integerWindow 1 (c.2.2.1 : ℝ) (R + 2))

theorem measurable_pureRecordSupport {J : ℕ} (σ K R : ℝ) (c : Record J) :
    MeasurableSet (pureRecordSupport σ K R c) := by
  have hconst : MeasurableSet {p : ObsSpace | |(c.2.2.2 : ℝ)| ≤ K + 1} := by
    by_cases h : |(c.2.2.2 : ℝ)| ≤ K + 1 <;> simp [h]
  exact hconst.inter ((measurable_baseRectangle measurableSet_Ico measurableSet_Icc).prod
    (measurableSet_le (by fun_prop) measurable_const))

theorem pureRecordSupport_volume {J : ℕ} (hJ : 0 < J) {σ K R : ℝ}
    (hσ : 0 < σ) (hR : 0 ≤ R) (c : Record J) :
    reference (pureRecordSupport σ K R c) ≤
      ENNReal.ofReal (2 * (R + 1) * (8 * R + 18) * σ / (J : ℝ)) := by
  have hh := integerWindow_count_le (c := (c.2.2.1 : ℝ)) (a := 1)
    (by norm_num) (show 0 ≤ R + 2 by linarith)
  have hh' : Measure.count (integerWindow 1 (c.2.2.1 : ℝ) (R + 2)) ≤
      ENNReal.ofReal (8 * R + 18) := by convert hh using 1 <;> ring
  calc
    _ ≤ reference (recordBase σ R c ×ˢ integerWindow 1 (c.2.2.1 : ℝ) (R + 2)) :=
      measure_mono inter_subset_right
    _ = (ENNReal.ofReal ((J : ℝ)⁻¹) * ENNReal.ofReal (2 * (R + 1) * σ)) *
        Measure.count (integerWindow 1 (c.2.2.1 : ℝ) (R + 2)) := by
      rw [reference, Measure.prod_prod, volume_baseRectangle measurableSet_Ico measurableSet_Icc,
        cell_volume hJ, Real.volume_Icc]
      congr 2
      congr 1
      ring
    _ ≤ (ENNReal.ofReal ((J : ℝ)⁻¹) * ENNReal.ofReal (2 * (R + 1) * σ)) *
        ENNReal.ofReal (8 * R + 18) := mul_le_mul' le_rfl hh'
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg J)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (J : ℝ)⁻¹ * (2 * (R + 1) * σ))]
      congr 1
      ring

theorem pureRecordSupport_overlap {J : ℕ} (hJ : 0 < J) {σ K R : ℝ}
    (hσ : 0 < σ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (W : Finset (Record J)) (p : ObsSpace)
    (hW : ∀ c ∈ W, p ∈ pureRecordSupport σ K R c) :
    (W.card : ℝ) ≤ (8 * R + 10) * (8 * R + 18) * (8 * K + 10) := by
  classical
  obtain ⟨hAf, hAc⟩ := integerWindow_finite_card (c := p.1 1) hσ
    (show 0 ≤ (R + 1) * σ by positivity)
  obtain ⟨hBf, hBc⟩ := integerWindow_finite_card (c := (p.2 : ℝ))
    (a := 1) (by norm_num) (show 0 ≤ R + 2 by linarith)
  obtain ⟨hCf, hCc⟩ := integerWindow_finite_card (c := 0)
    (a := 1) (by norm_num) (show 0 ≤ K + 1 by linarith)
  have hcard := record_card_le_product hJ (p.1 0) W hAf hBf hCf
    (fun c hc => (hW c hc).2.1.1) (by
      intro c hc
      have hp := hW c hc
      refine ⟨?_, ?_, ?_⟩
      · change |σ * (c.2.1 : ℝ) - p.1 1| ≤ (R + 1) * σ
        rw [abs_sub_comm]
        exact abs_le.mpr ⟨by linarith [hp.2.1.2.1], by linarith [hp.2.1.2.2]⟩
      · change |1 * (c.2.2.1 : ℝ) - (p.2 : ℝ)| ≤ R + 2
        simpa only [integerWindow, mem_ofPred_eq, one_mul, abs_sub_comm] using hp.2.2
      · simpa only [integerWindow, mem_ofPred_eq, one_mul, sub_zero] using hp.1)
  have ha : (hAf.toFinset.card : ℝ) ≤ 8 * R + 10 := by
    rw [← Set.ncard_eq_toFinset_card _ hAf]
    refine hAc.trans_eq ?_
    field_simp [hσ.ne']
    ring
  have hb : (hBf.toFinset.card : ℝ) ≤ 8 * R + 18 := by
    rw [← Set.ncard_eq_toFinset_card _ hBf]
    convert hBc using 1 <;> ring
  have hc : (hCf.toFinset.card : ℝ) ≤ 8 * K + 10 := by
    rw [← Set.ncard_eq_toFinset_card _ hCf]
    convert hCc using 1 <;> ring
  calc
    _ ≤ (hAf.toFinset.card : ℝ) * ((hBf.toFinset.card : ℝ) * (hCf.toFinset.card : ℝ)) := by
      exact_mod_cast hcard
    _ ≤ (8 * R + 10) * ((8 * R + 18) * (8 * K + 10)) := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
