/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/NativeMeshCaps.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open Submission.Lib.K4ContactNormalization

/-- A primitive ceiling in one original base cell controls an interval around
any fixed native center. An unchanged palette factor may be included in `C`. -/
theorem original_cell_interval_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → Q) (native : Ω → ℝ) (q : Q)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (C : ENNReal)
    (hcap : ∀ j : ℤ,
      μ {p | base p = q ∧ ⌊native p / a⌋ = j} ≤ C) (center : ℝ) :
    μ {p | base p = q ∧ |native p - center| ≤ L * a} ≤
      ENNReal.ofReal (2 * L + 5) * C := by
  let offsets : Finset ℤ := Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉
  have hsub : {p | base p = q ∧ |native p - center| ≤ L * a} ⊆
      ⋃ j ∈ offsets, {p | base p = q ∧ ⌊native p / a⌋ = ⌊center / a⌋ + j} := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨⌊native p / a⌋ - ⌊center / a⌋, mem_iUnion.mpr ?_⟩
    exact ⟨floor_offset_mem ha hp.2, hp.1, by omega⟩
  have hcard : (offsets.card : ENNReal) ≤ ENNReal.ofReal (2 * L + 5) := by
    calc
      _ = ENNReal.ofReal (offsets.card : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (card_floor_offsets_le hL)
  calc
    _ ≤ μ (⋃ j ∈ offsets,
        {p | base p = q ∧ ⌊native p / a⌋ = ⌊center / a⌋ + j}) := measure_mono hsub
    _ ≤ ∑ j ∈ offsets,
        μ {p | base p = q ∧ ⌊native p / a⌋ = ⌊center / a⌋ + j} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ offsets, C := Finset.sum_le_sum (fun j _ => hcap _)
    _ = (offsets.card : ENNReal) * C := by simp
    _ ≤ _ := mul_le_mul_left hcard C

/-- Null exceptions in the native comparison cost no original mass. -/
theorem original_event_interval_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → Q) (native : Ω → ℝ) (q : Q)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (C : ENNReal)
    (hcap : ∀ j : ℤ,
      μ {p | base p = q ∧ ⌊native p / a⌋ = j} ≤ C)
    (E : Set Ω) (center : ℝ)
    (hE : ∀ᵐ p ∂μ, p ∈ E → base p = q ∧ |native p - center| ≤ L * a) :
    μ E ≤ ENNReal.ofReal (2 * L + 5) * C := by
  exact (measure_mono_ae hE).trans
    (original_cell_interval_cap μ base native q ha hL C hcap center)

/-- Coarse unit native bins and a bounded native signal supply the base-cell
ceiling needed for the first mesh calibration. -/
theorem original_base_cap_from_native_unit_bins {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → Q) (native : Ω → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (C : ENNReal)
    (hcap : ∀ (q : Q) (j : ℤ), μ {p | base p = q ∧ ⌊native p⌋ = j} ≤ C)
    (hbound : ∀ᵐ p ∂μ, |native p| ≤ K) (q : Q) :
    μ {p | base p = q} ≤ ENNReal.ofReal (2 * K + 5) * C := by
  apply original_event_interval_cap μ base native q (a := 1) (by norm_num) hK C
    (fun j => by simpa only [div_one] using hcap q j) {p | base p = q} 0
  filter_upwards [hbound] with p hp hq
  exact ⟨hq, by simpa only [sub_zero, mul_one] using hp⟩

/-- Fine affine error and small base-polynomial oscillation confine the
original native signal to a bounded number of its own fine bins. -/
theorem native_signal_near_base_center (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (L : Fin 4 → ℝ) (x : Fin 4 → ℝ)
    (y : Fin 3 → ℝ) {a K : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (hclose : |eval x (affineBase L) - x 3| ≤ a)
    (hd : |eval x (pderiv 3 P)| ≤ K)
    (hdd : |eval x (pderiv 3 (pderiv 3 P))| ≤ K)
    (hosc : |eval (x ∘ Fin.castSucc) (affineSheetRestriction L P) -
      eval y (affineSheetRestriction L P)| ≤ K * a) :
    |eval x P - eval y (affineSheetRestriction L P)| ≤ 3 * K * a := by
  have hc := affine_correction_error L P hP x ha hclose hd hdd
  rw [eval_baseCalibratedTest] at hc
  have herror : a * K + a ^ 2 / 2 * K ≤ 2 * K * a := by
    nlinarith [mul_nonneg hK (mul_nonneg ha (sub_nonneg.mpr ha1)), mul_nonneg hK ha]
  calc
    _ = |(eval x P - eval (x ∘ Fin.castSucc) (affineSheetRestriction L P)) +
        (eval (x ∘ Fin.castSucc) (affineSheetRestriction L P) -
          eval y (affineSheetRestriction L P))| := by congr 1; ring
    _ ≤ |eval x P - eval (x ∘ Fin.castSucc) (affineSheetRestriction L P)| +
        |eval (x ∘ Fin.castSucc) (affineSheetRestriction L P) -
          eval y (affineSheetRestriction L P)| := abs_add_le _ _
    _ ≤ 2 * K * a + K * a := add_le_add (hc.trans herror) hosc
    _ = _ := by ring

/-- The transfer preserves every factor in the original native cap, including
the original velocity-palette numerator. -/
theorem affine_residual_original_cell_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → Q) (x : Ω → Fin 4 → ℝ) (q : Q)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (L : Fin 4 → ℝ) (y : Fin 3 → ℝ) {a K : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K) (C : ENNReal)
    (hcap : ∀ j : ℤ, μ {p | base p = q ∧ ⌊eval (x p) P / a⌋ = j} ≤ C)
    (E : Set Ω)
    (hE : ∀ᵐ p ∂μ, p ∈ E → base p = q ∧
      |eval (x p) (affineBase L) - x p 3| ≤ a ∧
      |eval (x p) (pderiv 3 P)| ≤ K ∧
      |eval (x p) (pderiv 3 (pderiv 3 P))| ≤ K ∧
      |eval (x p ∘ Fin.castSucc) (affineSheetRestriction L P) -
        eval y (affineSheetRestriction L P)| ≤ K * a) :
    μ E ≤ ENNReal.ofReal (6 * K + 5) * C := by
  have htrace : ∀ᵐ p ∂μ, p ∈ E → base p = q ∧
      |eval (x p) P - eval y (affineSheetRestriction L P)| ≤ (3 * K) * a := by
    filter_upwards [hE] with p hp hpE
    obtain ⟨hbase, hclose, hd, hdd, hosc⟩ := hp hpE
    exact ⟨hbase, native_signal_near_base_center P hP L (x p) y ha.le ha1 hK
      hclose hd hdd hosc⟩
  have heq : 2 * (3 * K) + 5 = 6 * K + 5 := by ring
  simpa only [heq] using original_event_interval_cap μ base (fun p => eval (x p) P) q ha
    (mul_nonneg (by norm_num) hK) C hcap E
    (eval y (affineSheetRestriction L P)) htrace

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
