import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Schedule
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.TreeChoice
import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Fiber

set_option autoImplicit false

/-!
# Auxiliary facts for the assembly of the higher jets

* `exists_good_block`: some dyadic block of length `2⁻ᵀ` carries at least half of the average
  labelled mass (the label fraction `treeP 0` integrates to `≥ m/2`);
* `lintegral_mul_pow_ge`: a Markov lower bound for `∫ a · aᵉ` when `a ≤ 1` and `∫ a ≥ m/2`;
* `gapLoss_le`: `gapLoss Kg k ≤ 2^{k+1} / Kg`;
* `block_lintegral_eq`: Tonelli, `∫_{block} ν{l ∈ D, (l,t) labelled} dt = 2⁻ᵀ ∫_D treeP 0 dν`;
* `blockIco_eq_dI`: the half-open block of a point of `dI T j` is `dI T j`.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Λ : Type*} [MeasurableSpace Λ]

theorem blockIco_eq_dI {T : ℕ} {j : ℤ} {u : ℝ} (hu : u ∈ dI T j) : blockIco T u = dI T j := by
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  obtain ⟨h1, h3⟩ := hu
  have hfl : ⌊u * 2 ^ T⌋ = j := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [div_le_iff₀ h2] at h1; exact h1
    · rw [lt_div_iff₀ h2] at h3; exact h3
  simp only [blockIco, dI, hfl]

theorem gapLoss_le {Kg : ℝ} (hKg : 0 < Kg) : ∀ k, gapLoss Kg k ≤ (2 ^ (k + 1) - 2) / Kg
  | 0 => by simp [gapLoss]
  | k + 1 => by
    have ih := gapLoss_le hKg k
    simp only [gapLoss]
    have e : (2 ^ (k + 1 + 1) - 2 : ℝ) / Kg = 2 * ((2 ^ (k + 1) - 2) / Kg) + 2 / Kg := by
      field_simp; ring
    rw [e]; linarith

theorem gapLoss_le' {Kg : ℝ} (hKg : 0 < Kg) (k : ℕ) : gapLoss Kg k ≤ 2 ^ (k + 1) / Kg :=
  (gapLoss_le hKg k).trans (div_le_div_of_nonneg_right (by linarith) hKg.le)

/-- The label fraction of one block, integrated. -/
theorem lintegral_treeP_zero (Lab : Set (Λ × ℝ)) (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ)
    (ν : Measure Λ) [SFinite ν] (n : ℕ) (j : ℤ) :
    ∫⁻ l, treeP Lab Tl 0 univ l n j ∂ν = (ν.prod volume) (Lab ∩ univ ×ˢ dI n j) * 2 ^ n := by
  have hS : MeasurableSet (Lab ∩ univ ×ˢ dI n j) :=
    hLab.inter (MeasurableSet.univ.prod (measurableSet_dI n j))
  rw [Measure.prod_apply hS, ← lintegral_mul_const _ ?_]
  · refine lintegral_congr fun l => ?_
    simp only [treeP]
    congr 1
    congr 1
    ext t
    simp only [mem_inter_iff, mem_univ, and_true, mem_ofPred_eq, mem_preimage, mem_prod,
      true_and]
    tauto
  · exact measurable_measure_prodMk_left hS

/-- Some dyadic block carries half of the average labelled mass. -/
theorem exists_good_block {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab)
    (htime : ∀ p ∈ Lab, p.2 ∈ Icc (0 : ℝ) 1) (Tl : ℕ → ℕ) (ν : Measure Λ) [SFinite ν] (T : ℕ)
    {m : ℝ} (hm : ENNReal.ofReal m ≤ (ν.prod volume) Lab) :
    ∃ j : ℤ, ENNReal.ofReal (m / 2) ≤ ∫⁻ l, treeP Lab Tl 0 univ l T j ∂ν := by
  classical
  by_contra hall
  push Not at hall
  set s := Finset.range (2 ^ T + 1)
  have hsne : s.Nonempty := ⟨0, Finset.mem_range.mpr (by positivity)⟩
  have hlt : ∑ j ∈ s, ∫⁻ l, treeP Lab Tl 0 univ l T (j : ℤ) ∂ν <
      ∑ _j ∈ s, ENNReal.ofReal (m / 2) :=
    ENNReal.sum_lt_sum_of_nonempty hsne fun j _ => hall j
  -- the blocks cover the labels
  have hcov : Lab ⊆ ⋃ j ∈ s, Lab ∩ univ ×ˢ dI T (j : ℤ) := by
    intro p hp
    have ht := htime p hp
    have h2 : (0 : ℝ) < 2 ^ T := by positivity
    set j := ⌊p.2 * 2 ^ T⌋₊
    have hx0 : 0 ≤ p.2 * 2 ^ T := mul_nonneg ht.1 h2.le
    have hj : j < 2 ^ T + 1 := by
      have : j ≤ 2 ^ T := by
        apply Nat.floor_le_of_le
        push_cast
        calc p.2 * 2 ^ T ≤ 1 * 2 ^ T := by gcongr; exact ht.2
          _ = 2 ^ T := one_mul _
      omega
    refine mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, hp, mem_univ _, ?_⟩
    simp only [dI, Int.cast_natCast, mem_Ico]
    constructor
    · rw [div_le_iff₀ h2]; exact Nat.floor_le hx0
    · rw [lt_div_iff₀ h2]; exact Nat.lt_floor_add_one _
  have hsum : (ν.prod volume) Lab ≤ ∑ j ∈ s, (ν.prod volume) (Lab ∩ univ ×ˢ dI T (j : ℤ)) :=
    (measure_mono hcov).trans (measure_biUnion_finset_le s _)
  have hge : (2 : ℝ≥0∞) ^ T * ENNReal.ofReal m ≤
      ∑ j ∈ s, ∫⁻ l, treeP Lab Tl 0 univ l T (j : ℤ) ∂ν := by
    simp only [lintegral_treeP_zero Lab hLab Tl ν T]
    rw [← Finset.sum_mul, mul_comm]
    gcongr
    exact hm.trans hsum
  have hle : ∑ _j ∈ s, ENNReal.ofReal (m / 2) ≤ (2 : ℝ≥0∞) ^ T * ENNReal.ofReal m := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rcases le_or_gt m 0 with hm0 | hm0
    · rw [ENNReal.ofReal_of_nonpos (by linarith), mul_zero]; exact bot_le
    · have e : ENNReal.ofReal m = 2 * ENNReal.ofReal (m / 2) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
      rw [e, ← mul_assoc]
      gcongr
      push_cast
      calc (2 : ℝ≥0∞) ^ T + 1 ≤ 2 ^ T + 2 ^ T := by gcongr; exact one_le_pow₀ (by norm_num)
        _ = 2 ^ T * 2 := by ring
  exact absurd (hlt.trans_le (hle.trans hge)) (lt_irrefl _)

/-- Markov lower bound. -/
theorem lintegral_mul_pow_ge {ν : Measure Λ} [IsProbabilityMeasure ν] {a : Λ → ℝ≥0∞}
    (ha : Measurable a) (ha1 : ∀ l, a l ≤ 1) {m : ℝ} (hm : 0 ≤ m)
    (h : ENNReal.ofReal (m / 2) ≤ ∫⁻ l, a l ∂ν) (e : ℕ) :
    ENNReal.ofReal ((m / 4) ^ (e + 2)) ≤ ∫⁻ l, a l * a l ^ e ∂ν := by
  classical
  set c := ENNReal.ofReal (m / 4)
  set G := {l | c ≤ a l}
  have hG : MeasurableSet G := measurableSet_le measurable_const ha
  -- the large set has mass at least `c`
  have h1 : ∫⁻ l, a l ∂ν ≤ ν G + c := by
    calc ∫⁻ l, a l ∂ν ≤ ∫⁻ l, (G.indicator (fun _ => (1 : ℝ≥0∞)) l + c) ∂ν := by
          apply lintegral_mono
          intro l
          by_cases hl : l ∈ G
          · simp only [hl, indicator_of_mem]; exact (ha1 l).trans le_self_add
          · simp only [hl, not_false_eq_true, indicator_of_notMem, zero_add]
            exact (lt_of_not_ge hl).le
      _ = ν G + c := by
          rw [lintegral_add_right _ measurable_const, lintegral_indicator_const hG, lintegral_const,
            measure_univ, mul_one, one_mul]
  have hc2 : ENNReal.ofReal (m / 2) = c + c := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hcG : c ≤ ν G := by
    have h2 := h.trans h1
    rw [hc2] at h2
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h2
  -- the integral of `a · aᵉ` over the large set
  calc ENNReal.ofReal ((m / 4) ^ (e + 2)) = c ^ (e + 1) * c := by
        rw [← pow_succ, ENNReal.ofReal_pow (by positivity)]
    _ ≤ c ^ (e + 1) * ν G := by gcongr
    _ = ∫⁻ l, G.indicator (fun _ => c ^ (e + 1)) l ∂ν := (lintegral_indicator_const hG _).symm
    _ ≤ ∫⁻ l, a l * a l ^ e ∂ν := by
        apply lintegral_mono
        intro l
        by_cases hl : l ∈ G
        · simp only [hl, indicator_of_mem]
          rw [pow_succ', mul_comm]
          have hl' : c ≤ a l := hl
          calc c ^ e * c ≤ a l ^ e * a l := by gcongr
            _ = a l * a l ^ e := mul_comm _ _
        · simp only [hl, not_false_eq_true, indicator_of_notMem]; exact bot_le

/-- Tonelli on one block. -/
theorem block_lintegral_eq {Lab : Set (Λ × ℝ)} (hLab : MeasurableSet Lab) (Tl : ℕ → ℕ)
    (ν : Measure Λ) [SFinite ν] {D : Set Λ} (hD : MeasurableSet D) (T : ℕ) (j : ℤ) :
    ∫⁻ t in dI T j, ν {l | l ∈ D ∧ (l, t) ∈ Lab} =
      ENNReal.ofReal ((2 ^ T)⁻¹) * ∫⁻ l in D, treeP Lab Tl 0 univ l T j ∂ν := by
  set Z : Set (Λ × ℝ) := {p | p.1 ∈ D ∧ p.2 ∈ dI T j ∧ p ∈ Lab}
  have hZ : MeasurableSet Z :=
    (measurable_fst hD).inter ((measurable_snd (measurableSet_dI T j)).inter hLab)
  have hJ := measurableSet_dI T j
  -- left side
  have hL : ∫⁻ t in dI T j, ν {l | l ∈ D ∧ (l, t) ∈ Lab} = (ν.prod volume) Z := by
    rw [Measure.prod_apply_symm hZ, ← lintegral_indicator hJ]
    congr 1
    ext t
    by_cases ht : t ∈ dI T j
    · simp only [ht, indicator_of_mem]
      congr 1
      ext l
      simp only [mem_ofPred_eq, mem_preimage, Z, ht, true_and]
    · simp only [ht, not_false_eq_true, indicator_of_notMem]
      symm
      convert measure_empty (μ := ν)
      ext l
      simp only [mem_preimage, mem_empty_iff_false, iff_false, Z, mem_ofPred_eq]
      tauto
  -- right side
  have h2T : ENNReal.ofReal ((2 ^ T)⁻¹) * (2 : ℝ≥0∞) ^ T = 1 := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      show ENNReal.ofReal ((2 : ℝ) ^ T) = (2 : ℝ≥0∞) ^ T by
        rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)
  have hR : ∫⁻ l in D, treeP Lab Tl 0 univ l T j ∂ν = (ν.prod volume) Z * 2 ^ T := by
    rw [Measure.prod_apply hZ, ← lintegral_mul_const _ (measurable_measure_prodMk_left hZ),
      ← lintegral_indicator hD]
    congr 1
    ext l
    by_cases hl : l ∈ D
    · simp only [hl, indicator_of_mem, treeP]
      congr 1
      congr 1
      ext t
      simp only [mem_inter_iff, mem_univ, and_true, mem_ofPred_eq, mem_preimage, Z, hl, true_and]
    · simp only [hl, not_false_eq_true, indicator_of_notMem]
      have : Prod.mk l ⁻¹' Z = ∅ := by
        ext t; simp only [mem_preimage, mem_empty_iff_false, iff_false, Z, mem_ofPred_eq]
        tauto
      rw [this, measure_empty, zero_mul]
  rw [hL, hR, mul_comm ((ν.prod volume) Z), ← mul_assoc, h2T, one_mul]

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
