-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/BandBounds.lean. Existing attribution comments are retained below.

import Mathlib

/-! Band bounds for laws whose binned observation has a density.

If the observation `p ↦ (y p, ⌊h p / a⌋)` of a measure `μ` has density `g` with respect to
`volume ⊗ count`, then the part of `μ` where `g ≤ c` and the hidden value `h` lies within
`W` of a measurable graph `G (y)` over a base region `Reg` has mass at most
`c · vol(Reg) · (2W/a + 2)`. -/

namespace Submission.Obl.k4_paired_test_normalization

open MeasureTheory Set

/-- Integers `n` with `lo ≤ n a ≤ hi` number at most `(hi - lo)/a + 1`. -/
lemma count_int_window_le {a lo hi : ℝ} (ha : 0 < a) (hlh : lo ≤ hi) :
    Measure.count {n : ℤ | lo ≤ n * a ∧ n * a ≤ hi} ≤ ENNReal.ofReal ((hi - lo) / a + 1) := by
  have hsub : {n : ℤ | lo ≤ n * a ∧ n * a ≤ hi} ⊆ (Finset.Icc ⌈lo / a⌉ ⌊hi / a⌋ : Set ℤ) := by
    intro n ⟨h1, h2⟩
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ ha]; exact h1
    · rw [Int.le_floor, le_div_iff₀ ha]; exact h2
  calc Measure.count {n : ℤ | lo ≤ n * a ∧ n * a ≤ hi}
      ≤ Measure.count (Finset.Icc ⌈lo / a⌉ ⌊hi / a⌋ : Set ℤ) := measure_mono hsub
    _ = (Finset.Icc ⌈lo / a⌉ ⌊hi / a⌋).card := Measure.count_apply_finset _
    _ ≤ ENNReal.ofReal ((hi - lo) / a + 1) := by
        rw [Int.card_Icc]
        have h1 : ((⌊hi / a⌋ + 1 - ⌈lo / a⌉).toNat : ℝ) ≤ (hi - lo) / a + 1 := by
          have hfl := Int.floor_le (hi / a)
          have hce := Int.le_ceil (lo / a)
          rcases le_or_gt (⌊hi / a⌋ + 1 - ⌈lo / a⌉) 0 with h | h
          · rw [Int.toNat_of_nonpos h]
            simp only [Nat.cast_zero]
            have : 0 ≤ (hi - lo) / a := div_nonneg (by linarith) ha.le
            linarith
          · rw [show ((⌊hi / a⌋ + 1 - ⌈lo / a⌉).toNat : ℝ) =
                ((⌊hi / a⌋ + 1 - ⌈lo / a⌉ : ℤ) : ℝ) by
              rw [← Int.cast_natCast, Int.toNat_of_nonneg h.le]]
            push_cast
            rw [sub_div]
            linarith
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal h1

/-- **Band bound.** -/
theorem band_mass_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (y : X → EuclideanSpace ℝ (Fin 3)) (h : X → ℝ) {a : ℝ} (ha : 0 < a)
    (hobs : Measurable (fun p => (y p, ⌊h p / a⌋)))
    (g : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg : Measurable g)
    (hmap : μ.map (fun p => (y p, ⌊h p / a⌋)) = (volume.prod Measure.count).withDensity g)
    (c : ENNReal) (Reg : Set (EuclideanSpace ℝ (Fin 3))) (hReg : MeasurableSet Reg)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (hG : Measurable G) {W : ℝ} (hW : 0 ≤ W) :
    μ {p | g (y p, ⌊h p / a⌋) ≤ c ∧ y p ∈ Reg ∧ |h p - G (y p)| ≤ W} ≤
      c * volume Reg * ENNReal.ofReal (2 * W / a + 2) := by
  set ob : X → EuclideanSpace ℝ (Fin 3) × ℤ := fun p => (y p, ⌊h p / a⌋) with hob
  set A : Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
    {q | q.1 ∈ Reg ∧ G q.1 - W - a ≤ (q.2 : ℝ) * a ∧ (q.2 : ℝ) * a ≤ G q.1 + W} with hA_def
  have hz : Measurable (fun q : EuclideanSpace ℝ (Fin 3) × ℤ => ((q.2 : ℝ) * a)) :=
    (measurable_of_countable (fun n : ℤ => (n : ℝ) * a)).comp measurable_snd
  have hGq : Measurable (fun q : EuclideanSpace ℝ (Fin 3) × ℤ => G q.1) := hG.comp measurable_fst
  have hA : MeasurableSet A := by
    refine (hReg.preimage measurable_fst).inter ((measurableSet_le ?_ hz).inter
      (measurableSet_le hz ?_))
    · exact (hGq.sub_const W).sub_const a
    · exact hGq.add_const W
  have hAc : MeasurableSet (A ∩ {q | g q ≤ c}) := hA.inter (measurableSet_le hg measurable_const)
  have hsub : {p | g (y p, ⌊h p / a⌋) ≤ c ∧ y p ∈ Reg ∧ |h p - G (y p)| ≤ W} ⊆
      ob ⁻¹' (A ∩ {q | g q ≤ c}) := by
    intro p ⟨hgc, hR, hb⟩
    have hfl := Int.floor_le (h p / a)
    have hfl2 := Int.lt_floor_add_one (h p / a)
    have h1 : (⌊h p / a⌋ : ℝ) * a ≤ h p := by
      have := mul_le_mul_of_nonneg_right hfl ha.le
      rwa [div_mul_cancel₀ _ ha.ne'] at this
    have h2 : h p < ((⌊h p / a⌋ : ℝ) + 1) * a := by
      have := mul_lt_mul_of_pos_right hfl2 ha
      rwa [div_mul_cancel₀ _ ha.ne'] at this
    rw [abs_le] at hb
    refine ⟨⟨hR, ?_, ?_⟩, hgc⟩
    · show G (y p) - W - a ≤ (⌊h p / a⌋ : ℝ) * a
      nlinarith
    · show (⌊h p / a⌋ : ℝ) * a ≤ G (y p) + W
      linarith
  calc μ {p | g (y p, ⌊h p / a⌋) ≤ c ∧ y p ∈ Reg ∧ |h p - G (y p)| ≤ W}
      ≤ μ (ob ⁻¹' (A ∩ {q | g q ≤ c})) := measure_mono hsub
    _ = (μ.map ob) (A ∩ {q | g q ≤ c}) := (Measure.map_apply hobs hAc).symm
    _ = ∫⁻ q in A ∩ {q | g q ≤ c}, g q ∂(volume.prod Measure.count) := by
        rw [hmap, withDensity_apply _ hAc]
    _ ≤ ∫⁻ q in A ∩ {q | g q ≤ c}, c ∂(volume.prod Measure.count) := by
        apply setLIntegral_mono measurable_const
        intro q hq
        exact hq.2
    _ = c * (volume.prod Measure.count) (A ∩ {q | g q ≤ c}) := by
        rw [setLIntegral_const]
    _ ≤ c * (volume.prod Measure.count) A := by gcongr; exact inter_subset_left
    _ ≤ c * (volume Reg * ENNReal.ofReal (2 * W / a + 2)) := by
        gcongr
        rw [Measure.prod_apply hA]
        calc ∫⁻ z, Measure.count (Prod.mk z ⁻¹' A) ∂volume
            ≤ ∫⁻ z, Reg.indicator (fun _ => ENNReal.ofReal (2 * W / a + 2)) z ∂volume := by
              apply lintegral_mono
              intro z
              show Measure.count (Prod.mk z ⁻¹' A) ≤ _
              by_cases hz : z ∈ Reg
              · rw [indicator_of_mem hz]
                have : Prod.mk z ⁻¹' A =
                    {n : ℤ | G z - W - a ≤ n * a ∧ n * a ≤ G z + W} := by
                  ext n; simp [A, hz]
                rw [this]
                calc _ ≤ ENNReal.ofReal ((G z + W - (G z - W - a)) / a + 1) :=
                      count_int_window_le ha (by linarith)
                  _ = ENNReal.ofReal (2 * W / a + 2) := by
                      congr 1; field_simp; ring
              · rw [indicator_of_notMem hz]
                have : Prod.mk z ⁻¹' A = ∅ := by
                  ext n; simp [A, hz]
                rw [this, measure_empty]
          _ = ENNReal.ofReal (2 * W / a + 2) * volume Reg := lintegral_indicator_const hReg _
          _ = volume Reg * ENNReal.ofReal (2 * W / a + 2) := mul_comm _ _
    _ = c * volume Reg * ENNReal.ofReal (2 * W / a + 2) := by ring

end Submission.Obl.k4_paired_test_normalization
