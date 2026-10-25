-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_twisted_extraction.Compact.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_sticky_twisted_extraction.Extremal

namespace WangZahlLot.Obl.wz_sticky_twisted_extraction

open Set Metric MeasureTheory
open scoped ENNReal

/-- Inner regularity retains at least half of each shading's mass. Zero-measure
shadings cause no exceptional case in the resulting family. -/
theorem exists_compact_half_mass {n : ℕ} {Y : Fin n → Set Space}
    (hm : ∀ i, MeasurableSet (Y i)) (hf : ∀ i, volume (Y i) ≠ ⊤) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      ∀ i, volume (Y i) / 2 ≤ volume (Z i) := by
  classical
  have hex : ∀ i, ∃ K : Set Space,
      K ⊆ Y i ∧ IsCompact K ∧ volume (Y i) / 2 ≤ volume K := by
    intro i
    by_cases hzero : volume (Y i) = 0
    · exact ⟨∅, empty_subset _, isCompact_empty, by simp [hzero]⟩
    obtain ⟨K, hKY, hK, hmass⟩ := (hm i).exists_lt_isCompact
      (ENNReal.half_lt_self hzero (hf i))
    exact ⟨K, hKY, hK, hmass.le⟩
  choose Z hZY hZ hmass using hex
  exact ⟨Z, hZY, hZ, hmass⟩

/-- Compact refinement with an explicitly quantified loss in the density error. -/
theorem DenseFamily.compact_refinement {η η' δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : DenseFamily η δ n x v Y)
    (hloss : 2 * δ ^ η' ≤ δ ^ η) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      DenseFamily η' δ n x v Z := by
  have hfin : ∀ i, volume (Y i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((h.2.2.2.2.2.1 i).trans (h.2.2.1 i)))
  obtain ⟨Z, hZY, hZ, hmass⟩ := exists_compact_half_mass h.2.2.2.2.1 hfin
  refine ⟨Z, hZY, hZ, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i => (hZ i).measurableSet, fun i => (hZY i).trans (h.2.2.2.2.2.1 i), ?_⟩
  calc
    ENNReal.ofReal (δ ^ η' * (n : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * (δ ^ η * (n : ℝ) * δ ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hη : δ ^ η' ≤ (1 / 2 : ℝ) * δ ^ η := by linarith
      calc
        δ ^ η' * (n : ℝ) * δ ^ 2 ≤
            ((1 / 2 : ℝ) * δ ^ η) * (n : ℝ) * δ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) (sq_nonneg _)
        _ = _ := by ring
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ ≤ (1 / 2 : ENNReal) * ∑ i, volume (Y i) := mul_le_mul' le_rfl h.2.2.2.2.2.2
    _ = ∑ i, volume (Y i) / 2 := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ ∑ i, volume (Z i) := Finset.sum_le_sum (fun i _ => hmass i)

/-- The fixed factor lost in compact refinement is absorbed below an explicit
positive scale, independently of the tube family. -/
theorem exists_compact_refinement_cutoff {η : ℝ} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      2 * δ ^ η ≤ δ ^ (η / 2) := by
  let d : ℝ := (1 / 2 : ℝ) ^ (η / 2)⁻¹
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd
  have hhalf : δ ^ (η / 2) ≤ (1 / 2 : ℝ) := by
    calc
      δ ^ (η / 2) ≤ d ^ (η / 2) :=
        Real.rpow_le_rpow hδ.le hδd (by linarith)
      _ = (1 / 2 : ℝ) := Real.rpow_inv_rpow (by norm_num) (by linarith)
  have heq : δ ^ η = δ ^ (η / 2) * δ ^ (η / 2) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  rw [heq]
  nlinarith [Real.rpow_nonneg hδ.le (η / 2)]

/-- The compact restriction needed for subsequent projection/Fubini arguments
can be made without changing the fixed deficit exponent. -/
theorem VolumeExamples.compact {s : ℝ} (h : VolumeExamples s) :
    ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
      0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        DenseFamily η δ n x v Y ∧ AllScales η δ n x v ∧
        (∀ i, IsCompact (Y i)) ∧ volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s) := by
  intro η d0 hη hd0
  obtain ⟨d, hd, hcut⟩ := exists_compact_refinement_cutoff hη
  obtain ⟨δ, hδ, hδmin, hδ100, n, x, v, Y, hf, hs, hv⟩ :=
    h (η / 2) (min d0 d) (by linarith) (lt_min hd0 hd)
  have hδd : δ ≤ d := hδmin.trans (min_le_right _ _)
  obtain ⟨Z, hZY, hZ, hfZ⟩ := hf.compact_refinement (hcut δ hδ hδd)
  refine ⟨δ, hδ, hδmin.trans (min_le_left _ _), hδ100, n, x, v, Z, hfZ,
    hs.mono_error hδ (by linarith) (by linarith), hZ, ?_⟩
  exact (measure_mono (iUnion_mono hZY)).trans hv

theorem continuous_twistedProjection {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (TwistedProjection f) := by
  unfold TwistedProjection
  fun_prop

theorem isCompact_twistedProjection_union {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, IsCompact (Y i)) {f : ℝ → ℝ} (hf : Continuous f) :
    IsCompact (TwistedProjection f '' (⋃ i, Y i)) :=
  (isCompact_iUnion hY).image (continuous_twistedProjection hf)

end WangZahlLot.Obl.wz_sticky_twisted_extraction
