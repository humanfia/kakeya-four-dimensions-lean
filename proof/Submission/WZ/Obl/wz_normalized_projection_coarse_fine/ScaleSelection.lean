-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ScaleSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset

/-- A suffix-minimum argument for logarithmic covering counts.

Here `t` is a normalized scale parameter, `a` is the normalized logarithm of
the covering count, and `d` is the ambient dimension. The lower bound on `a`
comes from a terminal count of dimension at least `s`, together with the
ambient packing bound between the current scale and the terminal scale.
-/
theorem exists_coarse_frostman_scale {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (i₀ : ι) {s d ε : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht₀ : t i₀ = 0) (ha₀ : a i₀ = 0)
    (ht : ∀ i, t i ≤ 1) (hpacking : ∀ i, s - d * (1 - t i) ≤ a i) :
    ∃ j, t j ≤ 1 - ε ∧ ∀ k,
      s * (t k - t j) - d * ε * (1 - t j) ≤ a k - a j := by
  classical
  let g : ι → ℝ := fun i => a i - s * t i
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image Finset.univ g
    (show (Finset.univ : Finset ι).Nonempty from ⟨i₀, Finset.mem_univ _⟩)
  have hmin' (k : ι) : g j ≤ g k := hmin k (Finset.mem_univ _)
  by_cases hjcoarse : t j ≤ 1 - ε
  · refine ⟨j, hjcoarse, fun k => ?_⟩
    have hm := hmin' k
    have herr : 0 ≤ d * ε * (1 - t j) :=
      mul_nonneg (mul_nonneg hd hε.le) (sub_nonneg.mpr (ht j))
    dsimp [g] at hm
    linarith
  · refine ⟨i₀, by rw [ht₀]; linarith, fun k => ?_⟩
    have hjlate : 1 - ε < t j := lt_of_not_ge hjcoarse
    have htail : 0 ≤ 1 - t j := sub_nonneg.mpr (ht j)
    have hsTail : 0 ≤ s * (1 - t j) := mul_nonneg hs htail
    have hdTail : d * (1 - t j) ≤ d * ε := mul_le_mul_of_nonneg_left (by linarith) hd
    have hp := hpacking j
    have hm := hmin' k
    dsimp [g] at hm
    rw [ht₀, ha₀]
    nlinarith

/-- An unnormalized version permits beginning at a positive scale.
The terminal packing error `e` is carried explicitly. -/
theorem exists_suffix_count_scale {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (i₀ : ι) {L s d e ε : ℝ}
    (hL : t i₀ < L) (hs : 0 ≤ s) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : ∀ i, t i ≤ L)
    (hpacking : ∀ i, s * (L - t i₀) - e - d * (L - t i) ≤ a i - a i₀) :
    ∃ j, t j ≤ L - ε * (L - t i₀) ∧ ∀ k,
      s * (t k - t j) -
        (d * ε + e / (L - t i₀)) * (L - t j) ≤ a k - a j := by
  classical
  let g : ι → ℝ := fun i => a i - s * t i
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image Finset.univ g
    (show (Finset.univ : Finset ι).Nonempty from ⟨i₀, Finset.mem_univ _⟩)
  have hmin' (k : ι) : g j ≤ g k := hmin k (Finset.mem_univ _)
  have hgap : 0 < L - t i₀ := sub_pos.mpr hL
  by_cases hjcoarse : t j ≤ L - ε * (L - t i₀)
  · refine ⟨j, hjcoarse, fun k => ?_⟩
    have hm := hmin' k
    have herr : 0 ≤ (d * ε + e / (L - t i₀)) * (L - t j) :=
      mul_nonneg (add_nonneg (mul_nonneg hd hε.le) (div_nonneg he hgap.le))
        (sub_nonneg.mpr (ht j))
    dsimp [g] at hm
    linarith
  · refine ⟨i₀, ?_, fun k => ?_⟩
    · have := mul_le_mul_of_nonneg_right hε1 hgap.le
      linarith
    · have hjlate : L - ε * (L - t i₀) < t j := lt_of_not_ge hjcoarse
      have htail : 0 ≤ L - t j := sub_nonneg.mpr (ht j)
      have hsTail : 0 ≤ s * (L - t j) := mul_nonneg hs htail
      have hdTail : d * (L - t j) ≤ d * (ε * (L - t i₀)) :=
        mul_le_mul_of_nonneg_left (by linarith) hd
      have hp := hpacking j
      have hm := hmin' k
      have hdiv : e / (L - t i₀) * (L - t i₀) = e := div_mul_cancel₀ _ hgap.ne'
      dsimp [g] at hm
      nlinarith

/-- Multiplicative covering-count form of the coarse-scale selection lemma. -/
theorem exists_frostman_count_scale {ι : Type*} [Fintype ι]
    (t N : ι → ℝ) (i₀ : ι) {B L s d e ε : ℝ}
    (hB : 1 < B) (hN : ∀ i, 0 < N i) (hL : t i₀ < L)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : ∀ i, t i ≤ L)
    (hpacking : ∀ i, N i₀ * B ^ (s * (L - t i₀) - e - d * (L - t i)) ≤ N i) :
    ∃ j, t j ≤ L - ε * (L - t i₀) ∧ ∀ k,
      N j * B ^ (s * (t k - t j) -
        (d * ε + e / (L - t i₀)) * (L - t j)) ≤ N k := by
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hlog : 0 < Real.log B := Real.log_pos hB
  let a : ι → ℝ := fun i => Real.log (N i) / Real.log B
  have hp : ∀ i, s * (L - t i₀) - e - d * (L - t i) ≤ a i - a i₀ := by
    intro i
    have h := Real.log_le_log (mul_pos (hN i₀) (Real.rpow_pos_of_pos hB0 _)) (hpacking i)
    rw [Real.log_mul (hN i₀).ne' (Real.rpow_pos_of_pos hB0 _).ne',
      Real.log_rpow hB0] at h
    dsimp [a]
    rw [← sub_div, le_div_iff₀ hlog]
    linarith
  obtain ⟨j, hj, hjk⟩ := exists_suffix_count_scale t a i₀ hL hs hd he hε hε1 ht hp
  refine ⟨j, hj, fun k => ?_⟩
  apply (Real.log_le_log_iff (mul_pos (hN j) (Real.rpow_pos_of_pos hB0 _)) (hN k)).mp
  rw [Real.log_mul (hN j).ne' (Real.rpow_pos_of_pos hB0 _).ne', Real.log_rpow hB0]
  have h := hjk k
  dsimp [a] at h
  rw [← sub_div, le_div_iff₀ hlog] at h
  linarith

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
