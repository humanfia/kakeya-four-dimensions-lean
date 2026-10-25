-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.Compact.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- Retaining half the mass can always be done by compact subsets, including null sets. -/
theorem compact_half_mass {A : Set Space} (hA : MeasurableSet A) (hfin : volume A ≠ ∞) :
    ∃ K : Set Space, K ⊆ A ∧ IsCompact K ∧ volume A / 2 ≤ volume K := by
  by_cases hzero : volume A = 0
  · exact ⟨∅, empty_subset _, isCompact_empty, by simp [hzero]⟩
  obtain ⟨K, hKA, hK, hm⟩ :=
    hA.exists_lt_isCompact_of_ne_top hfin (ENNReal.half_lt_self hzero hfin)
  exact ⟨K, hKA, hK, hm.le⟩

/-- Compact approximation changes neither the tubes nor their separated covers. -/
theorem Family.compact_refinement {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (h : Family η δ n x v Y)
    (hp : δ ^ ε ≤ δ ^ η / 2) :
    ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
      Family ε δ n x v Z := by
  have hfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((h.2.2.2.2.2.1 i).trans (h.2.2.1 i)))
  choose Z hZY hZ hmass using fun i => compact_half_mass (h.2.2.2.2.1 i) (hfin i)
  refine ⟨Z, hZY, hZ, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i => (hZ i).measurableSet, fun i => (hZY i).trans (h.2.2.2.2.2.1 i), ?_⟩
  calc
    ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal ((δ ^ η * (n : ℝ) * δ ^ 2) / 2) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        δ ^ ε * (n : ℝ) * δ ^ 2 ≤ (δ ^ η / 2) * (n : ℝ) * δ ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) (sq_nonneg _)
        _ = _ := by ring
    _ = ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ ≤ (∑ i, volume (Y i)) / 2 := by gcongr; exact h.2.2.2.2.2.2
    _ = ∑ i, volume (Y i) / 2 := by rw [div_eq_mul_inv, Finset.sum_mul]; rfl
    _ ≤ ∑ i, volume (Z i) := Finset.sum_le_sum fun i _ => hmass i

/-- The entire compact, almost-extremal part of the target follows before constructing
any plane map or slope function. -/
theorem compact_extremal_examples {σ : ℝ} (hbelow : ∀ t : ℝ, t < σ → Examples t)
    (ε d0 : ℝ) (hε : 0 < ε) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family ε δ n x v Y ∧ Separated ε δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
          volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) := by
  let d1 : ℝ := (1 / 2 : ℝ) ^ (2 / ε)
  have hd1 : 0 < d1 := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hV⟩ :=
    hbelow (σ - ε) (by linarith) (ε / 2) (min d0 d1) (by positivity) (lt_min hd0 hd1)
  have hδd1 : δ ≤ d1 := hδ0.trans (min_le_right _ _)
  have hpower : δ ^ (ε / 2) ≤ 1 / 2 := by
    calc
      δ ^ (ε / 2) ≤ d1 ^ (ε / 2) := Real.rpow_le_rpow hδ.le hδd1 (by positivity)
      _ = 1 / 2 := by
        dsimp [d1]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have heq : 2 / ε * (ε / 2) = 1 := by field_simp
        rw [heq, Real.rpow_one]
  have hp : δ ^ ε ≤ δ ^ (ε / 2) / 2 := by
    calc
      δ ^ ε = δ ^ (ε / 2) * δ ^ (ε / 2) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (ε / 2) * (1 / 2) := by gcongr
      _ = _ := by ring
  obtain ⟨Z, hZY, hZ, hHZ⟩ := hH.compact_refinement hp
  exact ⟨δ, hδ, hδ0.trans (min_le_left _ _), hδmax, n, x, v, Z, hHZ,
    hS.mono_error hδ (by linarith) (by linarith), hZ,
    (measure_mono (iUnion_mono hZY)).trans hV⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
