-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CellLevelSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicPower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open scoped Classical

/-- A bounded integer parameter has a heavy exact level. Zero-weight indices
may have arbitrary parameters and do not affect the bound. -/
theorem weighted_exact_level {N : ℕ} (K : ℕ) (k : Fin N → ℕ) (w : Fin N → ENNReal)
    (hk : ∀ j, w j ≠ 0 → k j ≤ K) :
    ∃ (m : ℕ) (A : Finset (Fin N)), m ≤ K ∧ (∀ j ∈ A, k j = m) ∧
      (∑ j, w j) ≤ (K + 1 : ℕ) * ∑ j ∈ A, w j := by
  let col : Fin N → Fin (K + 1) := fun j => ⟨min (k j) K, Nat.lt_succ_of_le (min_le_right _ _)⟩
  obtain ⟨m, hmass⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (Nat.succ_pos K) Finset.univ col w
  let A := Finset.univ.filter fun j => k j = m.val
  have hsum : (∑ j ∈ Finset.univ.filter (fun j => col j = m), w j) = ∑ j ∈ A, w j := by
    simp only [A, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : w j = 0
    · simp [hz]
    · have hc : col j = m ↔ k j = m.val := by
        rw [Fin.ext_iff]
        simp only [col, min_eq_left (hk j hz)]
      simp only [hc]
  refine ⟨m.val, A, Nat.le_of_lt_succ m.isLt,
    fun j hj => (Finset.mem_filter.mp hj).2, ?_⟩
  simpa only [hsum] using hmass

/-- Whole local packets with a common dyadic multiplicity level retain a
logarithmic share of their total shading mass. -/
theorem common_cell_multiplicity_level {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n N : ℕ} (Y : Fin N → Fin n → Set X) (k : Fin N → ℕ)
    (hlevel : ∀ j p, p ∈ ⋃ i, Y j i →
      2 ^ k j ≤ (Finset.univ.filter fun i => p ∈ Y j i).card) :
    ∃ (m : ℕ) (A : Finset (Fin N)), m ≤ Nat.log 2 n ∧ (∀ j ∈ A, k j = m) ∧
      (∑ j, ∑ i, μ (Y j i)) ≤ (Nat.log 2 n + 1 : ℕ) * ∑ j ∈ A, ∑ i, μ (Y j i) := by
  apply weighted_exact_level (Nat.log 2 n) k (fun j => ∑ i, μ (Y j i))
  intro j hj
  have hne : (⋃ i, Y j i).Nonempty := by
    by_contra hh
    have hempty := not_nonempty_iff_eq_empty.mp hh
    have hzero (i : Fin n) : Y j i = ∅ := eq_empty_of_subset_empty (hempty ▸ subset_iUnion (Y j) i)
    simp only [hzero, measure_empty, Finset.sum_const_zero, ne_eq, not_true_eq_false] at hj
  obtain ⟨p, hp⟩ := hne
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  exact (hlevel j p hp).trans (by simpa using (Finset.univ.filter fun i => p ∈ Y j i).card_le_univ)

/-- The common packet level costs an arbitrarily small power of the scale,
without changing any packet internally. -/
theorem common_cell_multiplicity_level_power {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      ∀ n : ℕ, (n : ℝ) ≤ δ ^ (-D) →
      ∀ (X : Type*) [MeasurableSpace X] (μ : Measure X) (N : ℕ)
        (Y : Fin N → Fin n → Set X) (k : Fin N → ℕ),
        (∀ j p, p ∈ ⋃ i, Y j i → 2 ^ k j ≤ (Finset.univ.filter fun i => p ∈ Y j i).card) →
        ∃ (m : ℕ) (A : Finset (Fin N)), m ≤ Nat.log 2 n ∧ (∀ j ∈ A, k j = m) ∧
          ENNReal.ofReal (δ ^ ε) * (∑ j, ∑ i, μ (Y j i)) ≤ ∑ j ∈ A, ∑ i, μ (Y j i) := by
  obtain ⟨d, hd, hlog⟩ := logarithmic_count_power hD hε
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd n hn X _ μ N Y k hlevel
  obtain ⟨m, A, hm, hA, hmass⟩ := common_cell_multiplicity_level μ Y k hlevel
  refine ⟨m, A, hm, hA, ?_⟩
  have hlog' : ((Nat.log 2 n + 1 : ℕ) : ENNReal) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hlog δ hδ hδd n hn)
  have hh : (∑ j, ∑ i, μ (Y j i)) ≤ ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ A, ∑ i, μ (Y j i) :=
    hmass.trans (mul_le_mul_left hlog' _)
  have he : ENNReal.ofReal (δ ^ ε) * ENNReal.ofReal (δ ^ (-ε)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
    simp
  calc
    _ ≤ ENNReal.ofReal (δ ^ ε) * (ENNReal.ofReal (δ ^ (-ε)) * ∑ j ∈ A, ∑ i, μ (Y j i)) :=
      mul_le_mul_right hh _
    _ = _ := by rw [← mul_assoc, he, one_mul]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
