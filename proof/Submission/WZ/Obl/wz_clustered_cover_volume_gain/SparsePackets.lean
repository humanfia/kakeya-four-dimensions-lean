-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SparsePackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

local instance sparsePacketsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Discarding packets below an assigned mass threshold costs at most the
sum of those thresholds over the original objects. -/
theorem select_dense_packets {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    (hYm : ∀ i, MeasurableSet (Y i)) (cost : Fin n → ℝ≥0∞) :
    ∃ (good : Finset (Fin N)) (Z : Fin n → Set Space),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (f i ∉ good → Z i = ∅)) ∧
      (∀ k ∈ good, (∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) ≤
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i)) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (Z i)) + ∑ i, cost i := by
  let good := Finset.univ.filter fun k =>
    (∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) ≤
      ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)
  let Z := fun i => if f i ∈ good then Y i else ∅
  have hsum (k : Fin N) (hk : k ∈ good) :
      (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i)) =
        ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hfi := (Finset.mem_filter.mp hi).2
    simp only [Z, hfi, if_pos hk]
  have hpiece (k : Fin N) :
      (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) ≤
        (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i)) +
          ∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i := by
    by_cases hk : k ∈ good
    · rw [hsum k hk]
      exact le_add_right le_rfl
    · have hbad : ¬ (∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) ≤
          ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i) := by
        simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact (le_of_lt (lt_of_not_ge hbad)).trans (le_add_left le_rfl)
  refine ⟨good, Z, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : f i ∈ good
    · simp only [Z, if_pos hi]
      exact ⟨hYm i, subset_rfl, fun h => (h hi).elim⟩
    · simp only [Z, if_neg hi]
      exact ⟨MeasurableSet.empty, empty_subset _, fun _ => by trivial⟩
  · intro k hk
    rw [hsum k hk]
    exact (Finset.mem_filter.mp hk).2
  · calc
      _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i) :=
        (Finset.sum_fiberwise _ _ _).symm
      _ ≤ ∑ k, ((∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i)) +
          ∑ i ∈ Finset.univ.filter (fun i => f i = k), cost i) :=
        Finset.sum_le_sum fun k _ => hpiece k
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_fiberwise, Finset.sum_fiberwise]

lemma half_mass_after_loss {M P E : ℝ≥0∞} (hM : M ≠ ⊤)
    (hloss : M ≤ P + E) (hbudget : E ≤ (1 / 2 : ℝ≥0∞) * M) :
    (1 / 2 : ℝ≥0∞) * M ≤ P := by
  have he : (1 / 2 : ℝ≥0∞) * M + (1 / 2 : ℝ≥0∞) * M = M := by
    rw [← add_mul, one_div, ENNReal.inv_two_add_inv_two, one_mul]
  have hh : (1 / 2 : ℝ≥0∞) * M + (1 / 2 : ℝ≥0∞) * M ≤ P + (1 / 2 : ℝ≥0∞) * M := by
    rw [he]
    exact hloss.trans (add_le_add le_rfl hbudget)
  exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hM)).mp hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
