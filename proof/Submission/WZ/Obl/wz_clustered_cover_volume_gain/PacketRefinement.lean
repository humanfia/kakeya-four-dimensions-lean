-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PacketRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

lemma fiberBodyCount_eq_zero {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    {k : Fin N} {p : Space} (hp : p ∉ assignedFiber f Y k) : fiberBodyCount f Y k p = 0 := by
  rw [fiberBodyCount_eq_ncard]
  have he : {i : Fin n | f i = k ∧ p ∈ Y i} = ∅ := by
    ext i
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun hi => hp ⟨i, hi⟩
  simp [he]

lemma packet_count_bound {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    {B M : ℝ} (hB : 0 ≤ B) (p : Space)
    (hfiber : ∀ k, fiberBodyCount f Y k p ≤ B)
    (hpackets : bodyCount (assignedFiber f Y) p ≤ M) :
    bodyCount Y p ≤ M * B := by
  classical
  calc
    bodyCount Y p = ∑ k, fiberBodyCount f Y k p := (sum_fiberBodyCount f Y p).symm
    _ ≤ ∑ k, (assignedFiber f Y k).indicator (fun _ => B) p := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hp : p ∈ assignedFiber f Y k
      · simpa only [indicator_of_mem hp] using hfiber k
      · rw [indicator_of_notMem hp, fiberBodyCount_eq_zero f Y hp]
    _ = bodyCount (assignedFiber f Y) p * B := by
      rw [bodyCount_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hp : p ∈ assignedFiber f Y k <;> simp [hp]
    _ ≤ M * B := mul_le_mul_of_nonneg_right hpackets hB

/-- Independent refinements in packets combine without a loss in retained
mass. Their pointwise bounds add only over packets active at that point. -/
theorem combine_packet_refinements {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    {B M : ℝ} (hB : 0 ≤ B)
    (hactive : ∀ p, bodyCount (assignedFiber f Y) p ≤ M)
    (hrefine : ∀ k : Fin N, ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i ∧ (f i ≠ k → W i = ∅)) ∧
      (1 / 2 : ℝ≥0∞) * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) ≤
        ∑ i, volume (W i) ∧
      ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ M * B := by
  classical
  choose W hW hmass hcount using hrefine
  let Z := fun i => W (f i) i
  have hZm (i : Fin n) : MeasurableSet (Z i) := (hW (f i) i).1
  have hZY (i : Fin n) : Z i ⊆ Y i := (hW (f i) i).2.1
  have hsum (k : Fin N) : ∑ i, volume (W k i) =
      ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f i = k
    · simp [hi, Z]
    · simp [hi, (hW k i).2.2 hi]
  refine ⟨Z, fun i => ⟨hZm i, hZY i⟩, ?_, ?_⟩
  · calc
      _ = ∑ k, (1 / 2 : ℝ≥0∞) * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise]
      _ ≤ ∑ k, ∑ i, volume (W k i) := Finset.sum_le_sum fun k _ => hmass k
      _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i) := by simp only [hsum]
      _ = _ := Finset.sum_fiberwise _ _ _
  · intro p
    apply packet_count_bound f Z hB p
    · intro k
      have he : {i : Fin n | f i = k ∧ p ∈ Z i} = {i : Fin n | p ∈ W k i} := by
        ext i
        change (f i = k ∧ p ∈ Z i) ↔ p ∈ W k i
        constructor
        · rintro ⟨hi, hp⟩
          simpa only [Z, hi] using hp
        · intro hp
          have hi : f i = k := by
            by_contra hne
            simpa only [(hW k i).2.2 hne, mem_empty_iff_false] using hp
          exact ⟨hi, by simpa only [Z, hi] using hp⟩
      rw [fiberBodyCount_eq_ncard, he]
      exact hcount k p
    · apply le_trans _ (hactive p)
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard (fun k hk => by
        obtain ⟨i, hi, hp⟩ := hk
        exact ⟨i, hi, hZY i hp⟩) (Set.toFinite _)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
