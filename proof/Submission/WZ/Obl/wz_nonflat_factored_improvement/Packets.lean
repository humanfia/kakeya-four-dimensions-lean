-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.Packets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Incidences
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Prisms
import Submission.WZ.Obl.wz_tower_balanced_refinement

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_tower_balanced_refinement (enumerate enumerate_mem enumerate_injective exists_enumerate)

noncomputable section

/-- Exact containment counts after enumerating an arbitrary finite selection. -/
theorem enumerate_predicate_count {α : Type*} [Finite α] (s : Finset α) (P : α → Prop) :
    Set.ncard {i | P (enumerate s i)} = Set.ncard {i | i ∈ s ∧ P i} := by
  classical
  have he : enumerate s '' {i | P (enumerate s i)} = {i | i ∈ s ∧ P i} := by
    ext i
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨enumerate_mem s k, hk⟩
    · rintro ⟨hi, hp⟩
      obtain ⟨k, rfl⟩ := exists_enumerate s hi
      exact ⟨k, hp, rfl⟩
  rw [← Set.ncard_image_of_injective _ (enumerate_injective s), he]

def packetIndices {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => tube δ (x i) (v i) ⊆ W)

abbrev packetSize {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space) : ℕ :=
  (packetIndices δ x v W).card

abbrev packetIndex {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space) :
    Fin (packetSize δ x v W) → Fin n := enumerate (packetIndices δ x v W)

theorem packetSize_eq {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space) :
    packetSize δ x v W = Set.ncard {i | tube δ (x i) (v i) ⊆ W} := by
  classical
  simp [packetSize, packetIndices, Set.ncard_eq_toFinset_card']

theorem packetIndex_injective {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space) :
    Function.Injective (packetIndex δ x v W) := enumerate_injective _

theorem packetIndex_contained {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W : Set Space)
    (i : Fin (packetSize δ x v W)) :
    tube δ (x (packetIndex δ x v W i)) (v (packetIndex δ x v W i)) ⊆ W := by
  classical
  have h := enumerate_mem (packetIndices δ x v W) i
  simpa only [packetIndex, packetSize, packetIndices, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem packetIndex_count {n : ℕ} (δ : ℝ) (x v : Fin n → Space) (W U : Set Space) :
    Set.ncard {i | tube δ (x (packetIndex δ x v W i)) (v (packetIndex δ x v W i)) ⊆ U} =
      Set.ncard {i | tube δ (x i) (v i) ⊆ W ∧ tube δ (x i) (v i) ⊆ U} := by
  classical
  have h := enumerate_predicate_count (packetIndices δ x v W)
    (fun i => tube δ (x i) (v i) ⊆ U)
  simpa only [packetIndex, packetSize, packetIndices, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem balanced_cover_minimum {n q : ℕ} (hq : 0 < q) (R : Fin n → Fin q → Prop)
    {D : ℝ} (hD : 0 ≤ D) (hcover : ∀ i, ∃ j, R i j)
    (hpos : ∀ j, 0 < Set.ncard {i | R i j})
    (hbalance : ∀ j k, (Set.ncard {i | R i j} : ℝ) ≤ D * Set.ncard {i | R i k}) :
    ∃ N : ℕ, 0 < N ∧ (∀ j, N ≤ Set.ncard {i | R i j}) ∧
      (∀ j, (Set.ncard {i | R i j} : ℝ) ≤ D * N) ∧ (n : ℝ) ≤ q * D * N := by
  classical
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (fun j => Set.ncard {i | R i j})
    Finset.univ_nonempty
  refine ⟨Set.ncard {i | R i j}, hpos j, (fun k => hj k (Finset.mem_univ k)),
    (fun k => hbalance k j), ?_⟩
  have h := bounded_incidence_count (fun j i => R i j) (fun _ => True) (fun _ => True)
    (N := 1) (D := D * Set.ncard {i | R i j}) (by positivity)
    (by
      intro i _
      have hn : 0 < Set.ncard {j | R i j} := Set.ncard_pos (Set.toFinite _) |>.mpr (hcover i)
      exact_mod_cast hn)
    (fun k => hbalance k j) (fun _ _ _ _ => trivial)
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

theorem packet_meets_ball {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (hB : ∀ i, tube δ (x i) (v i) ⊆ unitBall) (W : Set Space)
    (hN : 0 < packetSize δ x v W) : (W ∩ unitBall).Nonempty := by
  let i : Fin (packetSize δ x v W) := ⟨0, hN⟩
  let k := packetIndex δ x v W i
  have hx : x k ∈ tube δ (x k) (v k) :=
    self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  exact ⟨x k, packetIndex_contained δ x v W i hx, hB k hx⟩

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
