-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.FibreShadings.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

def fibreShading {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) (i : Fin n) : Set V :=
  if i ∈ S ∧ f i = k then Z i else ∅

theorem mem_fibreShading {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) (i : Fin n) (p : V) :
    p ∈ fibreShading S f Z k i ↔ i ∈ S ∧ f i = k ∧ p ∈ Z i := by
  classical
  by_cases hi : i ∈ S ∧ f i = k
  · simp [fibreShading, hi, hi.1, hi.2]
  · simp only [fibreShading, ite_eq_right hi, Set.mem_empty_iff_false, false_iff]
    exact fun h => hi ⟨h.1, h.2.1⟩

theorem fibreShading_measurable {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (hZ : ∀ i, MeasurableSet (Z i)) (k : Fin N) (i : Fin n) :
    MeasurableSet (fibreShading S f Z k i) := by
  classical
  dsimp only [fibreShading]
  split_ifs
  · exact hZ i
  · exact MeasurableSet.empty

theorem fibreShading_subset {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) (i : Fin n) : fibreShading S f Z k i ⊆ Z i :=
  fun p hp => ((mem_fibreShading S f Z k i p).mp hp).2.2

theorem fibreShading_zero {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) (i : Fin n)
    (hi : i ∉ S.filter (fun i => f i = k)) : fibreShading S f Z k i = ∅ := by
  classical
  exact ite_eq_right (fun h => hi (Finset.mem_filter.mpr h))

theorem sum_fibreShading {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) :
    (∑ i, μ (fibreShading S f Z k i)) = ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
  classical
  have he : S.filter (fun i => f i = k) =
      Finset.univ.filter (fun i => i ∈ S ∧ f i = k) := by ext i; simp
  rw [he, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S ∧ f i = k <;> simp [fibreShading, hi, μ]

theorem sum_fibreShading_on_fibre {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set V) (k : Fin N) :
    (∑ i ∈ S.filter (fun i => f i = k), μ (fibreShading S f Z k i)) =
      ∑ i ∈ S.filter (fun i => f i = k), μ (Z i) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [fibreShading, ite_eq_left (Finset.mem_filter.mp hi)]

/-- A supported fibre has no shading mass outside its fine-index set. -/
theorem sum_supported_fibre {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (W : Fin n → Set V) (k : Fin N)
    (hsupport : ∀ i p, p ∈ W i → i ∈ S ∧ f i = k) :
    (∑ i ∈ S.filter (fun i => f i = k), μ (W i)) = ∑ i, μ (W i) := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have he : W i = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun p hp =>
    hi (Finset.mem_filter.mpr (hsupport i p hp)))
  simp [he, μ]

/-- Summing supported packets over coarse indices equals the shading mass
of their joined fine family. -/
theorem sum_selected_packets {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (A : Finset (Fin N)) (W : Fin N → Fin n → Set V)
    (hsupport : ∀ k ∈ A, ∀ i p, p ∈ W k i → i ∈ S ∧ f i = k) :
    (∑ k ∈ A, ∑ i, μ (W k i)) =
      ∑ i ∈ S.filter (fun i => f i ∈ A), μ (W (f i) i) := by
  classical
  rw [← Finset.sum_fiberwise_eq_sum_filter S A f (fun i => μ (W (f i) i))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sum_supported_fibre S f (W k) k (hsupport k hk)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

end WangZahlLot.Obl.wz_coarse_grains_assembly
