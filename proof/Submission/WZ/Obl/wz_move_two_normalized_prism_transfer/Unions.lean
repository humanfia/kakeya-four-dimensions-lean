-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Unions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Defs

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory

/-- The support of one incidence prism. -/
def pieceSupport {n L : ℕ} (W : Fin n → Fin L → Set V) (j : Fin L) : Set V :=
  ⋃ i, W i j

/-- All incidence pieces in one coarse fibre, before assigning the fine tubes. -/
def pieceFibre {n L N : ℕ} (W : Fin n → Fin L → Set V) (γ : Fin L → Fin N)
    (k : Fin N) (i : Fin n) : Set V :=
  {p | ∃ j, γ j = k ∧ p ∈ W i j}

lemma pieceFibre_measurable {n L N : ℕ} (W : Fin n → Fin L → Set V)
    (γ : Fin L → Fin N) (hW : ∀ i j, MeasurableSet (W i j)) (k : Fin N) (i : Fin n) :
    MeasurableSet (pieceFibre W γ k i) := by
  have he : pieceFibre W γ k i = ⋃ j, ⋃ (_ : γ j = k), W i j := by
    ext p
    simp [pieceFibre]
  rw [he]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hW i j

/-- Within a coarse tube, two pieces present at the same point have the same prism label. -/
lemma active_piece_unique {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N}
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    {j j' : Fin L} {i i' : Fin n} {p : V}
    (hγ : γ j = γ j') (hi : p ∈ W i j) (hi' : p ∈ W i' j') : j = j' := by
  by_contra hne
  exact Set.disjoint_left.mp (hdisj j j' hne hγ)
    (Set.mem_iUnion.mpr ⟨i, hi⟩) (Set.mem_iUnion.mpr ⟨i', hi'⟩)

/-- One active prism describes the whole fibre incidence set at that point. -/
lemma pieceFibre_eq_at {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N}
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    {k : Fin N} {j : Fin L} {p : V}
    (hγ : γ j = k) (hp : p ∈ pieceSupport W j) :
    ∀ i, p ∈ pieceFibre W γ k i ↔ p ∈ W i j := by
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hp
  intro i
  constructor
  · rintro ⟨j', hj', hi⟩
    have he := active_piece_unique hdisj (hj'.trans hγ.symm) hi hi₀
    simpa only [he] using hi
  · intro hi
    exact ⟨j, hγ, hi⟩

/-- The stage-2 fibre union preserves the full per-prism broadness estimate. -/
theorem pieceFibre_broad {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {v : Fin n → V} {δ h ρ β : ℝ}
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hbr : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ β * q n {i | p ∈ W i j}) :
    ∀ k (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ pieceFibre W γ k i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ β * q n {i | p ∈ pieceFibre W γ k i} := by
  intro k p u r hu hdr hrρ
  by_cases hp : ∃ i, p ∈ pieceFibre W γ k i
  · obtain ⟨i₀, j, hj, hi⟩ := hp
    have he := pieceFibre_eq_at hdisj hj (Set.mem_iUnion.mpr ⟨i₀, hi⟩)
    simpa only [he] using hbr j p u r hu hdr hrρ
  · have he : ∀ i, p ∉ pieceFibre W γ k i := fun i hi => hp ⟨i, hi⟩
    simp only [he, false_and, Set.ofPred_false, q, Set.ncard_empty, Nat.cast_zero, mul_zero,
      le_refl]

/-- Summing the per-prism incidence masses equals summing the fibre masses. -/
theorem pieceFibre_mass {n L N : ℕ} (W : Fin n → Fin L → Set V)
    (γ : Fin L → Fin N) (hW : ∀ i j, MeasurableSet (W i j))
    (hdisj : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j')) :
    (∑ k, ∑ i, μ (pieceFibre W γ k i)) = ∑ i, ∑ j, μ (W i j) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hf (k : Fin N) : pieceFibre W γ k i =
      ⋃ j ∈ (Finset.univ.filter (fun j => γ j = k)), W i j := by
    ext p
    simp [pieceFibre]
  have hm (k : Fin N) : μ (pieceFibre W γ k i) =
      ∑ j ∈ Finset.univ.filter (fun j => γ j = k), μ (W i j) := by
    rw [hf]
    exact measure_biUnion_finset (fun j _ j' _ hne => hdisj i j j' hne)
      (fun j _ => hW i j)
  simp_rw [hm]
  exact Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (γ j)) _

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
