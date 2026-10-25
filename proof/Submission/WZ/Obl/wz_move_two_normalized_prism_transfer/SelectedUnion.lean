-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.SelectedUnion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Unions

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory

/-- The union associated to a selected coarse assignment retains exactly the selected
fibre mass and all pointwise broadness. Empty fine shadings are excluded from `S`. -/
theorem selected_fibre_union {n L N : ℕ} {δ h ρ ω ζ : ℝ}
    {W : Fin n → Fin L → Set V} {Y : Fin n → Set V} {γ : Fin L → Fin N}
    {x v : Fin n → V} {y w : Fin N → V} (Q : Finset (Fin N)) (f : Fin n → Fin N)
    (hfQ : ∀ i, f i ∈ Q)
    (hassign : ∀ i j, γ j ∈ Q → (W i j).Nonempty → f i = γ j)
    (hW : ∀ i j, MeasurableSet (W i j) ∧ W i j ⊆ Y i)
    (hcont : ∀ i j, (W i j).Nonempty → T δ (x i) (v i) ⊆ T ρ (y (γ j)) (w (γ j)))
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hbr : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i j}) :
    ∃ (S : Finset (Fin n)) (Z : Fin n → Set V),
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅)) ∧
      (∀ i, i ∈ S ↔ (Z i).Nonempty) ∧
      (∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
      (∑ i ∈ S, μ (Z i)) = ∑ k ∈ Q, ∑ i, μ (pieceFibre W γ k i) ∧
      Broad ω ζ δ h ρ n N v S Z f ∧
      (∀ i j, γ j ∈ Q → W i j ⊆ Z i) ∧
      (∀ i p, p ∈ Z i → ∃ j, γ j ∈ Q ∧ γ j = f i ∧ p ∈ W i j) := by
  classical
  let Z (i : Fin n) : Set V := pieceFibre W γ (f i) i
  let S := Finset.univ.filter (fun i => (Z i).Nonempty)
  have hSmem (i : Fin n) : i ∈ S ↔ (Z i).Nonempty := by simp [S]
  have hZempty (i : Fin n) (hi : i ∉ S) : Z i = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (fun h => hi ((hSmem i).mpr h))
  have hmem (i : Fin n) (k : Fin N) (hk : k ∈ Q) {p : V}
      (hp : p ∈ pieceFibre W γ k i) : f i = k := by
    obtain ⟨j, hj, hpj⟩ := hp
    exact (hassign i j (hj ▸ hk) ⟨p, hpj⟩).trans hj
  have hzero (i : Fin n) (k : Fin N) (hk : k ∈ Q) (hne : k ≠ f i) :
      pieceFibre W γ k i = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hne (hmem i k hk hp).symm
  have hsum : (∑ i ∈ S, μ (Z i)) = ∑ k ∈ Q, ∑ i, μ (pieceFibre W γ k i) := by
    rw [Finset.sum_comm]
    have hall : (∑ i ∈ S, μ (Z i)) = ∑ i, μ (Z i) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp only [hZempty i hi, μ, measure_empty]
    rw [hall]
    apply Finset.sum_congr rfl
    intro i _
    symm
    apply Finset.sum_eq_single (f i)
    · intro k hk hne
      simp only [hzero i k hk hne, μ, measure_empty]
    · exact fun hi => (hi (hfQ i)).elim
  have hset (k : Fin N) (hk : k ∈ Q) (p : V) :
      ∀ i, (i ∈ S ∧ f i = k ∧ p ∈ Z i) ↔ p ∈ pieceFibre W γ k i := by
    intro i
    constructor
    · rintro ⟨_, hik, hp⟩
      simpa only [Z, hik] using hp
    · intro hp
      have hik := hmem i k hk hp
      have hpZ : p ∈ Z i := by simpa only [Z, hik] using hp
      exact ⟨(hSmem i).mpr ⟨p, hpZ⟩, hik, hpZ⟩
  refine ⟨S, Z, ?_, hSmem, ?_, hsum, ?_, ?_, ?_⟩
  · intro i
    refine ⟨pieceFibre_measurable W γ (fun i j => (hW i j).1) (f i) i, ?_, hZempty i⟩
    rintro p ⟨j, hj, hp⟩
    exact (hW i j).2 hp
  · intro i hi
    obtain ⟨p, j, hj, hp⟩ := (hSmem i).mp hi
    simpa only [hj] using hcont i j ⟨p, hp⟩
  · intro k p u r hu hdr hrρ
    by_cases hk : k ∈ Q
    · have he := hset k hk p
      have hcaps : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} =
          {i | p ∈ pieceFibre W γ k i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
        ext i
        simpa only [Set.mem_ofPred_eq, ← and_assoc] using and_congr_left (fun _ => he i)
      have hall : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} = {i | p ∈ pieceFibre W γ k i} := by
        ext i
        exact he i
      change q n _ ≤ δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n _
      rw [hcaps, hall]
      exact pieceFibre_broad hdisj hbr k p u r hu hdr hrρ
    · have hn : ∀ i, f i ≠ k := fun i he => hk (he ▸ hfQ i)
      change q n _ ≤ δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n _
      simp only [hn, false_and, and_false, Set.ofPred_false, q, Set.ncard_empty,
        Nat.cast_zero, mul_zero, le_refl]
  · intro i j hj p hp
    exact ⟨j, (hassign i j hj ⟨p, hp⟩).symm, hp⟩
  · rintro i p ⟨j, hj, hp⟩
    exact ⟨j, hj ▸ hfQ i, hj, hp⟩

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
