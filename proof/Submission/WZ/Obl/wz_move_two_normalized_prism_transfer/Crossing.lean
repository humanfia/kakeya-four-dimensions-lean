-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Crossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Unions

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

open Set MeasureTheory

/-- The union of all pieces on a fine tube. -/
def pieceUnion {n L : ℕ} (W : Fin n → Fin L → Set V) (i : Fin n) : Set V := ⋃ j, W i j

/-- Assigned pieces have exactly the same fibre and grain unions. -/
theorem pieceUnion_fibre_cover {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {S : Finset (Fin n)}
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j) (k : Fin N) :
    {p | ∃ j, γ j = k ∧ p ∈ pieceSupport W j} =
      {p | ∃ i ∈ S, f i = k ∧ p ∈ pieceUnion W i} := by
  ext p
  constructor
  · rintro ⟨j, hj, hp⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    have ha := hassign i j ⟨p, hi⟩
    exact ⟨i, ha.1, ha.2.trans hj, Set.mem_iUnion.mpr ⟨j, hi⟩⟩
  · rintro ⟨i, hiS, hi, hp⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (hassign i j ⟨p, hj⟩).2.symm.trans hi,
      Set.mem_iUnion.mpr ⟨i, hj⟩⟩

/-- An incidence meeting a grain of its assigned fibre belongs to that same prism. -/
lemma pieceUnion_meets_support {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N}
    (hassign : ∀ i j, (W i j).Nonempty → f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    {i : Fin n} {j : Fin L} (hij : f i = γ j)
    (hmeet : (pieceUnion W i ∩ pieceSupport W j).Nonempty) : (W i j).Nonempty := by
  obtain ⟨p, hp, hpj⟩ := hmeet
  obtain ⟨j', hp'⟩ := Set.mem_iUnion.mp hp
  obtain ⟨i', hpi'⟩ := Set.mem_iUnion.mp hpj
  have he : j' = j := active_piece_unique hdisj
    ((hassign i j' ⟨p, hp'⟩).symm.trans hij) hp' hpi'
  exact ⟨p, he ▸ hp'⟩

/-- The additional avoidance condition that makes the direct union obey frozen crossing.
The disjointness of the supports alone gives the nonempty piece, but not this inclusion. -/
theorem pieceUnion_crossing {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {U : Fin L → Set V}
    (hassign : ∀ i j, (W i j).Nonempty → f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (havoid : ∀ i j j', j ≠ j' → γ j = γ j' → (W i j).Nonempty →
      Disjoint (W i j') (U j))
    {i : Fin n} {j : Fin L} (hij : f i = γ j)
    (hmeet : (pieceUnion W i ∩ pieceSupport W j).Nonempty) :
    pieceUnion W i ∩ U j ⊆ pieceSupport W j := by
  have hne := pieceUnion_meets_support hassign hdisj hij hmeet
  rintro p ⟨hp, hpU⟩
  obtain ⟨j', hp'⟩ := Set.mem_iUnion.mp hp
  by_cases he : j = j'
  · exact Set.mem_iUnion.mpr ⟨i, he.symm ▸ hp'⟩
  · have hγ : γ j = γ j' := hij.symm.trans (hassign i j' ⟨p, hp'⟩)
    exact False.elim (Set.disjoint_left.mp (havoid i j j' he hγ hne) hp' hpU)

/-- Assignment identifies the fibre union with the union of the original prism pieces. -/
lemma pieceUnion_fibre_eq {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {S : Finset (Fin n)}
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j)
    (k : Fin N) (p : V) (i : Fin n) :
    (i ∈ S ∧ f i = k ∧ p ∈ pieceUnion W i) ↔ p ∈ pieceFibre W γ k i := by
  constructor
  · rintro ⟨hiS, hi, hp⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (hassign i j ⟨p, hj⟩).2.symm.trans hi, hj⟩
  · rintro ⟨j, hj, hp⟩
    have ha := hassign i j ⟨p, hp⟩
    exact ⟨ha.1, ha.2.trans hj, Set.mem_iUnion.mpr ⟨j, hp⟩⟩

/-- A common multiplicity interval on the separate prism supports is unchanged
when the assigned pieces are united inside each coarse fibre. -/
theorem pieceUnion_multiplicity {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {S : Finset (Fin n)} {m : ℝ}
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hmult : ∀ j p, p ∈ pieceSupport W j →
      q n {i | p ∈ W i j} ∈ Set.Icc m (2 * m)) :
    ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ pieceUnion W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ pieceUnion W i} ∈ Set.Icc m (2 * m) := by
  intro k p hp
  have hp' : p ∈ {p | ∃ i ∈ S, f i = k ∧ p ∈ pieceUnion W i} := hp
  rw [← pieceUnion_fibre_cover hassign k] at hp'
  obtain ⟨j, hj, hpj⟩ := hp'
  have he : {i | i ∈ S ∧ f i = k ∧ p ∈ pieceUnion W i} = {i | p ∈ W i j} := by
    ext i
    exact (pieceUnion_fibre_eq hassign k p i).trans (pieceFibre_eq_at hdisj hj hpj i)
  rw [he]
  exact hmult j p hpj

/-- Assigned stage-2 pieces give the frozen broadness predicate, with no exponent loss. -/
theorem pieceUnion_broad {n L N : ℕ} {W : Fin n → Fin L → Set V}
    {γ : Fin L → Fin N} {f : Fin n → Fin N} {S : Finset (Fin n)}
    {v : Fin n → V} {ω ζ δ h ρ : ℝ}
    (hassign : ∀ i j, (W i j).Nonempty → i ∈ S ∧ f i = γ j)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (pieceSupport W j) (pieceSupport W j'))
    (hbr : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i j}) :
    Broad ω ζ δ h ρ n N v S (pieceUnion W) f := by
  intro k p u r hu hdr hrρ
  have he := pieceUnion_fibre_eq hassign k p
  simpa only [← and_assoc, he] using
    pieceFibre_broad hdisj hbr k p u r hu hdr hrρ

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
