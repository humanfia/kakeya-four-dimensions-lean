-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.SelectedPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.GrainPacket
import Submission.WZ.Obl.wz_coarse_grains_assembly.AssembleH
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- Joining independently refined fibres and restricting their coarse
indices recovers each individual shading on its assigned fibre. -/
theorem selected_packet_membership {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (A : Finset (Fin N)) (hA : A.Nonempty) (W : Fin N → Fin n → Set V)
    (hsupport : ∀ k ∈ A, ∀ i p, p ∈ W k i → i ∈ S ∧ f i = k)
    (k : Fin A.card) (p : V) (i : Fin n) :
    (i ∈ S.filter (fun i => f i ∈ A) ∧ rFib A hA f i = k ∧
      p ∈ (if f i ∈ A then W (f i) i else ∅)) ↔ p ∈ W (rIdx A k) i := by
  classical
  constructor
  · rintro ⟨hi, hfi, hp⟩
    obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
    have he := (rFib_eq_iff A hA f hiA k).mp hfi
    rw [ite_eq_left hiA, he] at hp
    exact hp
  · intro hp
    obtain ⟨hiS, hfi⟩ := hsupport _ (rIdx_mem A k) i p hp
    have hiA : f i ∈ A := hfi ▸ rIdx_mem A k
    refine ⟨Finset.mem_filter.mpr ⟨hiS, hiA⟩, (rFib_eq_iff A hA f hiA k).mpr hfi, ?_⟩
    rw [ite_eq_left hiA, hfi]
    exact hp

/-- Common-multiplicity packets on selected coarse fibres assemble to the
frozen grains and broadness predicates after reindexing. -/
theorem assemble_selected_packets {δ h ρ c ω ζ m : ℝ} {n N : ℕ}
    {x v : Fin n → V} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (A : Finset (Fin N)) (hA : A.Nonempty) (W : Fin N → Fin n → Set V)
    (y w : Fin N → V)
    (hδ : 0 < δ) (hwidth : 16 * δ ≤ ρ * c) (hρc : ρ * c ≤ c) (hc1 : c ≤ 1)
    (hsupport : ∀ k ∈ A, ∀ i p, p ∈ W k i → i ∈ S ∧ f i = k)
    (hpacket : ∀ k ∈ A, Nonempty (GrainPacket δ h ρ c x v (W k) (y k) (w k)))
    (hmult : ∀ k ∈ A, ∀ p, (∃ i, p ∈ W k i) →
      q n {i | p ∈ W k i} ∈ Set.Icc m (2 * m))
    (hbr : ∀ k ∈ A, ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ W k i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W k i}) :
    ∃ g : ℝ, 0 < g ∧
      Broad ω ζ δ h ρ n A.card v (S.filter (fun i => f i ∈ A))
        (fun i => if f i ∈ A then W (f i) i else ∅) (rFib A hA f) ∧
      H δ h n x v (S.filter (fun i => f i ∈ A))
        (fun i => if f i ∈ A then W (f i) i else ∅) ρ A.card
        (fun k => y (rIdx A k)) (fun k => w (rIdx A k)) (rFib A hA f) (16 * δ) c 0 g := by
  classical
  let Z (i : Fin n) : Set V := if f i ∈ A then W (f i) i else ∅
  let S' := S.filter (fun i => f i ∈ A)
  have hmem := selected_packet_membership S f A hA W hsupport
  have hset (k : Fin A.card) (p : V) :
      {i | i ∈ S' ∧ rFib A hA f i = k ∧ p ∈ Z i} = {i | p ∈ W (rIdx A k) i} := by
    ext i
    exact hmem k p i
  have hunion (k : Fin A.card) :
      {p | ∃ i ∈ S', rFib A hA f i = k ∧ p ∈ Z i} = {p | ∃ i, p ∈ W (rIdx A k) i} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    exact exists_congr (fun i => hmem k p i)
  have hdiag (k : Fin A.card) (i : Fin n) (hi : i ∈ S') (hfi : rFib A hA f i = k) :
      Z i = W (rIdx A k) i := by
    have hiA := (Finset.mem_filter.mp hi).2
    have he := (rFib_eq_iff A hA f hiA k).mp hfi
    dsimp only [Z]
    rw [ite_eq_left hiA, he]
  have hBroad : Broad ω ζ δ h ρ n A.card v S' Z (rFib A hA f) := by
    intro k p u r hu hdr hrρ
    have hcap : {i | i ∈ S' ∧ rFib A hA f i = k ∧ p ∈ Z i ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} =
        {i | p ∈ W (rIdx A k) i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
      ext i
      change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _)
      constructor
      · rintro ⟨hi, hfi, hp, hangle⟩
        exact ⟨(hmem k p i).mp ⟨hi, hfi, hp⟩, hangle⟩
      · rintro ⟨hp, hangle⟩
        obtain ⟨hi, hfi, hp⟩ := (hmem k p i).mpr hp
        exact ⟨hi, hfi, hp, hangle⟩
    rw [hcap, hset]
    exact hbr _ (rIdx_mem A k) p u r hu hdr hrρ
  obtain ⟨g, hg, hH⟩ := assemble_H (x := x) (v := v) (S := S') (Z := Z)
    (y := fun k => y (rIdx A k)) (w := fun k => w (rIdx A k)) (f := rFib A hA f)
    (m := m) hδ hwidth hρc hc1 (by
      intro k
      obtain ⟨D⟩ := hpacket _ (rIdx_mem A k)
      refine ⟨D.L, D.center, D.frame, D.shading, D.geometry, D.disjoint,
        D.cover.trans (hunion k).symm, D.density, ?_, ?_⟩
      · intro p hp
        rw [hset]
        apply hmult _ (rIdx_mem A k) p
        change p ∈ {p | ∃ i, p ∈ W (rIdx A k) i}
        rw [← hunion k]
        exact hp
      · intro i hi hfi j hne
        rw [hdiag k i hi hfi] at hne ⊢
        exact D.crossing i j hne)
  exact ⟨g, hg, hBroad, hH⟩

end WangZahlLot.Obl.wz_coarse_grains_assembly
