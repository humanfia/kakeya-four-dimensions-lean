-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.RegularRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Assembly
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.PrismData
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- Keeping whole coarse fibres preserves the density, multiplicity and crossing
conditions needed by the grains output. Only the occupied prism labels are kept. -/
theorem grains_on_selected_fibres {ω ζ δ h ρ c m : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (D : PrismData ω ζ δ h ρ c n x v Y)
    {S : Finset (Fin n)} {f : Fin n → Fin D.N}
    (hassign : ∀ i j, (D.W i j).Nonempty → i ∈ S ∧ f i = D.γ j)
    (hmult : ∀ j p, p ∈ pieceSupport D.W j →
      q n {i | p ∈ D.W i j} ∈ Set.Icc m (2 * m))
    (havoid : ∀ i j j', j ≠ j' → D.γ j = D.γ j' → (D.W i j).Nonempty →
      Disjoint (D.W i j') (P D.a (ρ * c) c (D.z j) (D.e j)))
    (Q : Finset (Fin D.N)) (hQ : Q.Nonempty) :
    ∃ g : ℝ, 0 < g ∧
      H δ h n x v (S.filter (fun i => f i ∈ Q))
        (fun i => if f i ∈ Q then pieceUnion D.W i else ∅)
        ρ Q.card (D.y ∘ WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q)
        (D.w ∘ WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q)
        (WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ f) D.a c 0 g := by
  classical
  let J := Finset.univ.filter (fun j => D.γ j ∈ Q)
  let fj := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx J
  let fk := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q
  let γ' := fun j => WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ D.γ (fj j)
  let f' := WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ f
  let W' := fun i j => D.W i (fj j)
  let S' := S.filter (fun i => f i ∈ Q)
  have hfj (j : Fin J.card) : D.γ (fj j) ∈ Q :=
    (Finset.mem_filter.mp (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem J j)).2
  have hγ' (j : Fin J.card) : fk (γ' j) = D.γ (fj j) :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_rFib Q hQ D.γ (hfj j)
  have hassign' : ∀ i j, (W' i j).Nonempty → i ∈ S' ∧ f' i = γ' j := by
    intro i j hne
    obtain ⟨hiS, hiγ⟩ := hassign i (fj j) hne
    have hiQ : f i ∈ Q := hiγ ▸ hfj j
    refine ⟨Finset.mem_filter.mpr ⟨hiS, hiQ⟩, ?_⟩
    apply WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q
    change fk (f' i) = fk (γ' j)
    rw [hγ']
    exact (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_rFib Q hQ f hiQ).trans hiγ
  have hdisj' : ∀ j j', j ≠ j' → γ' j = γ' j' →
      Disjoint (pieceSupport W' j) (pieceSupport W' j') := by
    intro j j' hne he
    apply D.disjoint (fj j) (fj j')
      (fun hh => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J hh))
    simpa only [hγ'] using congrArg fk he
  have hZeq : (fun i => if f i ∈ Q then pieceUnion D.W i else ∅) = pieceUnion W' := by
    funext i
    ext p
    by_cases hiQ : f i ∈ Q
    · simp only [hiQ, ite_true]
      constructor
      · intro hp
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
        have hjQ : D.γ j ∈ Q := (hassign i j ⟨p, hpj⟩).2 ▸ hiQ
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjQ⟩
        refine Set.mem_iUnion.mpr ⟨J.equivFin ⟨j, hjJ⟩, ?_⟩
        simpa only [W', fj, WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx,
          Equiv.symm_apply_apply] using hpj
      · intro hp
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
        exact Set.mem_iUnion.mpr ⟨fj j, hpj⟩
    · simp only [hiQ, ite_false, Set.mem_empty_iff_false, false_iff]
      intro hp
      obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hp
      exact hiQ ((hassign i (fj j) ⟨p, hpj⟩).2.symm ▸ hfj j)
  have havoid' : ∀ i j j', j ≠ j' → γ' j = γ' j' → (W' i j).Nonempty →
      Disjoint (W' i j') (P D.a (ρ * c) c ((D.z ∘ fj) j) ((D.e ∘ fj) j)) := by
    intro i j j' hne he hW
    apply havoid i (fj j) (fj j')
      (fun hh => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J hh)) _ hW
    simpa only [hγ'] using congrArg fk he
  obtain ⟨g, hg, hH⟩ := grains_of_separated_pieces (m := m)
    (W := W') (S := S') (γ := γ') (f := f')
    (y := D.y ∘ fk) (w := D.w ∘ fk) (z := D.z ∘ fj) (e := D.e ∘ fj)
    hδ D.lower D.middle D.upper D.length
    (fun i j => ⟨(D.pieces i (fj j)).1, fun p hp => ((D.pieces i (fj j)).2.1 hp).2⟩)
    (fun j => by simpa only [Function.comp_apply, hγ'] using D.geometry (fj j))
    hassign' hdisj' (fun j => D.dense (fj j))
    (pieceUnion_multiplicity hassign' hdisj' (fun j p hp => hmult (fj j) p hp))
    (fun i j hne => (D.crossing i (fj j) hne).2) havoid'
  refine ⟨g, hg, ?_⟩
  rw [hZeq]
  exact hH

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
