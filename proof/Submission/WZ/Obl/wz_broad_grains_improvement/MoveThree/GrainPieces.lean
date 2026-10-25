-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainPieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainPieces.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported measurable_assignedFiber fine_level_of_UF)

noncomputable section

/-- Lift one labelled part of each old grain to its original fine tubes.
The old coarse assignment specifies which fine incidences belong to a grain. -/
def fineGrainPiece {n N L K : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set V) (B : Fin L → Fin K → Set V) (i : Fin n) (l : Fin K) : Set V :=
  Z i ∩ assignedFiber γ (fun j => B j l) (f i)

/-- Every retained old grain carries between `m` and `2m` fine incidences.
This comparison remains true separately for each new label, even when
different old coarse fibres overlap. -/
theorem fineGrainPiece_count_bounds {δ h ρ a c b g : ℝ}
    {n N L K : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (hsupport : ∀ i, i ∉ S → Z i = ∅)
    (B : Fin L → Fin K → Set V) (hsub : ∀ j l, B j l ⊆ Hg j)
    (l : Fin K) (p : V) :
    m * q L {j | p ∈ B j l} ≤ q n {i | p ∈ fineGrainPiece f γ Z B i l} ∧
      q n {i | p ∈ fineGrainPiece f γ Z B i l} ≤ 2 * m * q L {j | p ∈ B j l} := by
  open WangZahlLot.Obl.wz_clustered_cover_volume_gain in
  have hbound : ∀ k p, p ∈ assignedFiber γ (fun j => B j l) k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    rintro k p ⟨j, hj, hp⟩
    rw [← supported_fine_count f hsupport]
    exact hG.2.2.2.2.2.2.2.2.1 k p (hG.2.2.2.2.2.2.1 k |>.subset
      ⟨j, hj, hsub j l hp⟩)
  have hd (j j' : Fin L) (hne : j ≠ j') (hγ : γ j = γ j') :
      Disjoint (B j l) (B j' l) :=
    (hG.2.2.2.2.2.1 j j' hne hγ).mono (hsub j l) (hsub j' l)
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.restrict_fiber_count_bounds
    f Z (assignedFiber γ (fun j => B j l)) hbound p
  rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount_assignedFiber γ
    (fun j => B j l) hd p] at hh
  exact hh

/-- A disjoint labelled refinement of the old grains yields fine-indexed
components with the same labels. It loses at most a factor two in incidence
mass and keeps the old-scale broadness in every labelled component. -/
theorem labelled_grain_refinement {ω ζ δ h ρ a c b g t : ℝ}
    {n N L K : ℕ} {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    (hZm : ∀ i, MeasurableSet (Z i)) (hsupport : ∀ i, i ∉ S → Z i = ∅)
    (hbroad : Broad ω ζ δ h ρ n N v S Z f)
    (B : Fin L → Fin K → Set V) (hBm : ∀ j l, MeasurableSet (B j l))
    (hsub : ∀ j l, B j l ⊆ Hg j)
    (hBdisj : ∀ j l l', l ≠ l' → Disjoint (B j l) (B j l'))
    (ht : 0 ≤ t) (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j, ∑ l, μ (B j l)) :
    (∀ i l, MeasurableSet (fineGrainPiece f γ Z B i l) ∧ fineGrainPiece f γ Z B i l ⊆ Z i) ∧
    (∀ i l l', l ≠ l' → Disjoint (fineGrainPiece f γ Z B i l) (fineGrainPiece f γ Z B i l')) ∧
    O (t / 2) * ∑ i, μ (Z i) ≤ ∑ i, ∑ l, μ (fineGrainPiece f γ Z B i l) ∧
    ∀ l, Broad ω ζ δ h ρ n N v S (fun i => fineGrainPiece f γ Z B i l) f := by
  obtain ⟨_, _, _, _, hgeom, hdisj, hfibre, _, hlevel, _, _, _⟩ := hG
  have hWm (i : Fin n) (l : Fin K) : MeasurableSet (fineGrainPiece f γ Z B i l) :=
    (hZm i).inter (measurable_assignedFiber γ (fun j => hBm j l) (f i))
  have hWdisj (i : Fin n) (l l' : Fin K) (hne : l ≠ l') :
      Disjoint (fineGrainPiece f γ Z B i l) (fineGrainPiece f γ Z B i l') := by
    apply Set.disjoint_left.mpr
    rintro p ⟨_, j, hj, hp⟩ ⟨_, j', hj', hp'⟩
    have he : j = j' := by
      by_contra hh
      exact Set.disjoint_left.mp (hdisj j j' hh (hj.trans hj'.symm))
        (hsub j l hp) (hsub j' l' hp')
    subst j'
    exact Set.disjoint_left.mp (hBdisj j l l' hne) hp hp'
  refine ⟨fun i l => ⟨hWm i l, inter_subset_left⟩, hWdisj, ?_, ?_⟩
  · let H' (j : Fin L) : Set V := ⋃ l, B j l
    have hH'm (j : Fin L) : MeasurableSet (H' j) := MeasurableSet.iUnion (hBm j)
    have hH'sub (j : Fin L) : H' j ⊆ Hg j := iUnion_subset (hsub j)
    have hH'mass (j : Fin L) : μ (H' j) = ∑ l, μ (B j l) := by
      simpa only [H', μ, tsum_fintype] using measure_iUnion (hBdisj j) (hBm j)
    have hretain' : O t * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j) := by
      simpa only [hH'mass] using hretain
    have hfib (k : Fin N) : assignedFiber γ Hg k = assignedFiber f Z k := by
      rw [assignedFiber_eq_supported f hsupport]
      exact hfibre k
    obtain ⟨m', hm', hlevel'⟩ := fine_level_of_UF hsupport ⟨m, hlevel⟩
    obtain ⟨_, hmass, _⟩ := grain_refinement_transfer_full f γ Z Hg H' hm' ht
      hZm (fun j => (hgeom j).1) hH'm hH'sub hdisj hfib hlevel' hretain'
    apply hmass.trans_eq
    apply Finset.sum_congr rfl
    intro i _
    have he : Z i ∩ assignedFiber γ H' (f i) = ⋃ l, fineGrainPiece f γ Z B i l := by
      ext p
      simp only [fineGrainPiece, assignedFiber, H', mem_inter_iff, mem_iUnion,
        mem_ofPred_eq]
      aesop
    change μ (Z i ∩ assignedFiber γ H' (f i)) = _
    rw [he]
    simpa only [μ, tsum_fintype] using measure_iUnion (hWdisj i) (hWm i)
  · intro l
    exact broad_restrict_fibres (fun k => assignedFiber γ (fun j => B j l) k) hbroad

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
