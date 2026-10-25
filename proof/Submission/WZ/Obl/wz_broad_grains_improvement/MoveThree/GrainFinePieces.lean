-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainFinePieces.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainFinePieces.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/GrainFinePieces.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinementBroadness
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.CommonCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported measurable_assignedFiber fine_level_of_UF)

/- The finite-label mass/disjointness argument below is adapted from this
workspace's o153/x0686, GrainPieces.lean (5791eff, extended 5894e3b). Its
parent module cannot be imported here. We use this obligation's existing
grainFineRefinement and the accepted grain_refinement_transfer directly. -/

/-- A row refinement covers exactly the same spatial union after it is
lifted to the original fine incidences. In particular its density is unchanged. -/
theorem grainFineRefinement_union {δ h ρ a c b g m : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N}
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hWH : ∀ j, W j ⊆ Hs j) :
    (⋃ i, grainFineRefinement S Z f W γ i) = ⋃ j, W j := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rcases (mem_grainFineRefinement S Z f W γ i p).mp hi with ⟨_, _, j, _, hj⟩
    exact mem_iUnion.mpr ⟨j, hj⟩
  · intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    have hold : p ∈ {p | ∃ j', γ j' = γ j ∧ p ∈ Hs j'} := ⟨j, rfl, hWH j hj⟩
    rw [hHB.2.2.2.2.2.2.1] at hold
    obtain ⟨i, hi, hfi, hpi⟩ := hold
    exact mem_iUnion.mpr ⟨i, (mem_grainFineRefinement S Z f W γ i p).mpr
      ⟨hi, hpi, j, hfi.symm, hj⟩⟩

/-- Pointwise fine counts and grain counts differ by the original common
fine multiplicity, separately inside every row refinement. -/
theorem grainFineRefinement_count_bounds {δ h ρ a c b g m : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs W : Fin L → Set V} {γ : Fin L → Fin N}
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hsupport : ∀ i, i ∉ S → Z i = ∅) (hWH : ∀ j, W j ⊆ Hs j) (p : V) :
    m * q L {j | p ∈ W j} ≤ q n {i | p ∈ grainFineRefinement S Z f W γ i} ∧
    q n {i | p ∈ grainFineRefinement S Z f W γ i} ≤ 2 * m * q L {j | p ∈ W j} := by
  open WangZahlLot.Obl.wz_clustered_cover_volume_gain in
  have hbound : ∀ k p, p ∈ assignedFiber γ W k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    rintro k p ⟨j, hj, hp⟩
    rw [← supported_fine_count f hsupport]
    exact hHB.2.2.2.2.2.2.2.2.1 k p ((hHB.2.2.2.2.2.2.1 k).subset
      ⟨j, hj, hWH j hp⟩)
  have hd (j j' : Fin L) (hne : j ≠ j') (hγ : γ j = γ j') :
      Disjoint (W j) (W j') :=
    (hHB.2.2.2.2.2.1 j j' hne hγ).mono (hWH j) (hWH j')
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.restrict_fiber_count_bounds
    f Z (assignedFiber γ W) hbound p
  rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount_assignedFiber γ W hd p] at hh
  simpa only [grainFineRefinement_eq_assignedFiber S Z f W γ hsupport,
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, q] using hh

/-- A disjoint finite family of old-grain row refinements lifts to disjoint
fine pieces with at most a factor-two aggregate mass loss. -/
theorem labelled_grainFineRefinement {κ : Type*} [Fintype κ]
    {ω ζ δ h ρ a c b g m t : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
    {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (hHB : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hZm : ∀ i, MeasurableSet (Z i)) (hsupport : ∀ i, i ∉ S → Z i = ∅)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (W : κ → Fin L → Set V) (hWm : ∀ k j, MeasurableSet (W k j))
    (hWH : ∀ k j, W k j ⊆ Hs j)
    (hWdisj : ∀ j, Pairwise fun k k' => Disjoint (W k j) (W k' j))
    (ht : 0 ≤ t) (hretain : O t * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W k j)) :
    (∀ k i, MeasurableSet (grainFineRefinement S Z f (W k) γ i) ∧
      grainFineRefinement S Z f (W k) γ i ⊆ Z i) ∧
    (∀ i, Pairwise fun k k' => Disjoint
      (grainFineRefinement S Z f (W k) γ i) (grainFineRefinement S Z f (W k') γ i)) ∧
    O (t / 2) * ∑ i, μ (Z i) ≤ ∑ k, ∑ i, μ (grainFineRefinement S Z f (W k) γ i) ∧
    (∀ k, Broad ω ζ δ h ρ n N v S (grainFineRefinement S Z f (W k) γ) f) ∧
    ∀ k, (⋃ i, grainFineRefinement S Z f (W k) γ i) = ⋃ j, W k j := by
  classical
  have href (k : κ) (i : Fin n) :=
    grainFineRefinement_eq_assignedFiber S Z f (W k) γ hsupport i
  have hBm (k : κ) (i : Fin n) : MeasurableSet (grainFineRefinement S Z f (W k) γ i) := by
    rw [href]
    exact (hZm i).inter (measurable_assignedFiber γ (hWm k) (f i))
  have hBdisj (i : Fin n) : Pairwise fun k k' => Disjoint
      (grainFineRefinement S Z f (W k) γ i) (grainFineRefinement S Z f (W k') γ i) := by
    intro k k' hne
    rw [href, href]
    apply Set.disjoint_left.mpr
    rintro p ⟨_, j, hj, hp⟩ ⟨_, j', hj', hp'⟩
    have he : j = j' := by
      by_contra hh
      exact Set.disjoint_left.mp (hHB.2.2.2.2.2.1 j j' hh (hj.trans hj'.symm))
        (hWH k j hp) (hWH k' j' hp')
    subst j'
    exact Set.disjoint_left.mp (hWdisj j hne) hp hp'
  refine ⟨fun k i => ⟨hBm k i, by rw [href]; exact inter_subset_left⟩,
    hBdisj, ?_, ?_, fun k => grainFineRefinement_union hHB (hWH k)⟩
  · let H' (j : Fin L) : Set V := ⋃ k, W k j
    have hH'm (j : Fin L) : MeasurableSet (H' j) := MeasurableSet.iUnion fun k => hWm k j
    have hH'sub (j : Fin L) : H' j ⊆ Hs j := iUnion_subset fun k => hWH k j
    have hH'mass (j : Fin L) : μ (H' j) = ∑ k, μ (W k j) := by
      simpa only [H', μ, tsum_fintype] using measure_iUnion (hWdisj j) (fun k => hWm k j)
    have hretain' : O t * ∑ j, μ (Hs j) ≤ ∑ j, μ (H' j) := by
      simp_rw [hH'mass]
      rw [Finset.sum_comm]
      exact hretain
    have hfib (k : Fin N) : assignedFiber γ Hs k = assignedFiber f Z k := by
      rw [assignedFiber_eq_supported f hsupport]
      exact hHB.2.2.2.2.2.2.1 k
    obtain ⟨m', hm', hlevel'⟩ := fine_level_of_UF hsupport ⟨m, hHB.2.2.2.2.2.2.2.2.1⟩
    obtain ⟨Uf, hUf, hmass, hUeq⟩ :=
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_refinement_transfer f γ Z Hs H' hm' ht
        hZm (fun j => (hHB.2.2.2.2.1 j).1) hH'm hH'sub hHB.2.2.2.2.2.1
        hfib hlevel' hretain'
    apply hmass.trans
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    calc
      μ (Uf i) ≤ μ (⋃ k, grainFineRefinement S Z f (W k) γ i) := by
        apply measure_mono
        intro p hp
        have hpU : p ∈ assignedFiber γ H' (f i) := by
          rw [← hUeq]
          exact ⟨i, rfl, hp⟩
        obtain ⟨j, hj, hjp⟩ := hpU
        obtain ⟨k, hkp⟩ := mem_iUnion.mp hjp
        apply mem_iUnion.mpr
        refine ⟨k, ?_⟩
        rw [href]
        exact ⟨(hUf i).2 hp, j, hj, hkp⟩
      _ = ∑ k, μ (grainFineRefinement S Z f (W k) γ i) := by
        simpa only [μ, tsum_fintype] using measure_iUnion (hBdisj i) (fun k => hBm k i)
  · intro k
    have hf : grainFineRefinement S Z f (W k) γ =
        (fun i => Z i ∩ assignedFiber γ (W k) (f i)) := funext (href k)
    rw [hf]
    exact Clear.broad_common_cut _ hbr

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
