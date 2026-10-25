-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CommonCutMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CommonCutMass.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported fine_level_of_UF)

/-- A common spatial cut retaining grain incidence mass retains fine
incidence mass, with the factor two from the uniform fibre levels. -/
theorem grain_common_cut_fine_mass {δ h ρ a c b g t : ℝ} (ht : 0 ≤ t)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m)
    {B : Set V} (hB : MeasurableSet B)
    (hretain : O t * ∑ j, μ (Hg j) ≤ ∑ j, μ (Hg j ∩ B)) :
    O (t / 2) * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ B) := by
  have hZsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hfib : ∀ k, assignedFiber γ Hg k = assignedFiber f Z k := by
    intro k
    rw [assignedFiber_eq_supported f hZsupport k]
    exact hG.2.2.2.2.2.2.1 k
  obtain ⟨m', hm', hlevel⟩ := fine_level_of_UF hZsupport ⟨m, hG.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨-, hmass, -⟩ := grain_refinement_transfer_full f γ Z Hg
    (fun j => Hg j ∩ B) hm' ht (fun i => (hC.1 i).1)
    (fun j => (hG.2.2.2.2.1 j).1) (fun j => (hG.2.2.2.2.1 j).1.inter hB)
    (fun _ => inter_subset_left) hG.2.2.2.2.2.1 hfib hlevel hretain
  apply hmass.trans
  apply Finset.sum_le_sum
  intro i _
  apply measure_mono
  rintro p ⟨hp, j, hj, hpj⟩
  exact ⟨hp, hpj.2⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
