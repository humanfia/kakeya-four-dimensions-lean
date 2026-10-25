-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.IncidenceRebase.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/IncidenceRebase.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/IncidenceRebase.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CapsBridge
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Monotone

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData G_iff_data)

/-- A prism witness constructed on a retained input shading is also a
witness on the original shading. Only the retained-mass exponent is added;
the dimensions, incidence pieces, auxiliary tubes, and stage are unchanged. -/
theorem incidence_data_rebase {ω ζ δ h h' t ρ c : ℝ} {n o : ℕ}
    {x v : Fin n → V} {Y Y' : Fin n → Set V} (D : PrismData n)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) (hgap : h + t ≤ h')
    (hY : ∀ i, Y' i ⊆ Y i)
    (hretain : O (δ ^ t) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i))
    (H : D.Valid ω ζ δ h ρ c x v Y' o) :
    D.Valid ω ζ δ h' ρ c x v Y o := by
  have hmass := H.2.2.2.2.2.1
  have H' := D.valid_mono hδ hδ1 (by linarith : h ≤ h') le_rfl H
  obtain ⟨ha, hab, hbc, hc, hW, _, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩ := H'
  refine ⟨ha, hab, hbc, hc, ?_, ?_, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩
  · intro i j
    refine ⟨(hW i j).1, ?_, (hW i j).2.2⟩
    exact fun p hp => ⟨hY i ((hW i j).2.1 hp).1, ((hW i j).2.1 hp).2⟩
  · calc
      O (δ ^ h') * ∑ i, μ (Y i) ≤ O (δ ^ (h + t)) * ∑ i, μ (Y i) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hgap)) le_rfl
      _ = O (δ ^ h) * (O (δ ^ t) * ∑ i, μ (Y i)) := by
        rw [Real.rpow_add hδ]
        dsimp only [O]
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h), mul_assoc]
      _ ≤ O (δ ^ h) * ∑ i, μ (Y' i) := mul_le_mul' le_rfl hretain
      _ ≤ _ := hmass

/-- Restore the original input shading after any retained refinement in
an earlier part of the construction. This works at every prism stage. -/
theorem incidence_prisms_rebase {ω ζ δ h h' t ρ c : ℝ} {n o : ℕ}
    {x v : Fin n → V} {Y Y' : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) (hgap : h + t ≤ h')
    (hY : ∀ i, Y' i ⊆ Y i)
    (hretain : O (δ ^ t) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i))
    (H : WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h ρ c n x v Y' o) :
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ c n x v Y o := by
  obtain ⟨D, HD⟩ := G_iff_data.mp H
  exact G_iff_data.mpr ⟨D, incidence_data_rebase D hδ hδ1 ht hgap hY hretain HD⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
