-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.DenseCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/DenseCut.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainBounds
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainMass
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DenseGrains

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber assignedFiber_eq_supported fine_level_of_UF fiberBodyCount
   fiberBodyCount_eq_ncard common_cut_dense_grains frozen_prism_volume)

noncomputable section

/-- A common fine cut followed by removal of sparse grain shadings preserves
the exact frozen state. Every nonempty output grain is individually dense. -/
theorem dense_grain_state_of_common_cut {ω ζ δ h h' ρ a c g t D : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 < t) (hD : 0 ≤ D)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (cut : Fin N → Set V) (hcut : ∀ k, MeasurableSet (cut k))
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ cut (f i)))
    (hDsmall : D ≤ t / 4 * δ ^ h)
    (hbudget : O (δ ^ h') ≤ O (t / 8) * O (δ ^ h)) :
    ∃ H' : Fin L → Set V,
      (∀ j, MeasurableSet (H' j) ∧ H' j ⊆ Hg j ∩ cut (γ j)) ∧
      O (t / 4) * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j) ∧
      (∀ j, H' j ≠ ∅ → O D * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (H' j)) ∧
      C δ h' n x v Y S (fun i => Z i ∩ assignedFiber γ H' (f i)) ρ N y w f True ∧
      Broad ω ζ δ h' ρ n N v S (fun i => Z i ∩ assignedFiber γ H' (f i)) f ∧
      GrainWitnesses δ h' n x v S (fun i => Z i ∩ assignedFiber γ H' (f i))
        ρ N y w f a c 0 g L z e H' γ m := by
  have ha : 0 ≤ a := hδ.le.trans hG.1
  have hrc : 0 ≤ ρ * c := ha.trans hG.2.1
  have hc : 0 ≤ c := hrc.trans hG.2.2.1
  have hgeom := hG.2.2.2.2.1
  have hZsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hfib : ∀ k, assignedFiber γ Hg k = assignedFiber f Z k := by
    intro k
    rw [assignedFiber_eq_supported f hZsupport k]
    exact hG.2.2.2.2.2.2.1 k
  obtain ⟨m', hm', hlevel⟩ := fine_level_of_UF hZsupport ⟨m, hG.2.2.2.2.2.2.2.2.1⟩
  have hm'pos : 0 < m' := by
    obtain ⟨i, hi, p, hp⟩ := cover_has_shaded_point hδ hA hC
    have hupper := (hlevel (f i) p ⟨i, rfl, hp⟩).2
    have hcount : 0 < fiberBodyCount f Z (f i) p := by
      rw [fiberBodyCount_eq_ncard]
      exact Nat.cast_pos.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, rfl, hp⟩)
    linarith
  have hfin : (∑ j, μ (Hg j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => (grain_real_weights hδ hG).1 j)
  have hcost : (∑ j, O D * μ (P a (ρ * c) c (z j) (e j))) ≤
      O (t / 4) * ∑ j, μ (Hg j) := by
    calc
      _ = O (D * L * a * (ρ * c) * c) := by
        simp only [μ, frozen_prism_volume ha hrc hc, O,
          ← ENNReal.ofReal_mul hD, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg L)]
        congr 1
        ring
      _ ≤ O ((t / 4 * δ ^ h) * L * a * (ρ * c) * c) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr
      _ = O (t / 4) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ t / 4)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
  obtain ⟨H', hH', hmass, hdense⟩ := common_cut_dense_grains f γ Z Hg
    (fun j => P a (ρ * c) c (z j) (e j)) cut hm'pos ht.le
    (fun i => (hC.1 i).1) (fun j => (hgeom j).1) hcut hfin
    hG.2.2.2.2.2.1 hfib hlevel hretain hcost
  have hbudget' : O (δ ^ h') ≤ O (t / 4) * O (δ ^ h) :=
    hbudget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
  have hdensity : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j) := by
    calc
      _ = O (δ ^ h') * O (L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ (O (t / 4) * O (δ ^ h)) * O (L * a * (ρ * c) * c) :=
        mul_le_mul' hbudget' le_rfl
      _ = O (t / 4) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 2
        ring
      _ ≤ O (t / 4) * ∑ j, μ (Hg j) := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
      _ ≤ _ := hmass
  exact ⟨H', hH', hmass, hdense,
    cover_of_grain_refinement hδ hδ1 hh (by positivity : 0 ≤ t / 4)
      hC hG (fun j => (hH' j).1) (fun j => (hH' j).2.trans inter_subset_left) hmass
      (by simpa only [show t / 4 / 2 = t / 8 by ring] using hbudget),
    Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB),
    grainWitnesses_of_refinement hG (fun j => (hH' j).1)
      (fun j => (hH' j).2.trans inter_subset_left) hdensity⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
