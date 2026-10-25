-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NarrowState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NarrowState.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseDichotomy
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber confinementDensity coarse_grains_transverse_or_narrow
   coarseLinear coarseLinear_norm_le dualLinear boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd unit)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (enumerate enumerate_mem enumerate_surj extendSets extendSets_enumerate extendSets_outside)

noncomputable section

/-- Under a common physical ball-density upper bound, individually dense
frozen grains either force the transverse density inequality or have a
pointwise narrow refinement preserving the cover, broadness, and grains. -/
theorem density_or_narrow_grain_state {ω ζ δ h h' ρ a c g s R D lam : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h')
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ s * ρ * c)
    (hR : 0 < R) (hRs : R ≤ (s / 2) * ρ * c) (hD : 0 < D) (hlam : 0 ≤ lam)
    {n N L : ℕ} {x v : Fin n → V} {S : Finset (Fin n)}
    {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hg : Fin L → Set V}
    {γ : Fin L → Fin N} {m : ℝ}
    (hYball : ∀ i, Y i ⊆ I)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hB : Broad ω ζ δ h ρ n N v S Z f)
    (hG : GrainWitnesses δ h n x v S Z ρ N y w f a c 0 g L z e Hg γ m)
    (hdense : ∀ j, Hg j ≠ ∅ → O D * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (Hg j))
    (hupper : ∀ j p, p ∈ Hg j → μ ((⋃ i, Y i) ∩ ball p R) ≤ O (lam * R ^ 3))
    (hbudget : O (δ ^ h') ≤ O (1 / 8 : ℝ) * O (δ ^ h)) :
    confinementDensity a ρ c D s ≤ 46080 * lam ∨
    ∃ H' : Fin L → Set V,
      (∀ j, MeasurableSet (H' j) ∧ H' j ⊆ Hg j ∧ (1 / 4 : ℝ≥0∞) * μ (Hg j) ≤ μ (H' j)) ∧
      (∀ i j p, p ∈ H' i → p ∈ H' j → pd (boxAxis (e i) 0) (boxAxis (e j) 0) ≤ s) ∧
      C δ h' n x v Y S (fun i => Z i ∩ assignedFiber γ H' (f i)) ρ N y w f True ∧
      Broad ω ζ δ h' ρ n N v S (fun i => Z i ∩ assignedFiber γ H' (f i)) f ∧
      GrainWitnesses δ h' n x v S (fun i => Z i ∩ assignedFiber γ H' (f i))
        ρ N y w f a c 0 g L z e H' γ m := by
  classical
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hρ : 0 < ρ := (mul_pos_iff_of_pos_right hc).mp hrc
  have hρ1 : ρ ≤ 1 := by nlinarith [hG.2.2.1]
  have haxis : ∀ j, ‖coarseLinear 1 (boxAxis (e j) 2)‖ ≤ 43 := by
    intro j
    have hh := coarseLinear_norm_le (by norm_num : (0 : ℝ) < 1) le_rfl (boxAxis (e j) 2)
    norm_num only [inv_one, boxAxis_norm, one_mul] at hh
    exact hh.trans (by norm_num)
  have hHU : ∀ j, Hg j ⊆ ⋃ i, Y i := by
    intro j p hp
    have hpG : p ∈ {p | ∃ j', γ j' = γ j ∧ p ∈ Hg j'} := ⟨j, rfl, hp⟩
    obtain ⟨i, _, _, hpi⟩ := hG.2.2.2.2.2.2.1 (γ j) |>.subset hpG
    exact mem_iUnion.mpr ⟨i, (hC.1 i).2.1 hpi⟩
  have hgeom := hG.2.2.2.2.1
  let Q := Finset.univ.filter fun j => Hg j ≠ ∅
  let pick := enumerate Q
  have hpick (j : Fin Q.card) : Hg (pick j) ≠ ∅ :=
    (Finset.mem_filter.mp (enumerate_mem Q j)).2
  rcases coarse_grains_transverse_or_narrow (by norm_num : (0 : ℝ) < 1) le_rfl hρ hρ1
    ha hG.2.1 hc hs hs1 has hR hRs hD hlam (z ∘ pick) (e ∘ pick) (Hg ∘ pick)
    (⋃ j, Hg j) (⋃ i, Y i)
    (fun j => haxis (pick j)) (fun j => (hgeom (pick j)).1)
    (fun j => (hgeom (pick j)).2.1)
    (fun j => subset_iUnion Hg (pick j)) (iUnion_subset hHU)
    (iUnion_subset hYball) (fun j => hdense (pick j) (hpick j)) (by
      intro p hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp hp
      exact hupper j p hj) with hd | href
  · exact Or.inl hd
  obtain ⟨W, hW, hnarrow⟩ := href
  let H' := extendSets Q W
  have hH' : ∀ j, MeasurableSet (H' j) ∧ H' j ⊆ Hg j ∧
      (1 / 4 : ℝ≥0∞) * μ (Hg j) ≤ μ (H' j) := by
    intro j
    by_cases hj : j ∈ Q
    · obtain ⟨j', rfl⟩ := enumerate_surj Q hj
      simpa only [H', extendSets_enumerate, Function.comp_apply, pick, μ] using hW j'
    · have he : Hg j = ∅ := by simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
      simp only [H', extendSets_outside Q W hj, he, MeasurableSet.empty, subset_refl,
        measure_empty, mul_zero, le_refl, and_self]
  have hquarter : O (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by norm_num [O, ENNReal.ofReal_div_of_pos]
  have hretain : O (1 / 4 : ℝ) * ∑ j, μ (Hg j) ≤ ∑ j, μ (H' j) := by
    rw [hquarter, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => (hH' j).2.2)
  have hbudget' : O (δ ^ h') ≤ O (1 / 4 : ℝ) * O (δ ^ h) :=
    hbudget.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)) le_rfl)
  have hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (H' j) := by
    calc
      _ = O (δ ^ h') * O (L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ (O (1 / 4 : ℝ) * O (δ ^ h)) * O (L * a * (ρ * c) * c) :=
        mul_le_mul' hbudget' le_rfl
      _ = O (1 / 4 : ℝ) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 2
        ring
      _ ≤ O (1 / 4 : ℝ) * ∑ j, μ (Hg j) := mul_le_mul' le_rfl hG.2.2.2.2.2.2.2.1
      _ ≤ _ := hretain
  refine Or.inr ⟨H', hH', ?_,
    cover_of_grain_refinement hδ hδ1 hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hC hG (fun j => (hH' j).1) (fun j => (hH' j).2.1) hretain (by
        simpa only [show (1 / 4 : ℝ) / 2 = 1 / 8 by norm_num] using hbudget),
    Broad_mono hδ hδ1 hh (broad_restrict_fibres _ hB),
    grainWitnesses_of_refinement hG (fun j => (hH' j).1) (fun j => (hH' j).2.1) hmass⟩
  have hdual (p : V) : dualLinear 1 p = p := by
    ext i
    fin_cases i <;> simp [dualLinear, WangZahlLot.Obl.wz_flat_factored_improvement.diagonalMap_apply]
  intro i j p hi hj
  have hiQ : i ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Set.Nonempty.ne_empty ⟨p, (hH' i).2.1 hi⟩⟩
  have hjQ : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Set.Nonempty.ne_empty ⟨p, (hH' j).2.1 hj⟩⟩
  obtain ⟨i', rfl⟩ := enumerate_surj Q hiQ
  obtain ⟨j', rfl⟩ := enumerate_surj Q hjQ
  have hi' : p ∈ W i' := by simpa only [H', extendSets_enumerate] using hi
  have hj' : p ∈ W j' := by simpa only [H', extendSets_enumerate] using hj
  simpa only [hdual, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.unit,
    boxAxis_norm, inv_one, one_smul, Function.comp_apply] using hnarrow i' j' p hi' hj'

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
