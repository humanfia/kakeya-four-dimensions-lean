-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseCount

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable section

abbrev coarseContraction : ℝ := 1 / 100000000
abbrev coarseRadius (b : ℝ) : ℝ := 4 * (3 * coarseContraction * b)

/-- A separated coarse cover with one distinct original prism assigned to every tube.
The loss in the number of prisms is measured by the original convex count. -/
theorem coarse_prism_net {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hL : 0 ≤ L) {q : ℕ} (hq : 0 < q) (e : Fin q → AffineIsometryEquiv ℝ Space Space)
    (hmeet : ∀ j, (e j '' standardPrism a b ∩ unitBall).Nonempty)
    (hcount : PrismCount a b L (fun j => e j '' standardPrism a b)) :
    ∃ (M : ℕ) (j : Fin M → Fin q) (z w : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i, tube (coarseRadius b) (z i) (w i) ⊆ unitBall) ∧
      (∀ i i', i ≠ i' → volume (tube (coarseRadius b) (z i) (w i) ∩
        tube (coarseRadius b) (z i') (w i')) ≤
          (1 / 2 : ENNReal) * volume (tube (coarseRadius b) (z i) (w i))) ∧
      (∀ i, (fun p : Space => coarseContraction • p) ''
        thickening (2 * b) (e (j i) '' standardPrism a b) ⊆
          tube (coarseRadius b) (z i) (w i)) ∧
      ConvexCount (coarseRadius b)
        ((coarseRadius b) ^ 2 / (a * b) * L * coarseContraction⁻¹ ^ 3) z w ∧
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * q ≤
        (M : ℝ) * (56 * ((coarseRadius b) ^ 2 / (a * b) * L * coarseContraction⁻¹ ^ 3)) := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hκ : 0 < coarseContraction := by norm_num
  have hκmax : coarseContraction ≤ 1 / 100000000 := le_rfl
  let c : Fin q → Space := fun i => coarseContraction • e i 0
  let u : Fin q → Fin 3 → Space := fun i => prismFrame (e i)
  have hu : ∀ i, Orthonormal ℝ (u i) := fun i => prismFrame_orthonormal (e i)
  have hc : ∀ i, ‖c i‖ < 1 / 100 := by
    intro i
    have hi := prism_center_norm_lt (hab.trans hb1) hb1 (e i) (hmeet i)
    dsimp [c]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    dsimp [coarseContraction]
    linarith
  obtain ⟨M, k, F, hM, hk, hFI, hFne, hFdisj, hmass, hcover, hsep⟩ :=
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.net_cover Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hq))
      (by positivity : 0 ≤ 3 * coarseContraction * b) le_rfl
      (by positivity : 0 < 3 * coarseContraction * b)
      (by dsimp [coarseContraction]; linarith)
      c u (fun i _ => hu i) (fun i _ => hc i)
  choose j hj using hFne
  let w : Fin M → Space := fun i =>
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.axisDir (u (k i))
  let z : Fin M → Space := fun i => c (k i) - (1 / 2 : ℝ) • w i
  have hw : ∀ i, ‖w i‖ = 1 := fun i =>
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.norm_axisDir (hu (k i))
  have hbig : ∀ i j', j' ∈ F i →
      (fun p : Space => coarseContraction • p) '' thickening (2 * b)
        (e j' '' standardPrism a b) ⊆ tube (coarseRadius b) (z i) (w i) := by
    intro i j' hj'
    exact (normalized_prism_neighborhood_subset hab hb1 hκ.le hκmax (e j')).trans
      (hcover i j' hj')
  have hinc : ∀ i j', j' ∈ F i →
      (fun p : Space => coarseContraction • p) '' (e j' '' standardPrism a b) ⊆
        tube (coarseRadius b) (z i) (w i) := by
    intro i j' hj'
    exact (Set.image_mono (self_subset_thickening (by positivity) _)).trans (hbig i j' hj')
  have hjinj : Function.Injective j := by
    intro i i' he
    by_contra hne
    exact Finset.disjoint_left.mp (hFdisj i i' hne) (hj i) (he ▸ hj i')
  have hr0 : 0 ≤ coarseRadius b := by dsimp [coarseRadius]; positivity
  have hr1 : coarseRadius b ≤ 1 := by dsimp [coarseRadius, coarseContraction]; linarith
  have hbound : ∀ i, ((F i).card : ℝ) ≤
      56 * ((coarseRadius b) ^ 2 / (a * b) * L * coarseContraction⁻¹ ^ 3) := by
    intro i
    exact prism_fiber_bound ha hb hκ hL hr0 hr1 hcount (F i) (z i) (w i) (hw i) (hinc i)
  refine ⟨M, j, z, w, hM, hjinj, hw, ?_, hsep, fun i => hbig i (j i) (hj i),
    prismCount_to_coarse ha hb hκ hL hcount j hjinj z w (fun i => hinc i (j i) (hj i)), ?_⟩
  · intro i
    exact WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube_subset_ball
      (by positivity) (by dsimp [coarseContraction]; linarith) (hu (k i)) (hc (k i))
  · calc
      _ ≤ ∑ i, ((F i).card : ℝ) := by simpa using hmass
      _ ≤ ∑ _i : Fin M,
          56 * ((coarseRadius b) ^ 2 / (a * b) * L * coarseContraction⁻¹ ^ 3) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = _ := by simp

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
