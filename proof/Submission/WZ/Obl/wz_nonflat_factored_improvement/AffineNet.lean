-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.AffineNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseNet
import Submission.WZ.Obl.wz_convex_container_tube_packing

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem affine_volume_preimage (f : AffineEquiv ℝ Space Space) {J : ℝ} (hJ : 0 < J)
    (hvol : ∀ U : Set Space, volume (f '' U) = ENNReal.ofReal J * volume U)
    (U : Set Space) : volume (f ⁻¹' U) = ENNReal.ofReal J⁻¹ * volume U := by
  have he := hvol (f ⁻¹' U)
  rw [Set.image_preimage_eq _ f.surjective] at he
  rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hJ.le),
    inv_mul_cancel₀ hJ.ne', ENNReal.ofReal_one, one_mul]

/-- A fixed-volume container can hold only a bounded number of essentially distinct tubes. -/
theorem bounded_tube_fiber {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i)))
    (F : Finset (Fin n)) (U : Set Space) (hU : volume U ≤ ENNReal.ofReal (C * δ ^ 2))
    (hcontain : ∀ i ∈ F, tube δ (x i) (v i) ⊆ U) :
    (F.card : ℝ) ≤ 1000000 * C ^ 2 := by
  classical
  let g : Fin F.card → Fin n := fun i => (F.equivFin.symm i).val
  have hg : Function.Injective g := fun _ _ h => F.equivFin.symm.injective (Subtype.ext h)
  have hp := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ
    (fun i => x (g i)) (fun i => v (g i))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU) (fun i => hv (g i))
    (fun i => hcontain (g i) (F.equivFin.symm i).property)
    (fun i j hij => hover (g i) (g j) (hg.ne hij))
  have hp' : ENNReal.ofReal ((F.card : ℝ) * δ ^ 4) ≤
      ENNReal.ofReal (1000000 * (C * δ ^ 2) ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal 1000000 * (volume U) ^ 2 := hp
      _ ≤ ENNReal.ofReal 1000000 * (ENNReal.ofReal (C * δ ^ 2)) ^ 2 := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hp'
  have hd4 : 0 < δ ^ 4 := by positivity
  apply (mul_le_mul_iff_left₀ hd4).mp
  nlinarith only [hr]

/-- Select essentially distinct unit tubes around affine images of the fine tubes.
The preimage-volume hypothesis gives a constant bound for each covering fibre. -/
theorem affine_tube_net {δ ρ C : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 1000000) (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (f : AffineEquiv ℝ Space Space)
    (c : Fin n → Space) (u : Fin n → Fin 3 → Space)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hc : ∀ i, ‖c i‖ < 1 / 100)
    (hv : ∀ i, ‖v i‖ = 1)
    (hover : ∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i)))
    (hprism : ∀ i, f '' tube δ (x i) (v i) ⊆
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism ρ ρ (c i) (u i))
    (hvolume : ∀ z w : Space, ‖w‖ = 1 →
      volume (f ⁻¹' tube (4 * ρ) z w) ≤ ENNReal.ofReal (C * δ ^ 2)) :
    ∃ (M : ℕ) (j : Fin M → Fin n) (z w : Fin M → Space),
      0 < M ∧ Function.Injective j ∧ (∀ i, ‖w i‖ = 1) ∧
      (∀ i, tube (4 * ρ) (z i) (w i) ⊆ unitBall) ∧
      (∀ i i', i ≠ i' → volume (tube (4 * ρ) (z i) (w i) ∩
        tube (4 * ρ) (z i') (w i')) ≤
          (1 / 2 : ENNReal) * volume (tube (4 * ρ) (z i) (w i))) ∧
      (∀ i, f '' tube δ (x (j i)) (v (j i)) ⊆ tube (4 * ρ) (z i) (w i)) ∧
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.netConst * n ≤
        (M : ℝ) * (1000000 * C ^ 2) := by
  classical
  obtain ⟨M, k, F, hM, hk, hFI, hFne, hFdisj, hmass, hcover, hsep⟩ :=
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.net_cover Finset.univ
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)) hρ.le le_rfl hρ hρ1
      c u (fun i _ => hu i) (fun i _ => hc i)
  choose j hj using hFne
  let w : Fin M → Space := fun i =>
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.axisDir (u (k i))
  let z : Fin M → Space := fun i => c (k i) - (1 / 2 : ℝ) • w i
  have hw : ∀ i, ‖w i‖ = 1 := fun i =>
    WangZahlLot.Obl.wz_transverse_cell_weighted_cover.norm_axisDir (hu (k i))
  have hinc : ∀ i j', j' ∈ F i →
      f '' tube δ (x j') (v j') ⊆ tube (4 * ρ) (z i) (w i) :=
    fun i j' hj' => (hprism j').trans (hcover i j' hj')
  have hjinj : Function.Injective j := by
    intro i i' he
    by_contra hne
    exact Finset.disjoint_left.mp (hFdisj i i' hne) (hj i) (he ▸ hj i')
  refine ⟨M, j, z, w, hM, hjinj, hw, ?_, hsep, fun i => hinc i (j i) (hj i), ?_⟩
  · intro i
    exact WangZahlLot.Obl.wz_transverse_cell_weighted_cover.cTube_subset_ball
      hρ.le (by linarith) (hu (k i)) (hc (k i))
  · calc
      _ ≤ ∑ i, ((F i).card : ℝ) := by simpa using hmass
      _ ≤ ∑ _i : Fin M, 1000000 * C ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact bounded_tube_fiber hδ hC x v hv hover (F i) _ (hvolume (z i) (w i) (hw i))
          (fun j' hj' p hp => hinc i j' hj' ⟨p, hp, rfl⟩)
      _ = _ := by simp

end WangZahlLot.Obl.wz_nonflat_factored_improvement
