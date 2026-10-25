-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.RescaleCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Defs
import Submission.WZ.Obl.wz_nsp_convex_test_family

/-!
# Homothetic hulls of convex sets

For a bounded convex set `W` with nonempty interior and `lam ≥ 1`, the convex set
`lam W - (lam - 1) W` contains every homothetic copy `c + lam (W - c)`, `c ∈ W`, and its volume
is at most a fixed multiple of `lam ^ 3` times the volume of `W` (max-volume simplex).
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

open WangZahlLot.Obl.wz_nsp_convex_test_family in
/-- The affine map attached to the standard quadruple is the identity. -/
private lemma rcnt_aff_id : ∃ Q : Fin 4 → Space, ∀ y, aff Q y = y := by
  refine ⟨![0, EuclideanSpace.single 0 1, EuclideanSpace.single 1 1,
    EuclideanSpace.single 2 1], fun y => ?_⟩
  ext i
  fin_cases i <;> simp [aff, linPart_apply]

open WangZahlLot.Obl.wz_nsp_convex_test_family in
/-- `aff Q` commutes with homotheties. -/
private lemma rcnt_aff_homothety (Q : Fin 4 → Space) (lam : ℝ) (y y' : Space) :
    aff Q y + lam • (aff Q y' - aff Q y) = aff Q (y + lam • (y' - y)) := by
  simp only [aff, map_add, map_smul, map_sub]
  abel_nf

private lemma rcnt_norm_homothety {lam : ℝ} (hlam : 1 ≤ lam) {y y' : Space} (hy : ‖y‖ ≤ 6)
    (hy' : ‖y'‖ ≤ 6) : ‖y + lam • (y' - y)‖ ≤ lam * 12 := by
  have h : y + lam • (y' - y) = lam • y' - (lam - 1) • y := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h]
  calc ‖lam • y' - (lam - 1) • y‖ ≤ ‖lam • y'‖ + ‖(lam - 1) • y‖ := norm_sub_le _ _
    _ = lam * ‖y'‖ + (lam - 1) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg (by linarith)]
    _ ≤ lam * 6 + (lam - 1) * 6 := by gcongr
    _ ≤ lam * 12 := by linarith

open WangZahlLot.Obl.wz_nsp_convex_test_family in
private lemma rcnt_hull_of_cover (Q : Fin 4 → Space) {W : Set Space} {lam : ℝ} (hlam : 1 ≤ lam)
    (hWQ : W ⊆ aff Q '' refBox) :
    Convex ℝ (aff Q '' closedBall 0 (lam * 12)) ∧
    (∀ c ∈ W, ∀ p ∈ W, c + lam • (p - c) ∈ aff Q '' closedBall 0 (lam * 12)) ∧
    volume (aff Q '' closedBall 0 (lam * 12)) =
      ENNReal.ofReal (lam ^ 3) * (volume (closedBall (0 : Space) 12) / volume refBox) *
        volume (aff Q '' refBox) := by
  refine ⟨convex_aff_image Q (convex_closedBall _ _), ?_, ?_⟩
  · intro c hc p hp
    obtain ⟨yc, hyc, rfl⟩ := hWQ hc
    obtain ⟨yp, hyp, rfl⟩ := hWQ hp
    refine ⟨yc + lam • (yp - yc), ?_, (rcnt_aff_homothety Q lam yc yp).symm⟩
    rw [mem_closedBall_zero_iff]
    exact rcnt_norm_homothety hlam (mem_closedBall_zero_iff.1 (refBox_subset_closedBall hyc))
      (mem_closedBall_zero_iff.1 (refBox_subset_closedBall hyp))
  · rw [volume_aff_image, volume_aff_image,
      Measure.addHaar_closedBall_mul volume (0 : Space) (by linarith) (by norm_num)]
    simp only [finrank_euclideanSpace_fin]
    have h1 : volume refBox ≠ 0 :=
      (lt_of_lt_of_le refSimplex_volume_pos (measure_mono refSimplex_subset_refBox)).ne'
    calc ENNReal.ofReal |LinearMap.det (linPart Q)| *
          (ENNReal.ofReal (lam ^ 3) * volume (closedBall (0 : Space) 12))
        = ENNReal.ofReal (lam ^ 3) * (volume (closedBall (0 : Space) 12) / volume refBox *
            volume refBox) * ENNReal.ofReal |LinearMap.det (linPart Q)| := by
          rw [ENNReal.div_mul_cancel h1 refBox_volume_ne_top]; ring
      _ = _ := by ring

open WangZahlLot.Obl.wz_nsp_convex_test_family in
private lemma rcnt_cover {W : Set Space} (hW : Convex ℝ W) (hW2 : W ⊆ ball 0 2) {c : Space}
    {r : ℝ} (hr : 0 < r) (hc : ball c r ⊆ W) :
    ∃ Q : Fin 4 → Space, W ⊆ aff Q '' refBox ∧
      volume (aff Q '' refBox) ≤ volume refBox / volume refSimplex * volume W := by
  obtain ⟨z, hsub, hvol⟩ := core hr (Nat.le_ceil (16 / r)) hW hW2 hc
  set P : Fin 4 → Space := fun j => gridIdx ⌈16 / r⌉₊ (r / 8) (z j) with hP
  by_cases h0 : volume (aff P '' refBox) = 0
  · have ht : testSet P = refBox := by simp [testSet, h0]
    rw [ht] at hsub hvol
    obtain ⟨Q0, hQ0⟩ := rcnt_aff_id
    have hid : aff Q0 '' refBox = refBox := by
      rw [show aff Q0 = id from funext hQ0, Set.image_id]
    refine ⟨Q0, ?_, ?_⟩
    · rw [hid]; exact hsub
    · rw [hid]; exact hvol
  · have ht : testSet P = aff P '' refBox := by simp [testSet, h0]
    rw [ht] at hsub hvol
    exact ⟨P, hsub, hvol⟩

open WangZahlLot.Obl.wz_nsp_convex_test_family in
/-- The constant of `homothety_hull`. -/
private noncomputable def rcntK : ℝ :=
  max 1 ((volume (closedBall (0 : Space) 12) / volume refBox *
    (volume refBox / volume refSimplex)).toReal)

private lemma rcnt_one_le_K : 1 ≤ rcntK := le_max_left _ _

open WangZahlLot.Obl.wz_nsp_convex_test_family in
private lemma rcnt_const_le (lam : ℝ) :
    ENNReal.ofReal (lam ^ 3) * (volume (closedBall (0 : Space) 12) / volume refBox *
      (volume refBox / volume refSimplex)) ≤ ENNReal.ofReal (rcntK * lam ^ 3) := by
  have hne : volume (closedBall (0 : Space) 12) / volume refBox *
      (volume refBox / volume refSimplex) ≠ ⊤ := by
    have h1 : volume refBox ≠ 0 :=
      (lt_of_lt_of_le refSimplex_volume_pos (measure_mono refSimplex_subset_refBox)).ne'
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top measure_closedBall_lt_top.ne h1)
      (ENNReal.div_ne_top refBox_volume_ne_top refSimplex_volume_pos.ne')
  rw [ENNReal.ofReal_mul (zero_le_one.trans rcnt_one_le_K), mul_comm]
  gcongr
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

theorem homothety_hull : ∃ K : ℝ, 1 ≤ K ∧ ∀ (W : Set Space) (lam : ℝ), Convex ℝ W →
    W ⊆ ball 0 2 → (∃ (c : Space) (r : ℝ), 0 < r ∧ ball c r ⊆ W) → 1 ≤ lam →
    ∃ W' : Set Space, Convex ℝ W' ∧ (∀ c ∈ W, ∀ p ∈ W, c + lam • (p - c) ∈ W') ∧
      volume W' ≤ ENNReal.ofReal (K * lam ^ 3) * volume W := by
  refine ⟨rcntK, rcnt_one_le_K, ?_⟩
  rintro W lam hW hW2 ⟨c, r, hr, hc⟩ hlam
  obtain ⟨Q, hWQ, hQvol⟩ := rcnt_cover hW hW2 hr hc
  obtain ⟨hconv, hmem, hvol⟩ := rcnt_hull_of_cover Q hlam hWQ
  refine ⟨_, hconv, hmem, ?_⟩
  rw [hvol]
  calc _ ≤ ENNReal.ofReal (lam ^ 3) * (volume (closedBall (0 : Space) 12) /
          volume WangZahlLot.Obl.wz_nsp_convex_test_family.refBox) *
        (volume WangZahlLot.Obl.wz_nsp_convex_test_family.refBox /
          volume WangZahlLot.Obl.wz_nsp_convex_test_family.refSimplex * volume W) := by
        gcongr
    _ = ENNReal.ofReal (lam ^ 3) * (volume (closedBall (0 : Space) 12) /
          volume WangZahlLot.Obl.wz_nsp_convex_test_family.refBox *
        (volume WangZahlLot.Obl.wz_nsp_convex_test_family.refBox /
          volume WangZahlLot.Obl.wz_nsp_convex_test_family.refSimplex)) * volume W := by
        ring
    _ ≤ ENNReal.ofReal (rcntK * lam ^ 3) * volume W := by
        gcongr
        exact rcnt_const_le lam


end WangZahlLot.Obl.wz_grains_nonsingular_slices
