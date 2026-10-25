-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AxisShiftCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShift
import Submission.WZ.Obl.wz_multiscale_finite_tower.CountComparison
import Submission.WZ.Obl.wz_multiscale_finite_tower.RepresentativeSlabs
import Submission.WZ.Obl.wz_multiscale_finite_tower.Counts
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ParentSlabs

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (doubled ConvexCount SlabBound convexExpansionLoss centered_segment centered_doubled_segment)

lemma slabBound_restrict {n : ℕ} {D : Set Space} {U : Fin n → Set Space}
    {P Q : Fin n → Prop} {L L' : ℝ} (hQP : ∀ i, Q i → P i)
    (hL : L * {i | P i}.ncard ≤ L' * {i | Q i}.ncard)
    (h : SlabBound D L P U) : SlabBound D L' Q U := by
  intro u t r hu hr
  have hc : {i | Q i ∧ U i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard ≤
      {i | P i ∧ U i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard :=
    Set.ncard_mono (fun i hi => ⟨hQP i hi.1, hi.2⟩)
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    ((h u t r hu hr).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl))

lemma slabBound_comp {n m : ℕ} {D : Set Space} {U : Fin n → Set Space} {L L' : ℝ}
    (h : SlabBound D L (fun _ : Fin n => True) U) (g : Fin m → Fin n)
    (hg : Function.Injective g) (hL : L * n ≤ L' * m) :
    SlabBound D L' (fun _ : Fin m => True) (U ∘ g) := by
  intro u t r hu hr
  have hc := count_comp_le g hg (fun i => U i ⊆ D ∩ {p | |inner ℝ u p - t| ≤ r})
  have hh := h u t r hu hr
  simp only [SlabBound, true_and, Set.ofPred_true, Set.ncard_univ, Nat.card_fin,
    Function.comp_apply] at hh ⊢
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hc)) le_rfl).trans
    (hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hL) le_rfl))

lemma longitudinal_shift_expansion {d a : ℝ} (hd : 0 < d) (ha : |a| ≤ 1 / 2)
    (x v : Space) : Tube d x v ⊆
      AffineMap.homothety (axisMidpoint (x + a • v) v) (2 : ℝ) '' Tube d (x + a • v) v := by
  apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.homothety_image_of_contraction _
    (by norm_num : (2 : ℝ) ≠ 0)
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.homothety_mem_tube
    (A := t - a - 1 / 2) (B := d)
  · rw [abs_le]
    constructor <;> nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2, ht.1, ht.2]
  · have he : p - (x + a • v + (1 / 2 : ℝ) • v) - (t - a - 1 / 2) • v =
        p - (x + t • v) := by module
    rw [he]
    exact hpt.le
  · norm_num
    linarith

theorem KatzTao.longitudinal_shift {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    {n : ℕ} {x v : Fin n → Space} (hK : KatzTao d L n x v) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 1 / 2)
    (hball : ∀ i, Tube d (x i + a i • v i) (v i) ⊆ ball 0 1) :
    KatzTao d (L * convexExpansionLoss 2) n (fun i => x i + a i • v i) v := by
  have hh := convex_count_of_expansions (r := d) (s := d) (A := 1) (C := 2) (L := L)
    (by norm_num) (by norm_num) hL (by simp) (fun _ : Fin n => True)
    (fun i => Tube d (x i + a i • v i) (v i)) (fun i => Tube d (x i) (v i))
    (fun i => axisMidpoint (x i + a i • v i) (v i))
    (fun _ _ => isOpen_thickening) (fun i _ => hball i)
    (fun i _ => self_subset_thickening hd _ (by
      simpa only [axisMidpoint, zero_smul, add_zero] using
        centered_segment (x i + a i • v i) (v i) (a := 0) (by norm_num)))
    (fun i _ => longitudinal_shift_expansion hd (ha i) _ _)
    (by simpa only [ConvexCount, KatzTao, true_and] using hK)
  simpa only [ConvexCount, KatzTao, true_and, one_mul] using hh

lemma centered_root_contains_ball (u : Space) : ball (0 : Space) 1 ⊆ Tube 1 (- (1 / 2 : ℝ) • u) u := by
  apply ball_subset_thickening
  convert centered_segment (- (1 / 2 : ℝ) • u) u (a := 0) (by norm_num) using 1 <;> module

lemma centered_doubled_root_contains_ball (u : Space) :
    ball (0 : Space) 1 ⊆ doubled 1 (- (1 / 2 : ℝ) • u) u := by
  have hz : (0 : Space) ∈ segment ℝ
      (- (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u)
      (- (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u + 2 • u) := by
    convert centered_doubled_segment (- (1 / 2 : ℝ) • u) u (a := 0) (by norm_num) using 1 <;> module
  exact (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2 * 1)).trans (ball_subset_thickening hz _)

/-- The initial Frostman bound survives inward shifts as a relative bound in
the fixed centered root. -/
theorem Frostman.longitudinal_root_shift {d L : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    {n : ℕ} {x v : Fin n → Space} (hF : Frostman d L n x v)
    (hball : ∀ i, Tube d (x i) (v i) ⊆ ball 0 1)
    (a : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1 / 2)
    (hnew : ∀ i, Tube d (x i + a i • v i) (v i) ⊆ ball 0 1)
    (u : Space) (hu : ‖u‖ = 1) :
    SlabBound (doubled 1 (- (1 / 2 : ℝ) • u) u) (512000000 * L)
      (fun _ : Fin n => True) (fun i => Tube d (x i + a i • v i) (v i)) := by
  let D := doubled 1 (- (1 / 2 : ℝ) • u) u
  have hBD : ball (0 : Space) 1 ⊆ D := centered_doubled_root_contains_ball u
  have hvol : volume D ≤ ENNReal.ofReal 256 := by
    simpa only [D, one_pow, mul_one] using doubled_volume_upper (by norm_num : (0 : ℝ) ≤ 1)
      le_rfl (- (1 / 2 : ℝ) • u) u hu
  have hrel : SlabBound D (256 * L) (fun _ : Fin n => True) (fun i => Tube d (x i) (v i)) := by
    have hh := hF.relative hball hBD (by norm_num : (0 : ℝ) ≤ 256) hvol le_rfl
    simpa only [SlabBound, WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slab, true_and,
      Set.ofPred_true, Set.ncard_univ, Nat.card_fin] using hh
  have hp (i : Fin n) : axisMidpoint (x i + a i • v i) (v i) ∈ Tube d (x i + a i • v i) (v i) := by
    apply self_subset_thickening hd
    simpa only [axisMidpoint, zero_smul, add_zero] using
      centered_segment (x i + a i • v i) (v i) (a := 0) (by norm_num)
  have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_of_comparable
    (D := D) (E := D) (a := 1 / 100) (B := 1) (C := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun i => axisMidpoint (x i + a i • v i) (v i))
    (fun i _ => hp i) (fun i _ => (hball i).trans hBD)
    (fun i _ => longitudinal_shift_expansion hd (ha i) _ _)
    (fun i _ => WangZahlLot.Obl.wz_rescaled_fibre_alternatives.parent_buffer
      (by norm_num : (0 : ℝ) < 1) (by norm_num : |(1 / 100 : ℝ)| ≤ 1 / 100)
      (centered_root_contains_ball u (hnew i (hp i))))
    (fun i _ => WangZahlLot.Obl.wz_rescaled_fibre_alternatives.parent_buffer
      (by norm_num : (0 : ℝ) < 1) (by norm_num : |(-(1 / 100) : ℝ)| ≤ 1 / 100)
      (centered_root_contains_ball u (hnew i (hp i))))
    (by simp) hrel
  have he : (1 : ℝ) * (2 / (1 / 100) ^ 3) * (256 * L) = 512000000 * L := by ring
  rw [he] at hh
  exact hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
