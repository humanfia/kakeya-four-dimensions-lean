-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.StemSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.OneSidedCrossing
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Quantiles
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.TubeRegularity
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume

/-! Selecting a substantial stem piece inside one of the crossed grains. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory Metric
open scoped ENNReal

lemma axial_strip_volume_le {d R : ℝ} {x v : V} (hd : 0 < d) (hR : 0 ≤ R)
    (hv : ‖v‖ = 1) (p : V) :
    volume (T d x v ∩ {q | |inner ℝ v (q-p)| ≤ R}) ≤
      O (128*(4*R+5*d)*d^2) := by
  have heq (q : V) : inner ℝ v (q-p) = inner ℝ v (q-x) - inner ℝ v (p-x) := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hh := wz_flat_cluster_slab_filling.tube_slice_volume_upper
    (x := x) (a := inner ℝ v (p-x)-R) hd hv (show 0 ≤ 2*R by positivity)
  calc
    _ ≤ volume (T d x v ∩ {q | inner ℝ v (p-x)-R ≤ inner ℝ v (q-x) ∧
        inner ℝ v (q-x) ≤ inner ℝ v (p-x)-R+2*R}) := by
      apply measure_mono
      rintro q ⟨hq, hr⟩
      change |inner ℝ v (q-p)| ≤ R at hr
      rw [heq, abs_le] at hr
      exact ⟨hq, by linarith [hr.1], by linarith [hr.2]⟩
    _ ≤ _ := by convert hh using 1 <;> congr 1 <;> ring

/-- A median point of a small shaded set belongs to a grain carrying one quarter
of the local mass, up to the tube-radius error. The grain assignment may be
arbitrary, provided its grain is crossed by the whole fine tube. -/
theorem exists_heavy_crossed_grain {d a b c : ℝ} {x v : V}
    (hd : 0 < d) (hc : 0 < c) (hdc : d ≤ c/100) (hab : a ≤ b) (hbc : b ≤ c)
    (hv : ‖v‖ = 1) {E : Set V} (hEm : MeasurableSet E) (hE0 : volume E ≠ 0)
    (hET : E ⊆ T d x v) (hEI : E ⊆ ball (0 : V) 1)
    (hdiam : ∀ p ∈ E, ∀ q ∈ E, dist p q ≤ c/10)
    {J : Type*} (z : J → V) (e : J → V ≃ₗᵢ[ℝ] V)
    (hcover : ∀ p ∈ E, ∃ j, p ∈ P a b c (z j) (e j) ∧
      Crosses d a b c x v (z j) (e j)) :
    ∃ j, volume.real E / 4 - 20000*d^3 ≤
      volume.real (E ∩ P a b c (z j) (e j)) := by
  have hEfin : volume E ≠ ∞ := measure_ne_top_of_subset hEI measure_ball_lt_top.ne
  obtain ⟨p, hpE, hpminus, hpplus⟩ := exists_two_sided_mass_point volume hEm hEfin hE0
    (fun q : V => inner ℝ v q) (by fun_prop) (volume_inner_level hv)
    (by norm_num : (0 : ℝ) < 1) (by
      intro q hq
      have hq1 : ‖q‖ < 1 := by simpa using hEI hq
      exact (abs_real_inner_le_norm v q).trans_lt (by simpa only [hv, one_mul] using hq1))
  obtain ⟨j, hpP, hcross⟩ := hcover p hpE
  refine ⟨j, ?_⟩
  let B : Set V := T d x v ∩ {q | |inner ℝ v (q-p)| ≤ 32*d}
  have hBT : B ⊆ T d x v := inter_subset_left
  have hBfin : volume B ≠ ∞ := measure_ne_top_of_subset hBT
    (wz_flat_cluster_slab_filling.tube_volume_ne_top d x v)
  have hBmass : volume.real B ≤ 20000*d^3 := by
    have hh := axial_strip_volume_le (x := x) hd (show 0 ≤ 32*d by positivity) hv p
    have hh' := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hh
    rw [ENNReal.toReal_ofReal (by positivity)] at hh'
    change volume.real B ≤ _
    change volume.real B ≤ _ at hh'
    nlinarith [pow_pos hd 3]
  have hPfin : volume (E ∩ P a b c (z j) (e j)) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left hEfin
  have hcoordinate (q : V) (hq : q ∈ E) : |inner ℝ v (q-p)| ≤ c/10 := by
    calc
      _ ≤ ‖v‖ * ‖q-p‖ := abs_real_inner_le_norm _ _
      _ = dist p q := by rw [hv, one_mul, ← dist_eq_norm, dist_comm]
      _ ≤ _ := hdiam p hpE q hq
  have hdiff (q : V) : inner ℝ v (q-p) = inner ℝ v q - inner ℝ v p :=
    inner_sub_right _ _ _
  rcases hcross.one_sided_subset hd hc hdc hab hbc hv (hET hpE) hpP with hplus | hminus
  · have hsub : (E ∩ {q | inner ℝ v p ≤ inner ℝ v q}) \ B ⊆
        E ∩ P a b c (z j) (e j) := by
      rintro q ⟨⟨hqE, hqside⟩, hqB⟩
      have hstrip : 32*d < |inner ℝ v (q-p)| :=
        lt_of_not_ge (fun hh => hqB ⟨hET hqE, hh⟩)
      have hnonneg : 0 ≤ inner ℝ v (q-p) := by rw [hdiff]; exact sub_nonneg.mpr hqside
      rw [abs_of_nonneg hnonneg] at hstrip
      exact ⟨hqE, hplus q (hET hqE) hstrip.le (le_abs_self _ |>.trans (hcoordinate q hqE))⟩
    have hcut := le_measureReal_sdiff (μ := volume)
      (s₁ := E ∩ {q | inner ℝ v p ≤ inner ℝ v q}) (s₂ := B) hBfin
    have hh := measureReal_mono hsub hPfin
    change volume.real E / 4 ≤ volume.real (E ∩ {q | inner ℝ v p ≤ inner ℝ v q}) at hpplus
    linarith
  · have hsub : (E ∩ {q | inner ℝ v q ≤ inner ℝ v p}) \ B ⊆
        E ∩ P a b c (z j) (e j) := by
      rintro q ⟨⟨hqE, hqside⟩, hqB⟩
      have hstrip : 32*d < |inner ℝ v (q-p)| :=
        lt_of_not_ge (fun hh => hqB ⟨hET hqE, hh⟩)
      have hnonpos : inner ℝ v (q-p) ≤ 0 := by rw [hdiff]; exact sub_nonpos.mpr hqside
      rw [abs_of_nonpos hnonpos] at hstrip
      exact ⟨hqE, hminus q (hET hqE) hstrip.le
        ((neg_le_abs _).trans (hcoordinate q hqE))⟩
    have hcut := le_measureReal_sdiff (μ := volume)
      (s₁ := E ∩ {q | inner ℝ v q ≤ inner ℝ v p}) (s₂ := B) hBfin
    have hh := measureReal_mono hsub hPfin
    change volume.real E / 4 ≤ volume.real (E ∩ {q | inner ℝ v q ≤ inner ℝ v p}) at hpminus
    linarith

/-- For a shading with density `lam`, a crossed grain captures a stem piece of
mass comparable to `lam c d²`, once the length dominates the radius error. -/
theorem exists_stem_grain {d a b c lam : ℝ} {x v : V}
    (hd : 0 < d) (hc : 0 < c) (hc1 : c ≤ 1) (hlam : 0 < lam)
    (hdc : d ≤ c/160) (hsmall : d ≤ lam*c/1000000000)
    (hab : a ≤ b) (hbc : b ≤ c) (hv : ‖v‖ = 1)
    {R : Set V} (hRm : MeasurableSet R) (hRT : R ⊆ T d x v)
    (hRI : R ⊆ ball (0 : V) 1) (hmass : O (lam*d^2) ≤ volume R)
    {J : Type*} (z : J → V) (e : J → V ≃ₗᵢ[ℝ] V)
    (hcover : ∀ p ∈ R, ∃ j, p ∈ P a b c (z j) (e j) ∧
      Crosses d a b c x v (z j) (e j)) :
    ∃ j, O (lam*c*d^2/10000) ≤ volume (R ∩ P a b c (z j) (e j)) := by
  obtain ⟨R', hR'm, hR'R, hhalf, hreg⟩ := regular_tube_shading_at_scale
    (r := c/20) (by positivity) (by linarith) (by linarith) hv hRm hRT
  have hRfin : volume R ≠ ∞ := measure_ne_top_of_subset hRI measure_ball_lt_top.ne
  have hR0 : 0 < volume R := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hmass
  have hR'0 : volume R' ≠ 0 := by
    intro he
    have hh : (1/2 : ENNReal) * volume R = 0 := le_zero_iff.mp (he ▸ hhalf)
    simp [hR0.ne'] at hh
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hR'0
  let E : Set V := R' ∩ ball p (c/20)
  have hER : E ⊆ R := inter_subset_left.trans hR'R
  have hEfin : volume E ≠ ∞ := measure_ne_top_of_subset hER hRfin
  have hElow : O (lam*c*d^2/640) ≤ volume E := by
    calc
      O (lam*c*d^2/640) = O ((c/20)/32) * O (lam*d^2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ O ((c/20)/32) * volume R := mul_le_mul_right hmass _
      _ ≤ volume E := hreg p hp
  have hE0 : volume E ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hElow)
  obtain ⟨j, hj⟩ := exists_heavy_crossed_grain hd hc (by linarith) hab hbc hv
    (hR'm.inter measurableSet_ball) hE0 (hER.trans hRT) (hER.trans hRI) (by
      intro q hq q' hq'
      calc
        dist q q' ≤ dist q p + dist p q' := dist_triangle _ _ _
        _ ≤ c/10 := by
          have hq1 : dist q p < c/20 := hq.2
          have hq2 : dist p q' < c/20 := by simpa only [mem_ball, dist_comm] using hq'.2
          linarith) z e (fun q hq => hcover q (hER hq))
  refine ⟨j, (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top_of_subset inter_subset_left hRfin)).mpr ?_⟩
  have hEreal : lam*c*d^2/640 ≤ volume.real E :=
    (ENNReal.ofReal_le_iff_le_toReal hEfin).mp hElow
  have hmono : volume.real (E ∩ P a b c (z j) (e j)) ≤
      volume.real (R ∩ P a b c (z j) (e j)) :=
    measureReal_mono (inter_subset_inter_left _ hER)
      (measure_ne_top_of_subset inter_subset_left hRfin)
  change volume.real E / 4 - 20000*d^3 ≤ volume.real (E ∩ P a b c (z j) (e j)) at hj
  have herr : 20000*d^3 ≤ lam*c*d^2/50000 := by
    have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg d)
    nlinarith
  change lam*c*d^2/10000 ≤ volume.real (R ∩ P a b c (z j) (e j))
  nlinarith [mul_pos (mul_pos hlam hc) (sq_pos_of_pos hd)]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
