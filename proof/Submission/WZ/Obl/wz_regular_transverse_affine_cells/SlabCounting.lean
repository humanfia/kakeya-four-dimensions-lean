-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.SlabCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabExtraction
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabVolume

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set Metric
open scoped ENNReal

open Classical in
/-- Equal-size physical bodies turn the weighted slab estimate into a counting
estimate. Passing to a subfamily costs only its retained proportion. -/
lemma slab_counting_of_good {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (U P : ι → Set E) (S : SlabSpec)
    (hmax : ∀ T : SlabSpec, T.weight I U (fun i => (volume (U i)).toReal) / T.width ≤
      2 * (∑ i ∈ I, (volume (U i)).toReal) / S.width) (hJI : J ⊆ I)
    {t q w C : ℝ} (ht : 0 < t) (hq : 0 < q) (hw : 0 < w)
    (hC : 1 ≤ C) (htq : t * q ≤ 1)
    (htS : t ≤ S.width)
    (hweights : ∀ i ∈ I, w ≤ (volume (U i)).toReal ∧ (volume (U i)).toReal ≤ C * w)
    (hcard : q * (I.card : ℝ) ≤ J.card)
    (hUP : ∀ i ∈ J, U i ⊆ P i)
    (hPne : ∀ i ∈ J, (P i).Nonempty)
    (hPball : ∀ i ∈ J, P i ⊆ ball (0 : E) (1 / 100)) :
    ∀ (ν : E) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal ((J.filter fun i => P i ⊆
        ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r).card : ℝ) ≤
      ENNReal.ofReal (16 * C / (t * q) * (J.card : ℝ)) *
        volume (ball (0 : E) 1 ∩ slab (innerSL ℝ ν) s r) := by
  classical
  have hSnonneg := S.width_pos.le
  intro ν s r hν hr
  let T : SlabSpec := ⟨ν, s, r, hν, hr⟩
  let F := J.filter fun i => P i ⊆ ball (0 : E) 1 ∩ T.carrier
  change ENNReal.ofReal (F.card : ℝ) ≤ _
  have hFJ : F ⊆ J := Finset.filter_subset _ _
  have hFI : F ⊆ I := hFJ.trans hJI
  have hFslab : ∀ i ∈ F, U i ⊆ T.carrier := by
    intro i hi
    exact (hUP i (hFJ hi)).trans ((Finset.mem_filter.mp hi).2.trans inter_subset_right)
  have hweightF : (F.card : ℝ) * w ≤ T.weight I U (fun i => (volume (U i)).toReal) := by
    calc (F.card : ℝ) * w = ∑ _i ∈ F, w := by simp
      _ ≤ ∑ i ∈ F, (volume (U i)).toReal :=
        Finset.sum_le_sum fun i hi => (hweights i (hFI hi)).1
      _ = ∑ i ∈ F, if U i ⊆ T.carrier then (volume (U i)).toReal else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ite_eq_left (hFslab i hi)]
      _ ≤ T.weight I U (fun i => (volume (U i)).toReal) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hFI
        intro i _ _
        split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
  have htotal : (∑ i ∈ I, (volume (U i)).toReal) ≤ (I.card : ℝ) * (C * w) := by
    calc (∑ i ∈ I, (volume (U i)).toReal) ≤ ∑ _i ∈ I, C * w :=
        Finset.sum_le_sum fun i hi => (hweights i hi).2
      _ = _ := by simp
  have hcount : (F.card : ℝ) * (t * q) ≤ 2 * C * r * (J.card : ℝ) := by
    have hm := (div_le_iff₀ T.width_pos).mp (hmax T)
    have hm' : T.weight I U (fun i => (volume (U i)).toReal) * S.width ≤
        2 * (∑ i ∈ I, (volume (U i)).toReal) * r := by
      have he : 2 * (∑ i ∈ I, (volume (U i)).toReal) / S.width * T.width =
          (2 * (∑ i ∈ I, (volume (U i)).toReal) * r) / S.width := by
        dsimp [T]
        ring
      rw [he, le_div_iff₀ S.width_pos] at hm
      exact hm
    have hfw : (F.card : ℝ) * w * t ≤ 2 * ((I.card : ℝ) * (C * w)) * r := by
      calc (F.card : ℝ) * w * t ≤ (F.card : ℝ) * w * S.width := by gcongr
        _ ≤ T.weight I U (fun i => (volume (U i)).toReal) * S.width := by gcongr
        _ ≤ 2 * (∑ i ∈ I, (volume (U i)).toReal) * r := hm'
        _ ≤ _ := by gcongr
    have hcancel : (F.card : ℝ) * t ≤ 2 * (I.card : ℝ) * C * r := by
      apply (mul_le_mul_iff_right₀ hw).mp
      nlinarith [hfw]
    calc (F.card : ℝ) * (t * q) = ((F.card : ℝ) * t) * q := by ring
      _ ≤ (2 * (I.card : ℝ) * C * r) * q := by gcongr
      _ = 2 * C * r * (q * (I.card : ℝ)) := by ring
      _ ≤ _ := by gcongr
  rcases F.eq_empty_or_nonempty with hF | ⟨i, hi⟩
  · simp [hF]
  obtain ⟨p, hp⟩ := hPne i (hFJ hi)
  have hpnorm : ‖p‖ ≤ 1 / 100 := by
    exact le_of_lt (by simpa using hPball i (hFJ hi) hp)
  have hps : |inner ℝ ν p - s| ≤ r := ((Finset.mem_filter.mp hi).2 hp).2
  have hvol := volume_ball_inter_slab_ge hν hr hpnorm hps
  have hscalar : (F.card : ℝ) ≤ 16 * C / (t * q) * (J.card : ℝ) * (min r 1 / 8) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (mul_pos ht hq)]
    rcases le_total r 1 with hr1 | hr1
    · rw [min_eq_left hr1]
      nlinarith [hcount]
    · rw [min_eq_right hr1]
      have hsub : (F.card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_le_card hFJ
      have hJ : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left htq (Nat.cast_nonneg F.card)]
  calc ENNReal.ofReal (F.card : ℝ)
      ≤ ENNReal.ofReal (16 * C / (t * q) * (J.card : ℝ) * (min r 1 / 8)) :=
        ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal (16 * C / (t * q) * (J.card : ℝ)) * ENNReal.ofReal (min r 1 / 8) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul_right hvol _

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
