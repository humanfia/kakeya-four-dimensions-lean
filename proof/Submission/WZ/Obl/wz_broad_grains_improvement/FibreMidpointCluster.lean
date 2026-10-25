-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.FibreMidpointCluster.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.ScalarAlignment
import Submission.WZ.Obl.wz_multiscale_finite_tower.PowerErrors
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShiftCounts
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (weighted_fintype_color axisMidpoint slabBound_comp exists_scale_cutoff
    power_coefficient_bound inverse_power_error_bound density_power_bound)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (Fibre convexCount_subfamily convexCount_mono slabBound_mono tube_midpoints_close)
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective sum_enumerate)

set_option maxHeartbeats 800000

/-- A bounded weighted point family has a fixed-fraction subfamily of diameter
at most 1/100. The constant is independent of the finite family. -/
theorem bounded_points_weighted_cluster : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α : Type} [DecidableEq α] (U : Finset α) (p : α → V),
      (∀ i, ‖p i‖ ≤ 3) → ∀ w : α → ENNReal, 0 < ∑ i∈U,w i →
    ∃ S : Finset α, S ⊆ U ∧ S.Nonempty ∧
      (∑ i∈U,w i) ≤ O C*(∑ i∈S,w i) ∧
      ∀ i∈S, ∀ j∈S, ‖p i-p j‖ ≤ 1/100 := by
  classical
  obtain ⟨F,_,_,hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      (isCompact_closedBall (0:V) 3).totallyBounded (by norm_num : (0:ℝ)<1/200)
  refine ⟨(F.card:ℝ)+1,by linarith [Nat.cast_nonneg (α := ℝ) F.card],?_⟩
  intro α _ U p hp w hw
  have hex (i : α) : ∃ z∈F, ‖p i-z‖ ≤ 1/200 := by
    have hh := hcover (show p i∈closedBall (0:V) 3 by simpa only [mem_closedBall,dist_zero_right] using hp i)
    obtain ⟨z,hz,hiz⟩ := mem_iUnion₂.mp hh
    exact ⟨z,hz,by simpa only [mem_closedBall,dist_eq_norm] using hiz⟩
  have hU : U.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty,lt_self_iff_false] at hw
  obtain ⟨i₀,hi₀⟩ := hU
  obtain ⟨z₀,hz₀,_⟩ := hex i₀
  letI : Nonempty F := ⟨⟨z₀,hz₀⟩⟩
  let col : α → F := fun i => ⟨(hex i).choose,(hex i).choose_spec.1⟩
  obtain ⟨z,hz⟩ := weighted_fintype_color U col w
  let S := U.filter fun i => col i=z
  have hs : (∑ i∈U,w i) ≤ O ((F.card:ℝ)+1)*(∑ i∈S,w i) := by
    apply hz.trans
    apply mul_le_mul' _ le_rfl
    simp only [Fintype.card_coe]
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hS : S.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty,mul_zero] at hs
    exact (not_lt_of_ge hs) hw
  refine ⟨S,Finset.filter_subset _ _,hS,hs,?_⟩
  have hnear (i : α) (hi : i∈S) : ‖p i-z.val‖ ≤ 1/200 := by
    have he : (col i).val=z.val := congrArg Subtype.val (Finset.mem_filter.mp hi).2
    rw [← he]
    exact (hex i).choose_spec.2
  intro i hi j hj
  have hh := norm_sub_le_norm_sub_add_norm_sub (p i) z.val (p j)
  rw [norm_sub_rev z.val (p j)] at hh
  linarith [hnear i hi,hnear j hj]

/-- A physical fibre admits a midpoint cluster with normalized density and
counting bounds. Only a fixed spatial localization is used; its cost becomes
an arbitrarily small power of the scale ratio. -/
theorem fibre_midpoint_cluster {θ : ℝ} (hθ : 0<θ) :
    ∃ η₀ c : ℝ, 0<η₀ ∧ η₀≤θ ∧ 0<c ∧ c≤1 ∧
      ∀ η r s : ℝ, 0<η → η≤η₀ → 0<s → s≤c*r → r≤1 →
      ∀ y w : V, ‖w‖=1 → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      Fibre r s η y w x v Y →
    ∃ (m : ℕ) (j : Fin m → Fin n), Function.Injective j ∧ m≤n ∧
      Fibre r s θ y w (x ∘ j) (v ∘ j) (Y ∘ j) ∧
      (s/r)^θ*n ≤ (m:ℝ) ∧ O ((s/r)^θ)*(∑ i,μ (Y i)) ≤ ∑ i,μ (Y (j i)) ∧
      ∀ i j', ‖axisMidpoint (x (j i)) (v (j i))-axisMidpoint (x (j j')) (v (j j'))‖ ≤ 1/100 := by
  classical
  obtain ⟨C,hC,Hcluster⟩ := bounded_points_weighted_cluster
  have hCpos : 0<C := lt_of_lt_of_le zero_lt_one hC
  let η₀ := θ/10
  have hη₀ : 0<η₀ := by dsimp [η₀]; positivity
  obtain ⟨c,hc,hc1,Hc⟩ := exists_scale_cutoff (1/(56*C)) η₀ 1 (by positivity) hη₀ (by norm_num)
  refine ⟨η₀,c,hη₀,by dsimp [η₀]; linarith,hc,hc1,?_⟩
  intro η r s hη hηη hs hsr hr1 y w hw n x v Y hF
  have hr : 0<r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  let d := s/r
  have hd : 0<d := div_pos hs hr
  have hdc : d≤c := (div_le_iff₀ hr).mpr hsr
  have hd1 : d≤1 := hdc.trans hc1
  have hs1 : s≤1 := by
    have hh : s≤r := (div_le_one hr).mp hd1
    exact hh.trans hr1
  have hbase : (56*C)*d^η₀ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (Hc d hd hdc) (by positivity : 0≤56*C)
    simpa only [mul_one_div_cancel (by positivity : (56*C)≠0)] using hh
  have hcoef (b a : ℝ) (hb : 0≤b) (hbC : b≤56*C) (ha : η₀≤a) : b*d^a≤1 :=
    power_coefficient_bound hd hd1 hb hbC ha hbase
  have hpos : 0<∑ i,μ (Y i) := (ENNReal.ofReal_pos.mpr
    (by have hn : (0:ℝ)<n := Nat.cast_pos.mpr hF.1; positivity : 0<d^η*n*s^2)).trans_le hF.2.2.1
  have hmid (i : Fin n) : ‖axisMidpoint (x i) (v i)-axisMidpoint y w‖ ≤ 3 := by
    have hh := tube_midpoints_close hs (hF.2.1 i).1 hw (hF.2.1 i).2.1
    rw [dist_eq_norm] at hh
    exact hh.le.trans (by linarith)
  obtain ⟨S,_,hS,hmass,hcluster⟩ := Hcluster Finset.univ
    (fun i => axisMidpoint (x i) (v i)-axisMidpoint y w) hmid
    (fun i => μ (Y i)) (by simpa using hpos)
  let j := enumerate S
  have hj : Function.Injective j := enumerate_injective S
  have hm : 0<(S.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hmn : S.card≤n := by simpa using Finset.card_le_univ S
  have hsum : (∑ i,μ (Y (j i)))=∑ i∈S,μ (Y i) := sum_enumerate S (fun i => μ (Y i))
  have hret : O (1/C)*(∑ i,μ (Y i)) ≤ ∑ i,μ (Y (j i)) := by
    rw [hsum]
    have hh := mul_le_mul_right hmass (O (1/C))
    have he : O (1/C)*O C=1 := by
      rw [← ENNReal.ofReal_mul (by positivity : 0≤1/C)]
      simp [hCpos.ne',O]
    simpa only [← mul_assoc,he,one_mul] using hh
  have hup : (∑ i,μ (Y (j i))) ≤ O (56*S.card*s^2) := by
    calc
      _ ≤ ∑ _i : Fin S.card,O (56*s^2) := Finset.sum_le_sum fun i _ =>
        (measure_mono (hF.2.1 (j i)).2.2.2).trans
          (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hs.le hs1 _ _ (hF.2.1 (j i)).1)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
        congr 1
        ring
  have hcard : (d^η/(56*C))*n ≤ (S.card:ℝ) := by
    have hh := ((mul_le_mul' (a := O (1/C)) le_rfl hF.2.2.1).trans hret).trans hup
    rw [← ENNReal.ofReal_mul (by positivity : 0≤1/C)] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤56*(S.card:ℝ)*s^2)).mp hh
    have hc' : (1/C)*(d^η*n) ≤ 56*S.card := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hs)).mp
      convert hh' using 1 <;> ring
    have he : d^η/(56*C)*n = (1/56:ℝ)*((1/C)*(d^η*n)) := by ring
    rw [he]
    linarith
  have hden : d^θ ≤ d^η/C := density_power_bound hd hCpos
    (hcoef C (θ-η) hCpos.le (by linarith) (by dsimp [η₀] at *; linarith))
  have hroot : d^(-η)*n/S.card ≤ d^(-θ) := by
    have hb : (56*C)*d^(-(2*η)) ≤ d^(-θ) := inverse_power_error_bound hd
      (hcoef _ (θ-2*η) (by positivity) le_rfl (by dsimp [η₀] at *; linarith))
    have he : ((56*C)*d^(-(2*η)))*((d^η/(56*C))*n)=d^(-η)*n := by
      have hp : d^(-(2*η))*d^η=d^(-η) := by rw [← Real.rpow_add hd]; congr 1; ring
      calc
        _ = (d^(-(2*η))*d^η)*n := by field_simp
        _ = _ := by rw [hp]
    apply (div_le_iff₀ hm).mpr
    rw [← he]
    exact (mul_le_mul_of_nonneg_left hcard (by positivity)).trans
      (mul_le_mul_of_nonneg_right hb hm.le)
  have hθcard : d^θ ≤ d^η/(56*C) := density_power_bound hd (by positivity)
    (hcoef _ (θ-η) (by positivity) le_rfl (by dsimp [η₀] at *; linarith))
  have hθret : d^θ ≤ 1/C := by
    apply (le_div_iff₀ hCpos).mpr
    simpa only [mul_comm] using hcoef C θ hCpos.le (by linarith) (by dsimp [η₀]; linarith)
  have hslab := slabBound_comp hF.2.2.2.2 j hj
    (show d^(-η)*n ≤ (d^(-η)*n/S.card)*S.card by rw [div_mul_cancel₀ _ hm.ne'])
  refine ⟨S.card,j,hj,hmn,⟨Finset.card_pos.mpr hS,fun i => hF.2.1 (j i),?_,?_,slabBound_mono hroot hslab⟩,
    (mul_le_mul_of_nonneg_right hθcard (Nat.cast_nonneg n)).trans hcard,
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hθret) le_rfl).trans hret,?_⟩
  · calc
      _ ≤ O ((d^η/C)*n*s^2) := ENNReal.ofReal_le_ofReal
        (mul_le_mul (mul_le_mul hden (Nat.cast_le.mpr hmn) (Nat.cast_nonneg _) (by positivity))
          le_rfl (sq_nonneg _) (by positivity))
      _ = O (1/C)*O (d^η*n*s^2) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0≤1/C)]
        congr 1
        ring
      _ ≤ O (1/C)*(∑ i,μ (Y i)) := mul_le_mul_right hF.2.2.1 _
      _ ≤ _ := hret
  · have hηθ : η ≤ θ := by
      dsimp [η₀] at hηη
      linarith
    have hK' := convexCount_subfamily (s := s) (L := d^(-η))
      (U := fun i => T s (x i) (v i)) j hj hF.2.2.2.1
    exact convexCount_mono (L := d^(-η)) (L' := d^(-θ))
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hηθ)) hK'
  · intro i i'
    have hh := hcluster (j i) (enumerate_mem S i) (j i') (enumerate_mem S i')
    simpa only [sub_sub_sub_cancel_right] using hh

end WangZahlLot.Obl.wz_broad_grains_improvement
