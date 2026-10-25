-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CentralNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CentralPreparation
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedGainTransfer
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.PowerLoss
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.MassTransfer

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (Fibre normalize normalizedRadius normalizedRadius_pos normalizedRadius_le radius_eq_ratio
    contraction normalize_parent_norm normalize_volume jacobian cancel_volume_factor ConvexCount)
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (axisMidpoint exists_scale_cutoff power_coefficient_bound density_power_bound)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

attribute [local irreducible] WangZahlLot.Obl.wz_rescaled_fibre_alternatives.normalize
set_option maxHeartbeats 1000000

/-- Physical normalization can produce aligned, strictly separated unit
extensions while keeping the selected physical shadings in full. The selected
indices, forward containment and power cardinality bound are all retained. -/
theorem normalize_aligned_with_power_loss {θ : ℝ} (hθ : 0 < θ) :
    ∃ η₀ c : ℝ, 0 < η₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0 < η → η ≤ η₀ → 0 < s → s ≤ c*r → r ≤ 1 →
      ∀ (y w : V) (e : V ≃ₗᵢ[ℝ] V), ‖w‖=1 → e w=axis →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      Fibre r s η y w x v Y → ∃ hr : 0<r,
      ∃ (M : ℕ) (j : Fin M → Fin n) (z u : Fin M → V),
        Function.Injective j ∧
        WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible
          (normalizedRadius r s) θ ((normalizedRadius r s)^(-θ))
          ((normalizedRadius r s)^(-θ)) z u (fun i => normalize e y w r hr '' Y (j i)) ∧
        AlignedAxes z u ∧
        (∀ i, normalize e y w r hr '' T s (x (j i)) (v (j i)) ⊆
          T (normalizedRadius r s) (z i) (u i)) ∧
        (normalizedRadius r s)^θ*n ≤ (M:ℝ) ∧
        O ((normalizedRadius r s)^θ)*(∑ i, μ (Y i)) ≤ ∑ i, μ (Y (j i)) := by
  let ε := θ/10
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεθ : ε ≤ θ := by dsimp [ε]; linarith
  obtain ⟨dC,hdC,_,HC⟩ := exists_scale_cutoff (1/56) (θ/2) 1
    (by norm_num) (by positivity) (by norm_num)
  obtain ⟨ηA,dA,hηA,hηAε,hdA,hdAC,hdAsmall,HA⟩ := prepare_central_admissible hε hdC
  obtain ⟨η₀,cN,hη₀,hcN,hcN1,HN⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.normalize_with_power_loss hηA
  let c := min cN dA
  have hc : 0<c := lt_min hcN hdA
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcN1
  refine ⟨η₀,c,hη₀,hc,hc1,?_⟩
  intro η r s hη hηη hs hsr hr1 y w e hw hew n x v Y hF
  have hr : 0<r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  have hsrN : s ≤ cN*r := hsr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  obtain ⟨_,m,j,z,u,hj,hA,hforward,hmid,hcard,hmass⟩ :=
    HN η r s hη hηη hs hsrN hr1 y w e hw hew n x v Y hF
  let d := normalizedRadius r s
  have hd : 0<d := normalizedRadius_pos hr hs
  have hsr' : s ≤ r := hsr.trans (mul_le_of_le_one_left hr.le hc1)
  have hdδ : d ≤ s/r := by
    rw [show d=4*contraction*(s/r) from radius_eq_ratio r s]
    exact mul_le_of_le_one_left (div_pos hs hr).le (by norm_num)
  have hddA : d ≤ dA := hdδ.trans (((div_le_iff₀ hr).mpr hsr).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hddA.trans hdAsmall).trans (by norm_num)
  have hAb : A d ηA (d^(-ηA)) (d^(-ηA)) m z u
      (fun i => normalize e y w r hr '' Y (j i)) := by
    simpa only [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible,
      ConvexCount,true_and] using hA
  have hmidnorm (i : Fin m) : ‖axisMidpoint (z i) (u i)‖ ≤ 1/2 := by
    change ‖z i+(1/2:ℝ)•u i‖ ≤ _
    rw [hmid i]
    have hm := normalize_parent_norm e hew hr hr1
      ((hF.2.1 (j i)).2.1 (self_subset_thickening hs _
        (by simpa only [zero_smul,add_zero] using
          (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_segment
            (x (j i)) (v (j i)) (a := 0) (by norm_num)))))
    exact hm.le.trans (by norm_num)
  have hcentral (i : Fin m) : normalize e y w r hr '' Y (j i) ⊆ closedBall 0 (1/2) := by
    rintro _ ⟨p,hp,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    exact (normalize_parent_norm e hew hr hr1
      ((hF.2.1 (j i)).2.1 ((hF.2.1 (j i)).2.2.2 hp))).le.trans (by norm_num)
  obtain ⟨k,j',u₀,hj',hkm,hA',hAF,hret⟩ :=
    HA d hd hddA m z u (fun i => normalize e y w r hr '' Y (j i)) hAb hmidnorm hcentral
  let X' : Fin k → V := fun i => recenterStart (z (j' i)) (u (j' i))
  have haxes : AlignedAxes X' (u ∘ j') :=
    ⟨u₀,0,hAF.direction_cap,fun i => (hAF.midpoint i).trans (by norm_num),hAF.aligned⟩
  have hforward' (i : Fin k) : normalize e y w r hr '' T s (x (j (j' i))) (v (j (j' i))) ⊆
      T d (X' i) (u (j' i)) := by
    apply central_shading_subset_recenter (hA.2.1 (j' i)).1 (hforward (j' i))
    rintro _ ⟨p,hp,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    exact (normalize_parent_norm e hew hr hr1 ((hF.2.1 (j (j' i))).2.1 hp)).le.trans (by norm_num)
  have hAtower : WangZahlLot.Obl.wz_multiscale_finite_tower.Admissible
      d ηA (d^(-ηA)) (d^(-ηA)) m z u
      (fun i => normalize e y w r hr '' Y (j i)) := hAb
  have hcard' := hAtower.aligned_retained_cardinality hAF hd hd1 hret
  have hbase : 56*d^(θ/2) ≤ 1 := by
    have hh := HC d hd (hddA.trans hdAC)
    linarith
  have hconst : 56*d^(θ-(2*ηA+ε)) ≤ 1 :=
    power_coefficient_bound hd hd1 (by norm_num) le_rfl
      (by dsimp [ε] at *; linarith) hbase
  have hpowcard : d^θ ≤ d^(2*ηA+ε)/56 := density_power_bound hd (by norm_num) hconst
  have hcardfinal : d^θ*n ≤ (k:ℝ) := by
    calc
      _ ≤ (d^(2*ηA+ε)/56)*n := mul_le_mul_of_nonneg_right hpowcard (Nat.cast_nonneg n)
      _ = ((1/56:ℝ)*d^(ηA+ε))*(d^ηA*n) := by
        rw [show 2*ηA+ε = (ηA+ε)+ηA by ring,Real.rpow_add hd]
        ring
      _ ≤ ((1/56:ℝ)*d^(ηA+ε))*m := mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ k := hcard'
  have hretp : O (d^ε)*(∑ i, μ (Y (j i))) ≤ ∑ i, μ (Y (j (j' i))) := by
    have hh := hret
    simp_rw [normalize_volume] at hh
    rw [← Finset.mul_sum,← Finset.mul_sum] at hh
    apply cancel_volume_factor (by positivity : 0<jacobian r)
    simpa only [mul_left_comm] using hh
  have hmassfinal : O (d^θ)*(∑ i, μ (Y i)) ≤ ∑ i, μ (Y (j (j' i))) := by
    calc
      _ ≤ O (d^(ε+ηA))*(∑ i, μ (Y i)) := mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hd hd1
          (by dsimp [ε] at *; linarith))) _
      _ = O (d^ε)*(O (d^ηA)*(∑ i, μ (Y i))) := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),← Real.rpow_add hd]
      _ ≤ O (d^ε)*(∑ i, μ (Y (j i))) := mul_le_mul_right hmass _
      _ ≤ _ := hretp
  refine ⟨hr,k,j ∘ j',X',u ∘ j',hj.comp hj',?_,haxes,hforward',hcardfinal,hmassfinal⟩
  have hAt := admissible_mono hd hd1 hεθ hA'
  simpa only [A,K,Function.comp_def,d,X',
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible,
    ConvexCount,true_and] using hAt

end WangZahlLot.Obl.wz_broad_grains_improvement
