-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ClusteredNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CentralNormalization
import Submission.WZ.Obl.wz_broad_grains_improvement.FibreMidpointCluster

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (Fibre normalize normalizedRadius normalizedRadius_pos normalizedRadius_le radius_eq_ratio contraction)
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

attribute [local irreducible] WangZahlLot.Obl.wz_rescaled_fibre_alternatives.normalize
set_option maxHeartbeats 800000

/-- An arbitrary physical fibre can be normalized to aligned unit extensions
on a fixed-size physical midpoint cluster, retaining power fractions of the
original indices and shadings. -/
theorem normalize_clustered_aligned {θ : ℝ} (hθ : 0<θ) :
    ∃ η₀ c : ℝ, 0<η₀ ∧ 0<c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0<η → η ≤ η₀ → 0<s → s ≤ c*r → r ≤ 1 →
      ∀ (y w : V) (e : V ≃ₗᵢ[ℝ] V), ‖w‖=1 → e w=axis →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      Fibre r s η y w x v Y → ∃ hr : 0<r,
      ∃ (M : ℕ) (j : Fin M → Fin n) (z u : Fin M → V),
        Function.Injective j ∧
        WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible
          (normalizedRadius r s) θ ((normalizedRadius r s)^(-θ))
          ((normalizedRadius r s)^(-θ)) z u (fun i => normalize e y w r hr '' Y (j i)) ∧
        AlignedAxes z u ∧
        (∀ i, normalize e y w r hr '' T s (x (j i)) (v (j i)) ⊆ T (normalizedRadius r s) (z i) (u i)) ∧
        (normalizedRadius r s)^θ*n  ≤  (M:ℝ) ∧
        O ((normalizedRadius r s)^θ)*(∑ i,μ (Y i))  ≤  ∑ i,μ (Y (j i)) ∧
        ∀ i i', ‖axisMidpoint (x (j i)) (v (j i))-axisMidpoint (x (j i')) (v (j i'))‖ ≤ 1/100 := by
  let ε := θ/4
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨ηN,cN,hηN,hcN,hcN1,HN⟩ := normalize_aligned_with_power_loss hε
  let β := min ηN ε
  have hβ : 0<β := lt_min hηN hε
  have hβN : β ≤ ηN := min_le_left _ _
  have hβε : β ≤ ε := min_le_right _ _
  obtain ⟨η₀,cC,hη₀,_,hcC,hcC1,HC⟩ := fibre_midpoint_cluster hβ
  let c := min cN cC
  have hc : 0<c := lt_min hcN hcC
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcN1
  refine ⟨η₀,c,hη₀,hc,hc1,?_⟩
  intro η r s hη hηη hs hsr hr1 y w e hw hew n x v Y hF
  have hr : 0<r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  have hsrC : s ≤ cC*r := hsr.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le)
  have hsrN : s ≤ cN*r := hsr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  obtain ⟨m,j,hj,_,hFC,hcardC,hmassC,hcluster⟩ := HC η r s hη hηη hs hsrC hr1 y w hw n x v Y hF
  obtain ⟨_,k,j',z,u,hj',hA,haxes,hforward,hcardN,hmassN⟩ :=
    HN β r s hβ hβN hs hsrN hr1 y w e hw hew m (x ∘ j) (v ∘ j) (Y ∘ j) hFC
  let d := normalizedRadius r s
  have hd : 0<d := normalizedRadius_pos hr hs
  have hsr' : s ≤ r := hsr.trans (mul_le_of_le_one_left hr.le hc1)
  have hd1 : d ≤ 1 := (normalizedRadius_le hr hsr').trans (by norm_num)
  have hdδ : d ≤ s/r := by
    rw [show d=4*contraction*(s/r) from radius_eq_ratio r s]
    exact mul_le_of_le_one_left (div_pos hs hr).le (by norm_num)
  have hεθ : ε ≤ θ := by dsimp [ε]; linarith
  have hsumθ : ε+β ≤ θ := by dsimp [ε] at *; linarith
  have hpow : d^θ ≤ d^(ε+β) := Real.rpow_le_rpow_of_exponent_ge hd hd1 hsumθ
  have hpowC : d^β ≤ (s/r)^β := Real.rpow_le_rpow hd.le hdδ hβ.le
  have hcard : d^θ*n ≤ (k:ℝ) := by
    calc
      _  ≤  d^(ε+β)*n := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg n)
      _ = d^ε*(d^β*n) := by rw [Real.rpow_add hd,mul_assoc]
      _  ≤  d^ε*((s/r)^β*n) := by gcongr
      _  ≤  d^ε*m := mul_le_mul_of_nonneg_left hcardC (Real.rpow_nonneg hd.le _)
      _  ≤  k := hcardN
  have hmass : O (d^θ)*(∑ i,μ (Y i)) ≤ ∑ i,μ (Y (j (j' i))) := by
    calc
      _  ≤  O (d^(ε+β))*(∑ i,μ (Y i)) := mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _
      _ = O (d^ε)*(O (d^β)*(∑ i,μ (Y i))) := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),← Real.rpow_add hd]
      _  ≤  O (d^ε)*(O ((s/r)^β)*(∑ i,μ (Y i))) := by
        gcongr
        exact ENNReal.ofReal_le_ofReal hpowC
      _  ≤  O (d^ε)*(∑ i,μ (Y (j i))) := mul_le_mul_right hmassC _
      _  ≤  _ := hmassN
  have hneg : d^(-ε) ≤ d^(-θ) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hεθ)
  exact ⟨hr,k,j ∘ j',z,u,hj.comp hj',
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.admissible_mono hd hd1 hεθ hneg hneg hA,
    haxes,hforward,hcard,hmass,fun i i' => hcluster (j' i) (j' i')⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
