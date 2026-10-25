-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPhysicalAlternative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.ClusteredNormalization
import Submission.WZ.Obl.wz_broad_grains_improvement.ClusteredLocalCover
import Submission.WZ.Obl.wz_multiscale_finite_tower.PhysicalAlternative

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (Fibre FibreCover GlobalCover normalize normalizedRadius normalizedRadius_pos normalizedRadius_le
    radius_eq_ratio contraction coverScale cover_parameters improvementConstant improvementConstant_pos
    local_improvement_of_normalized)
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (PhysicalFrame PhysicalCover volumeFactor physicalCover_of_fibreCover)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (exists_rotation)

attribute [local irreducible] WangZahlLot.Obl.wz_rescaled_fibre_alternatives.normalize
set_option maxHeartbeats 1000000

/-- The local one-scale alternative is needed only on aligned normalized axes,
and only below a uniform cutoff. -/
def AlignedAlternative (σ ω : ℝ) : Prop :=
  ∀ ζ : ℝ, 0<ζ → ∃ α κ η d₀ : ℝ, 0<α ∧ 0<κ ∧ 0<η ∧ 0<d₀ ∧
    ∀ d : ℝ, 0<d → d ≤ d₀ → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Admissible d η (d^(-η)) (d^(-η)) x v Y →
      AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ μ (⋃ i,Y i) ∨ GlobalCover d ζ ω x v Y

/-- Aligned normalized alternatives yield an unrestricted physical fibre
alternative, by first localizing physical midpoints at a fixed scale. -/
theorem local_alternative_of_aligned {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0<ω) (hω1 : ω ≤ 1)
    (hP : AlignedAlternative σ ω) {ζ : ℝ} (hζ : 0<ζ) :
    ∃ α κ : ℝ, 0<α ∧ 0<κ ∧ ∃ η₀ c : ℝ, 0<η₀ ∧ 0<c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0<η → η ≤ η₀ → 0<s → s ≤ c*r → r ≤ 1 →
      ∀ y w : V, ‖w‖=1 → ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      Fibre r s η y w x v Y →
      O (κ*(s/r)^(ω-α)*(n*s^2)*(n*(s/r))^(-σ)) ≤ μ (⋃ i,Y i) ∨
        FibreCover r s ζ coverScale ω y w x v Y := by
  let τ := ζ/100
  have hτ : 0<τ := by dsimp [τ]; positivity
  obtain ⟨α₀,κ₀,ηP,dP,hα₀,hκ₀,hηP,hdP,HP⟩ := hP τ hτ
  let θ := min ηP (min 1 (min (α₀/4) τ))
  have hθ : 0<θ := lt_min hηP (lt_min zero_lt_one (lt_min (by positivity) hτ))
  have hθηP : θ ≤ ηP := min_le_left _ _
  have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hθα : θ ≤ α₀/2 := by
    have hh : θ ≤ α₀/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hθτ : θ ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ηN,cN,hηN,hcN,hcN1,HN⟩ := normalize_clustered_aligned hθ
  obtain ⟨q,cP,hq,hτq,hcP,hcP100,HC⟩ := cover_parameters hζ hω
  let η₀ := min ηN τ
  let c := min cN (min cP dP)
  have hη₀ : 0<η₀ := lt_min hηN hτ
  have hc : 0<c := lt_min hcN (lt_min hcP hdP)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcN1
  have hcP' : c ≤ cP := (min_le_right _ _).trans (min_le_left _ _)
  have hcdP : c ≤ dP := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨α₀/2,improvementConstant κ₀ ω α₀ σ,by positivity,
    improvementConstant_pos hκ₀,η₀,c,hη₀,hc,hc1,?_⟩
  intro η r s hη hη0 hs hsr hr1 y w hw n x v Y hF
  have hr : 0<r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  have hsrN : s ≤ cN*r := hsr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hηN' : η ≤ ηN := hη0.trans (min_le_left _ _)
  have hητ : η ≤ τ := hη0.trans (min_le_right _ _)
  obtain ⟨e,hew⟩ := exists_rotation hw
  obtain ⟨_,M,j,z,u,hj,hA,haxes,hforward,hcard,hselected,hcluster⟩ :=
    HN η r s hη hηN' hs hsrN hr1 y w e hw hew n x v Y hF
  have hsr' : s ≤ r := hsr.trans (mul_le_of_le_one_left hr.le hc1)
  have hs100 : s ≤ 1/100 := calc
    _ ≤ c*r := hsr
    _ ≤ c := by nlinarith only [mul_le_mul_of_nonneg_left hr1 hc.le]
    _ ≤ cP := hcP'
    _ ≤ _ := hcP100
  have hδ : 0<s/r := div_pos hs hr
  have hδc : s/r ≤ c := (div_le_iff₀ hr).mpr hsr
  obtain ⟨hsmall,hqsmall,hrsmall,hmasssmall,herrorsmall⟩ := HC (s/r) hδ (hδc.trans hcP')
  have hd : 0<normalizedRadius r s := normalizedRadius_pos hr hs
  have hd100 : normalizedRadius r s ≤ 1/100 := (normalizedRadius_le hr hsr').trans (by norm_num)
  have hd1 : normalizedRadius r s ≤ 1 := hd100.trans (by norm_num)
  have hddP : normalizedRadius r s ≤ dP := by
    have hh : normalizedRadius r s ≤ s/r := by
      rw [radius_eq_ratio]
      exact mul_le_of_le_one_left hδ.le (by norm_num)
    exact hh.trans (hδc.trans hcdP)
  have hcount : (normalizedRadius r s)^(-θ) ≤ (normalizedRadius r s)^(-ηP) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθηP)
  have hAP := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.admissible_mono hd hd1 hθηP hcount hcount hA
  rcases HP (normalizedRadius r s) hd hddP M z u
    (fun i => normalize e y w r hr '' Y (j i)) hAP haxes with hQ | hG
  · exact Or.inl (local_improvement_of_normalized hσ hθα hκ₀ hr hs hsr' e y w
      hF.1 hA.1 j hj Y hcard hQ)
  · right
    exact local_cover_of_clustered_normalized hζ hω hω1 hθ1 hθτ hη hητ hr hr1 hs hsr' hs100 hq hτq
      (by simpa only [radius_eq_ratio] using hsmall)
      (by simpa only [radius_eq_ratio] using hqsmall)
      (by simpa only [radius_eq_ratio] using hrsmall)
      (by simpa only [radius_eq_ratio] using hmasssmall)
      (by simpa only [radius_eq_ratio] using herrorsmall)
      hw e hew x v Y hF j hj z u hA hforward hcluster hselected hG

/-- The uniform physical alternative consumed by hierarchy insertion. -/
def PhysicalStep (σ ω : ℝ) : Prop :=
  ∀ ζ h : ℝ, 0<ζ → 0<h →
    ∃ α κ θ c : ℝ, 0<α ∧ 0<κ ∧ 0<θ ∧ θ ≤ 1 ∧ 0<c ∧ c ≤ 1 ∧
      ∀ d r s : ℝ, 0<d → d ≤ 1 → 0<r → 0<s → d*r ≤ s →
      s ≤ c*r → r ≤ 1 → s/r ≤ d^h → ∀ y w : V, ‖w‖=1 → ∀ n x v Y,
      PhysicalFrame d r s θ y w n x v Y →
      O (κ*r^2*volumeFactor σ ω (s/r) n*(s/r)^(-α)) ≤ μ (⋃ i,Y i) ∨
        PhysicalCover d r s ζ coverScale ω y w n x v Y

/-- Scalar alignment is sufficient for the full physical-step interface used
by the finite hierarchy. No alignment restriction remains on PhysicalFrame. -/
theorem physical_step_of_aligned {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0<ω) (hω1 : ω ≤ 1)
    (hP : AlignedAlternative σ ω) : PhysicalStep σ ω := by
  intro ζ h hζ hh
  obtain ⟨α,κ,hα,hκ,η,c,hη,hc,hc1,HP⟩ := local_alternative_of_aligned hσ hω hω1 hP hζ
  refine ⟨α,κ,min 1 (h*η),c,hα,hκ,lt_min zero_lt_one (mul_pos hh hη),
    min_le_left _ _,hc,hc1,?_⟩
  intro d r s hd hd1 hr hs hdr hsr hr1 hgap y w hw n x v Y hF
  have hF' := hF.to_fibre hd hd1 hr hs hη.le hgap (min_le_right _ _)
  rcases HP η r s hη le_rfl hs hsr hr1 y w hw n x v Y hF' with hV | hC
  · left
    convert hV using 1
    congr 1
    dsimp [volumeFactor]
    rw [sub_eq_add_neg,Real.rpow_add (div_pos hs hr)]
    field_simp
  · exact Or.inr (physicalCover_of_fibreCover hC hd ((le_div_iff₀ hr).mpr hdr) hζ.le)

end WangZahlLot.Obl.wz_broad_grains_improvement
