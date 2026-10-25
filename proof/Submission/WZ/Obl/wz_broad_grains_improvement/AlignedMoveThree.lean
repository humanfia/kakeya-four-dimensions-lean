-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedMoveThree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedStageAlternative
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPrismProgress

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- The geometric part of Move 3 before exact coarse covering and incidence
normalization. The fixed length multiplier is chosen before the fine scale
and before any residual shading. -/
def PrismImprovement (σ ω ζ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α κ η d₀ K : ℝ,
    0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1/100 ∧ 1 ≤ K ∧
    ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y → J ω ζ d h ρ c n x v Y 2 →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (∃ ρ' c',J ω ζ d ε ρ' c' n x v Y 3) ∨
        ∃ ρ',d^(-ζ/2000)*ρ ≤ ρ' ∧
          WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ d ε ρ' (K*c) n x v Y 0

/-- Once the geometric prism improvement is available, all remaining steps
of Move 3 hold for scalar-aligned original fine families. -/
theorem aligned_move_three_of_prism_improvement {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε)
    (hprism : PrismImprovement σ ω ζ) :
    ∃ α κ η d₀ : ℝ,0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d^(-h)) (d^(-h)) n x v Y → AlignedAxes x v →
      J ω ζ d h ρ c n x v Y 2 →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (∃ ρ' c',D ω ζ d ε ρ' c' n x v Y true) ∨
        ∃ ρ' c',D ω ζ d ε ρ' c' n x v Y false ∧
          c ≤ c' ∧ d^(-ζ/2000)*ρ ≤ ρ' := by
  obtain ⟨αT,κT,ηT,dT,hαT,hκT,hηT,hηTε,hdT,hdT100,HT⟩ :=
    aligned_capped_prisms_give_scale_progress hσ hσ2 hω hω1 hE hζ hζω hε
  obtain ⟨αG,κG,ηG,dG,K,hαG,hκG,hηG,hηGε,hdG,_,hK,HG⟩ :=
    hprism (ηT/4) (by positivity)
  obtain ⟨η,dA,hη,hηηG,hdA,_,HA⟩ :=
    capped_prisms_of_stage_alternative hηT hηG hηGε
  have hηηT : η ≤ ηT := (hηηG.trans hηGε).trans (by linarith)
  refine ⟨min αG αT,min κG κT,η,min dT (min dG dA),by positivity,by positivity,hη,
    hηηT.trans hηTε,by positivity,(min_le_left _ _).trans hdT100,?_⟩
  intro d h ρ c n x v Y hd hdd hh hhη hA haxes hJ
  have hdT' := hdd.trans (min_le_left _ _)
  have hdG' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdA' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hdT'.trans hdT100).trans (by norm_num)
  have hβ : 0 ≤ ω*ζ/100 := by positivity
  have hβ1 : ω*ζ/100 ≤ 1 := by
    have hζ1 : ζ ≤ 1 := by linarith
    nlinarith [mul_nonneg hω.le hζ.le]
  have hηinput := hhη.trans hηηT
  rcases HA hd hdA' hhη hβ hβ1 hA hJ (r₀ := d^(-ζ/2000)*ρ) (c₀ := K*c)
      (by intro R hAR hJR; exact HG hd hdG' hηG.le le_rfl hAR hJR) with hg | ht | hp
  · exact Or.inl ((gain_mono hd hd1 (min_le_left _ _) (min_le_left _ _)
      (le_min hκG.le hκT.le)).trans hg)
  · obtain ⟨ρ',c',hJ'⟩ := ht
    exact Or.inr (Or.inl ⟨ρ',c',stage_three_to_terminal (stage_mono hd hd1 hηTε hJ')⟩)
  · obtain ⟨ρ₀,hscale,P,HP,Hcaps⟩ := hp
    have hc : 0 < c := (Real.rpow_pos_of_pos hd _).trans_le (stage_two_length_lower hd hJ)
    rcases HT hd hdT' hηT.le le_rfl (admissible_mono hd hd1 hηinput hA)
        haxes (stage_mono hd hd1 hηinput hJ) ρ₀ (K*c) P HP Hcaps hscale
        (le_mul_of_one_le_left hc.le hK) with hg | hp
    · exact Or.inl ((gain_mono hd hd1 (min_le_right _ _) (min_le_right _ _)
        (le_min hκG.le hκT.le)).trans hg)
    · exact Or.inr (Or.inr hp)

end WangZahlLot.Obl.wz_broad_grains_improvement
