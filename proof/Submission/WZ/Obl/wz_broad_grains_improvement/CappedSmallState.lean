-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedSmallState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedSmallPrisms
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedPrismState

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- At small coarse radius and grain length, capped exact prisms give a
volume gain or a full grain state on the original fine family. -/
theorem small_capped_prisms_gain_or_state {σ ω ζ ε t : ℝ}
    (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hε : 0 < ε) (ht : 0 < t) (hβ : 0 ≤ ω*ζ/100) (hβ1 : ω*ζ/100 ≤ 1) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d^(-h)) (d^(-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      d^(1-ω/100) ≤ ρ → ρ ≤ d^t → c ≤ d^t → 4*d ≤ c →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        J ω ζ d ε (16384*ρ) (32*c) n x v Y 0 := by
  obtain ⟨ηT,dT,hηT,hηTε,hdT,hdT100,HT⟩ :=
    stage_zero_of_capped_prisms (ω := ω) (ζ := ζ) hε
  let θ := min ηT 1
  have hθ : 0 < θ := lt_min hηT zero_lt_one
  obtain ⟨κ,ηS,dS,hκ,hηS,hηSθ,hdS,hdS100,HS⟩ :=
    small_prisms_gain_or_capped_stage_two hσ hσ2 hω hω1 hE hθ (min_le_right _ _) ht hβ hβ1
  refine ⟨(θ/100)*ω/2,κ,ηS,min dT dS,by positivity,hκ,hηS,
    hηSθ.trans ((min_le_left _ _).trans hηTε),by positivity,
    (min_le_left _ _).trans hdT100,?_⟩
  intro d h n x v Y hd hdd hh hA ρ c D HD Hcaps hbase hρt hct hdc
  have hdT' := hdd.trans (min_le_left _ _)
  have hdS' := hdd.trans (min_le_right _ _)
  have hd1 : d ≤ 1 := (hdT'.trans hdT100).trans (by norm_num)
  rcases HS hd hdS' hh hA ρ c D HD Hcaps hρt hct hdc with hg | hs
  · exact Or.inl hg
  · apply Or.inr
    apply HT hd hdT' (min_le_left _ _) (admissible_mono hd hd1 (hh.trans hηSθ) hA) hs
    have hρ : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hbase
    linarith

end WangZahlLot.Obl.wz_broad_grains_improvement
