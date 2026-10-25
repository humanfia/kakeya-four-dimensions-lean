-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedSeparatedState.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedAllScaleState

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- For lengths separated from the fine radius by a power, capped prism
normalization preserves both the coarse radius and the grain length. -/
theorem capped_prisms_gain_or_nondecreasing_state {σ ω ζ ε b : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) (hε : 0 < ε) (hb : 0 < b) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → h ≤ η → A d h (d ^ (-h)) (d ^ (-h)) n x v Y →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 1 → D.HasCaps d h ρ c →
      d ^ (1 - ω / 100) ≤ ρ → d ^ (1 - b) ≤ c →
      O (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
        ∃ ρ' c', ρ ≤ ρ' ∧ c ≤ c' ∧ J ω ζ d ε ρ' c' n x v Y 0 := by
  obtain ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,H⟩ :=
    capped_prisms_gain_or_state_with_length hσ hσ2 hω hω1 hE hζ hζω hε
      (half_pos hb)
  refine ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,?_⟩
  intro d h n x v Y hd hdd hh hA ρ c D HD Hcaps hbase hlength
  rcases H hd hdd hh hA ρ c D HD Hcaps hbase with hg | hs
  · exact Or.inl hg
  · obtain ⟨ρ',c',hρ,_,hc,hs⟩ := hs
    have hd1 : d < 1 := (hdd.trans hd₀small).trans_lt (by norm_num)
    have hp : d ^ (1 - b / 2) < d ^ (1 - b) :=
      Real.rpow_lt_rpow_of_exponent_gt hd hd1 (by linarith)
    exact Or.inr ⟨ρ',c',hρ,hc (hp.trans_le hlength),hs⟩

/-- The shape and small-coarse-scale conditions of a stage-two state already
give the power separation needed by the preceding normalization theorem. -/
theorem stage_two_length_lower {ω ζ d h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (H : J ω ζ d h ρ c n x v Y 2) :
    d ^ (1 - ω / 100) ≤ c := by
  obtain ⟨S,Z,N,y,w,f,a,g,_,_,_,_,hH,hstop⟩ := H
  obtain ⟨L,z,e,G,γ,m,hda,hab,hbc,_⟩ := hH
  have hc : 0 < c := hd.trans_le (hda.trans (hab.trans hbc))
  have hρ : ρ ≤ d ^ (ω / 100) := hstop.2.1 (by decide)
  have hprod : d ≤ d ^ (ω / 100) * c :=
    (hda.trans hab).trans (mul_le_mul_of_nonneg_right hρ hc.le)
  have hp : 0 < d ^ (ω / 100) := Real.rpow_pos_of_pos hd _
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ = d := by
      rw [← Real.rpow_add hd, show ω / 100 + (1 - ω / 100) = 1 by ring, Real.rpow_one]
    _ ≤ _ := hprod

end WangZahlLot.Obl.wz_broad_grains_improvement
