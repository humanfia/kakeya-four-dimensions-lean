-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPrismProgress.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CappedSeparatedState
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedCappedCover
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedGainTransfer

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- On aligned fine families, separated-length capped prisms need no exact
coarse cover as input: the cover and normalization preserve both scales. -/
theorem aligned_capped_prisms_gain_or_nondecreasing_state {σ ω ζ ε b : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) (hε : 0 < ε) (hb : 0 < b) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ {d h : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d ^ (-h)) (d ^ (-h)) n x v Y → AlignedAxes x v →
      ∀ ρ c (D : PrismData n), D.Valid ω ζ d h ρ c x v Y 0 → D.HasCaps d h ρ c →
      d ^ (1 - ω / 100) ≤ ρ → d ^ (1 - b) ≤ c →
      O (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
        ∃ ρ' c', ρ ≤ ρ' ∧ c ≤ c' ∧ J ω ζ d ε ρ' c' n x v Y 0 := by
  have hβ : 0 < ω * ζ / 100 := by positivity
  have hβ1 : ω * ζ / 100 ≤ 1 := by
    have hζ1 : ζ ≤ 1 := by linarith
    nlinarith [mul_nonneg hω.le hζ.le]
  obtain ⟨α,κ,ηS,dS,hα,hκ,hηS,hηSε,hdS,hdSsmall,HS⟩ :=
    capped_prisms_gain_or_nondecreasing_state hσ hσ2 hω hω1 hE hζ hζω hε hb
  obtain ⟨η,dC,hη,hηS',hdC,hdCsmall,HC⟩ :=
    aligned_exact_capped_prism_cover (τ := ω / 100) (by positivity) (by linarith)
      hβ hβ1 hηS
  refine ⟨α,κ,η,min dS dC,hα,hκ,hη,hηS'.trans hηSε,by positivity,
    (min_le_left _ _).trans hdSsmall,?_⟩
  intro d h n x v Y hd hdd hh hhη hA haxes ρ c D HD Hcaps hbase hlength
  obtain ⟨u,t,hcap,hmid,halign⟩ := haxes
  obtain ⟨ρ',hρ',D',HD',Hcaps',_⟩ := HC hd (hdd.trans (min_le_right _ _))
    hh hhη hA hcap hmid halign ρ c hbase D HD Hcaps
  have hd1 : d ≤ 1 := ((hdd.trans (min_le_left _ _)).trans hdSsmall).trans (by norm_num)
  rcases HS hd (hdd.trans (min_le_left _ _)) le_rfl
      (admissible_mono hd hd1 (hhη.trans hηS') hA) ρ' c D' HD' Hcaps'
      (hbase.trans hρ') hlength with hg | hs
  · exact Or.inl hg
  · obtain ⟨ρ'',c',hρ'',hc',hs⟩ := hs
    exact Or.inr ⟨ρ'',c',hρ'.trans hρ'',hc',hs⟩

/-- A growing capped prism family supplies the exact scale-growth alternative
on aligned stage-two inputs. No length loss remains in this assembly step. -/
theorem aligned_capped_prisms_give_scale_progress {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000) (hε : 0 < ε) :
    ∃ α κ η d₀ : ℝ, 0 < α ∧ 0 < κ ∧ 0 < η ∧ η ≤ ε ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0 < d → d ≤ d₀ → 0 ≤ h → h ≤ η →
      A d h (d ^ (-h)) (d ^ (-h)) n x v Y → AlignedAxes x v →
      J ω ζ d h ρ c n x v Y 2 →
      ∀ ρ₀ c₀ (D₀ : PrismData n),
        D₀.Valid ω ζ d h ρ₀ c₀ x v Y 0 → D₀.HasCaps d h ρ₀ c₀ →
        d ^ (-ζ / 2000) * ρ ≤ ρ₀ → c ≤ c₀ →
        O (κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ)) ≤ μ (⋃ i, Y i) ∨
          ∃ ρ' c', D ω ζ d ε ρ' c' n x v Y false ∧
            c ≤ c' ∧ d ^ (-ζ / 2000) * ρ ≤ ρ' := by
  obtain ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,HG⟩ :=
    aligned_capped_prisms_gain_or_nondecreasing_state hσ hσ2 hω hω1 hE hζ hζω hε
      (b := ω / 100) (by positivity)
  refine ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀small,?_⟩
  intro d h ρ c n x v Y hd hdd hh hhη hA haxes hJ ρ₀ c₀ D₀ HD₀ Hcaps hscale hlength
  have hclow := (stage_two_length_lower hd hJ).trans hlength
  have hρbase : d ^ (1 - ω / 100) ≤ ρ := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hb,_⟩ := hJ
    exact hb
  have hρpos : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hρbase
  have hd1 : d ≤ 1 := (hdd.trans hd₀small).trans (by norm_num)
  have hρle : ρ ≤ ρ₀ := by
    apply le_trans _ hscale
    exact le_mul_of_one_le_left hρpos.le
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith : -ζ / 2000 ≤ 0))
  rcases HG hd hdd hh hhη hA haxes ρ₀ c₀ D₀ HD₀ Hcaps
      (hρbase.trans hρle) hclow with hg | hs
  · exact Or.inl hg
  · obtain ⟨ρ',c',hρ',hc',hs⟩ := hs
    exact Or.inr ⟨ρ',c',stage_zero_to_loose hs,hlength.trans hc',hscale.trans hρ'⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
