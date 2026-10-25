-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedImprovement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedMoveTwo
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedMoveThree
import Submission.WZ.Obl.wz_broad_grains_move_one

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- The combined improvement alternative on scalar-aligned fine families.
Every output still refers to the original fine indices and shadings. -/
def AlignedImprovement (σ ω ζ ε : ℝ) : Prop :=
  ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ η≤ε ∧ 0<d₀ ∧ d₀≤1/100 ∧
    ∀ d : ℝ,0<d → d≤d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
    A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
    ∀ ρ c,D ω ζ d η ρ c n x v Y false →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (∃ ρ' c',D ω ζ d ε ρ' c' n x v Y true) ∨
        ∃ ρ' c',D ω ζ d ε ρ' c' n x v Y false ∧
          (d^(-ζ/2)*c≤c' ∨ c≤c' ∧ d^(-ζ/2000)*ρ≤ρ')

/-- Accepted Move 1 and the aligned Move 2/3 adapters give the complete
combined improvement once the uncapped geometric prism step is supplied. -/
theorem aligned_improvement_of_prisms {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ/100) (hprism : PrismImprovement σ ω ζ) :
    AlignedImprovement σ ω ζ ε := by
  obtain ⟨α₃,κ₃,η₃,d₃,hα₃,hκ₃,hη₃,hη₃ε,hd₃,hd₃100,H₃⟩ :=
    aligned_move_three_of_prism_improvement hσ hσ2 hω hω1 hE hζ hζω hε hprism
  obtain ⟨α₂,κ₂,η₂,d₂,hα₂,hκ₂,hη₂,hη₂η₃,hd₂,_,H₂⟩ :=
    aligned_move_two hσ hσ2 hω hω1 hE hζ hζω hη₃
  obtain ⟨α₁,κ₁,η₁,d₁,hα₁,hκ₁,hη₁,hη₁η₂,hd₁,_,H₁⟩ :=
    WangZahlLot.wz_broad_grains_move_one σ ω hσ hσ2 hω hω1
      O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl P rfl B rfl
      C rfl H rfl E rfl R rfl J rfl hE hR ζ hζ hζω η₂ hη₂
      ((hη₂η₃.trans hη₃ε).trans hεζ)
  let α := min α₁ (min α₂ α₃)
  let κ := min κ₁ (min κ₂ κ₃)
  have hα : 0 < α := by dsimp [α]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hη₁ε := (hη₁η₂.trans hη₂η₃).trans hη₃ε
  refine ⟨α,κ,η₁,min d₃ (min d₂ d₁),hα,hκ,hη₁,hη₁ε,by positivity,
    (min_le_left _ _).trans hd₃100,?_⟩
  intro d hd hdd n x v Y hA haxes ρ c hD
  have hd₃' := hdd.trans (min_le_left _ _)
  have hd₂' := hdd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd₁' := hdd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := (hd₃'.trans hd₃100).trans (by norm_num)
  have hgain₁ := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
    (show α≤α₁ from min_le_left _ _) (show κ≤κ₁ from min_le_left _ _) hκ.le
  have hgain₂ := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
    (show α≤α₂ from (min_le_right _ _).trans (min_le_left _ _))
    (show κ≤κ₂ from (min_le_right _ _).trans (min_le_left _ _)) hκ.le
  have hgain₃ := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
    (show α≤α₃ from (min_le_right _ _).trans (min_le_right _ _))
    (show κ≤κ₃ from (min_le_right _ _).trans (min_le_right _ _)) hκ.le
  rcases H₁ d hd hd₁' n x v Y hA ρ c (loose_to_stage_zero hD) with hg | hJ₁ | hp
  · exact Or.inl (hgain₁.trans hg)
  · rcases H₂ d hd hd₂' n x v Y (admissible_mono hd hd1 hη₁η₂ hA) haxes ρ c hJ₁ with
      hg | hJ₂ | hp
    · exact Or.inl (hgain₂.trans hg)
    · rcases H₃ hd hd₃' hη₃.le le_rfl
        (admissible_mono hd hd1 (hη₁η₂.trans hη₂η₃) hA) haxes hJ₂ with hg | ht | hp
      · exact Or.inl (hgain₃.trans hg)
      · exact Or.inr (Or.inl ht)
      · obtain ⟨ρ',c',hD',hc',hρ'⟩ := hp
        exact Or.inr (Or.inr ⟨ρ',c',hD',Or.inr ⟨hc',hρ'⟩⟩)
    · obtain ⟨ρ',c',hJ',hc'⟩ := hp
      exact Or.inr (Or.inr ⟨ρ',c',stage_zero_to_loose (stage_mono hd hd1 hη₃ε hJ'),Or.inl hc'⟩)
  · obtain ⟨ρ',c',hJ',hc'⟩ := hp
    exact Or.inr (Or.inr ⟨ρ',c',stage_zero_to_loose
      (stage_mono hd hd1 (hη₂η₃.trans hη₃ε) hJ'),Or.inl hc'⟩)

end WangZahlLot.Obl.wz_broad_grains_improvement
