-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PrismEndpoint.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedOneScale
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismConcentration
import Submission.WZ.Obl.wz_rescaled_tube_estimate

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory

/-- The actual original-input geometric construction supplies the prism
endpoint with length multiplier one. Its radius growth is stronger than
the progress required by the frozen grain iteration. -/
theorem prism_improvement_of_estimate {σ ω ζ : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) : PrismImprovement σ ω ζ := by
  intro ε hε
  have he : 0 < min ε (ζ/100) := by positivity
  obtain ⟨α,κ,η,d₀,hα,hκ,hη,hηe,hd₀,hd₀100,H⟩ :=
    MoveThree.gain_terminal_or_incidence_prisms hσ hσ2 hω hω1 hE hζ hζω
      he (min_le_right _ _)
  refine ⟨α,κ,η,d₀,1,hα,hκ,hη,hηe.trans (min_le_left _ _),hd₀,hd₀100,le_rfl,?_⟩
  intro d h ρ c n x v Y hd hdd hh hhη hA hJ
  have hd1 : d ≤ 1 := (hdd.trans hd₀100).trans (by norm_num)
  rcases H d h hd hdd hh hhη n x v Y hA ρ c hJ with hg | ht | hp
  · exact Or.inl hg
  · exact Or.inr (Or.inl ⟨ρ,c,stage_mono hd hd1 (min_le_left _ _) ht⟩)
  · obtain ⟨ρ',hgrow,hG⟩ := hp
    have hρ : 0 ≤ ρ := by
      obtain ⟨S,Z,N,y,w,f,a,g,_,hbase,_⟩ := hJ
      exact (Real.rpow_pos_of_pos hd _).le.trans hbase
    have hgrow' : d^(-ζ/2000)*ρ ≤ ρ' :=
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -ζ/400≤ -ζ/2000)) hρ).trans hgrow
    refine Or.inr (Or.inr ⟨ρ',hgrow',?_⟩)
    simpa only [one_mul] using WangZahlLot.Obl.wz_move_two_capped_prism_overlap.G_mono
      hd hd1 (min_le_left ε (ζ/100)) (le_refl 0) hG

/-- Residual restoration and local union-volume selection add incidence
caps to the actual prism construction, without any alignment assumption. -/
theorem capped_prism_improvement {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε) :
    ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ η≤ε ∧ 0<d₀ ∧ d₀≤1/100 ∧
      ∀ {d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V},
      0<d → d≤d₀ → 0≤h → h≤η → A d h (d^(-h)) (d^(-h)) n x v Y →
      J ω ζ d h ρ c n x v Y 2 →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (∃ ρ' c',J ω ζ d ε ρ' c' n x v Y 3) ∨
        ∃ ρ',d^(-ζ/2000)*ρ ≤ ρ' ∧
          ∃ P : WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PrismData n,
            P.Valid ω ζ d ε ρ' c x v Y 0 ∧ P.HasCaps d ε ρ' c := by
  have he : 0 < min (ε/4) (ζ/100) := by positivity
  obtain ⟨α,κ,θ,dG,hα,hκ,hθ,hθe,hdG,hdG100,HG⟩ :=
    MoveThree.gain_terminal_or_incidence_prisms hσ hσ2 hω hω1 hE hζ hζω
      he (min_le_right _ _)
  have hθε : θ ≤ ε/4 := hθe.trans (min_le_left _ _)
  obtain ⟨η,dA,hη,hηθ,hdA,_,HA⟩ := capped_prisms_of_stage_alternative hε hθ hθε
  refine ⟨α,κ,η,min dG dA,hα,hκ,hη,hηθ.trans (hθε.trans (by linarith)),
    by positivity,(min_le_left _ _).trans hdG100,?_⟩
  intro d h ρ c n x v Y hd hdd hh hhη hA hJ
  have hdG' := hdd.trans (min_le_left _ _)
  have hd1 : d ≤ 1 := (hdG'.trans hdG100).trans (by norm_num)
  have hβ : 0 ≤ ω*ζ/100 := by positivity
  have hβ1 : ω*ζ/100 ≤ 1 := by
    have hζ1 : ζ ≤ 1 := by linarith
    nlinarith [mul_nonneg hω.le hζ.le]
  apply HA hd (hdd.trans (min_le_right _ _)) hhη hβ hβ1 hA hJ
  intro R hAR hJR
  rcases HG d θ hd hdG' hθ.le le_rfl n x v R hAR ρ c hJR with hg | ht | hp
  · exact Or.inl hg
  · exact Or.inr (Or.inl ⟨ρ,c,stage_mono hd hd1 (min_le_left _ _) ht⟩)
  · obtain ⟨ρ',hgrow,hG⟩ := hp
    have hρ : 0 ≤ ρ := by
      obtain ⟨S,Z,N,y,w,f,a,g,_,hbase,_⟩ := hJ
      exact (Real.rpow_pos_of_pos hd _).le.trans hbase
    exact Or.inr (Or.inr ⟨ρ',
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -ζ/400≤ -ζ/2000)) hρ).trans hgrow,
      WangZahlLot.Obl.wz_move_two_capped_prism_overlap.G_mono
        hd hd1 (min_le_left _ _) (le_refl 0) hG⟩)

/-- The full improvement alternative for aligned original fine axes. -/
theorem aligned_improvement {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω) (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000)
    (hε : 0 < ε) (hεζ : ε ≤ ζ/100) : AlignedImprovement σ ω ζ ε :=
  aligned_improvement_of_prisms hσ hσ2 hω hω1 hE hR hζ hζω hε hεζ
    (prism_improvement_of_estimate hσ hσ2 hω hω1 hE hζ hζω)

/-- A normalized aligned family either gains volume or admits the exact
coarse factorization used in the accepted multiscale theorem. -/
theorem aligned_one_scale {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω) : AlignedOneScale σ ω :=
  aligned_one_scale_of_prisms hσ hσ2 hω hω1 hE hR
    (fun ζ hζ hζω => prism_improvement_of_estimate hσ hσ2 hω hω1 hE hζ hζω)

/-- Accepted local rescaling supplies the auxiliary relative estimate. -/
theorem aligned_one_scale_of_estimate {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) : AlignedOneScale σ ω := by
  apply aligned_one_scale hσ hσ2 hω hω1 hE
  exact WangZahlLot.wz_rescaled_tube_estimate σ ω hσ hσ2 hω hω1
    O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl B rfl E rfl R rfl hE

end WangZahlLot.Obl.wz_broad_grains_improvement
