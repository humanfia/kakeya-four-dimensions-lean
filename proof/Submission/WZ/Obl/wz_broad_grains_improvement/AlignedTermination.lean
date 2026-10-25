-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedTermination.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedFiniteIteration
import Submission.WZ.Obl.wz_broad_cover_slab_refinement
import Submission.WZ.Obl.wz_terminal_grains_restoration.Main
import Submission.WZ.Obl.wz_grains_alternative_remove_cutoff

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory

/-- The restored grain payload, including the relative slab bound. -/
abbrev RestoredGrains := WangZahlLot.Obl.wz_terminal_grains_restoration.Gp

/-- The accepted cutoff-removal theorem also applies to an alternative
restricted to aligned axes: put the alignment implication in its predicate. -/
theorem aligned_alternative_remove_cutoff {σ ω h : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hh : 0 < h)
    (U : (d : ℝ) → (n : ℕ) → (Fin n → V) → (Fin n → V) → (Fin n → Set V) → Prop)
    (hsmall : ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ 0<d₀ ∧ d₀≤1/100 ∧
      ∀ d : ℝ,0<d → d≤d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨ U d n x v Y) :
    ∃ α : ℝ,0<α ∧ ∃ κ : ℝ,0<κ ∧ ∃ η : ℝ,0<η ∧ η≤h ∧
      ∀ d : ℝ,0<d → d≤1/100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨ U d n x v Y := by
  classical
  have hs : ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ 0<d₀ ∧ d₀≤1/100 ∧
      ∀ d : ℝ,0<d → d≤d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        (AlignedAxes x v → U d n x v Y) := by
    obtain ⟨α,κ,η,d₀,hα,hκ,hη,hd₀,hd₀100,H⟩ := hsmall
    refine ⟨α,κ,η,d₀,hα,hκ,hη,hd₀,hd₀100,?_⟩
    intro d hd hdd n x v Y hA
    by_cases ha : AlignedAxes x v
    · rcases H d hd hdd n x v Y hA ha with hg | hu
      · exact Or.inl hg
      · exact Or.inr (fun _ => hu)
    · exact Or.inr (fun haxes => (ha haxes).elim)
  obtain ⟨α,hα,κ,hκ,η,hη,hηh,H⟩ := WangZahlLot.wz_grains_alternative_remove_cutoff
    σ ω hσ hσ2 hω hω1 O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl
    (fun d n x v Y => AlignedAxes x v → U d n x v Y) h hh hs
  refine ⟨α,hα,κ,hκ,η,hη,hηh,?_⟩
  intro d hd hd100 n x v Y hA haxes
  exact (H d hd hd100 n x v Y hA).imp_right (fun hu => hu haxes)

/-- Aligned finite termination followed by the accepted terminal-restoration
theorem yields the full grains alternative at all fine scales. -/
theorem aligned_grains_of_improvement {σ ω h : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hImprove : ∀ ζ : ℝ,0<ζ → ζ≤ω/1000 →
      ∀ ε : ℝ,0<ε → ε≤ζ/100 → AlignedImprovement σ ω ζ ε) (hh : 0 < h) :
    ∃ α : ℝ,0<α ∧ ∃ κ : ℝ,0<κ ∧ ∃ η : ℝ,0<η ∧ η≤h ∧
      ∀ d : ℝ,0<d → d≤1/100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ S Z ρ N y w f,RestoredGrains ω d h n x v Y S Z ρ N y w f := by
  have hRefine : ∀ β : ℝ,0<β → ∀ τ : ℝ,0<τ →
      WangZahlLot.Obl.wz_terminal_grains_restoration.Rp σ ω β τ :=
    WangZahlLot.wz_broad_cover_slab_refinement σ ω hσ hσ2 hω hω1
      O rfl q rfl I rfl T rfl Q rfl X rfl K rfl F rfl A rfl C rfl B rfl E rfl
      WangZahlLot.Obl.wz_terminal_grains_restoration.Rp rfl hE
  obtain ⟨ζ,αR,κR,ηR,dR,hζ,hζω,hαR,hκR,hηR,_,hdR,_,HR⟩ :=
    WangZahlLot.Obl.wz_terminal_grains_restoration.main σ ω hσ hσ2 hω hω1 hRefine h hh
  obtain ⟨αT,κT,ηT,dT,hαT,hκT,hηT,hηTηR,hdT,hdT100,HT⟩ :=
    aligned_terminal_of_improvement hσ hσ2 hω hω1 hE hζ hζω hηR (hImprove ζ hζ hζω)
  apply aligned_alternative_remove_cutoff hσ hσ2 hω hω1 hh
    (fun d n x v Y => ∃ S Z ρ N y w f,RestoredGrains ω d h n x v Y S Z ρ N y w f)
  refine ⟨min αT αR,min κT κR,ηT,min dT dR,by positivity,by positivity,hηT,
    by positivity,(min_le_left _ _).trans hdT100,?_⟩
  intro d hd hdd n x v Y hA haxes
  have hdT' := hdd.trans (min_le_left _ _)
  have hdR' := hdd.trans (min_le_right _ _)
  have hd1 : d ≤ 1 := (hdT'.trans hdT100).trans (by norm_num)
  have hgainT := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
    (min_le_left αT αR) (min_le_left κT κR) (le_min hκT.le hκR.le)
  have hgainR := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1
    (min_le_right αT αR) (min_le_right κT κR) (le_min hκT.le hκR.le)
  rcases HT d hd hdT' n x v Y hA haxes with hg | ⟨ρ,c,hD⟩
  · exact Or.inl (hgainT.trans hg)
  · rcases HR d hd hdR' n x v Y (admissible_mono hd hd1 hηTηR hA) ρ c hD with hg | hG
    · exact Or.inl (hgainR.trans hg)
    · exact Or.inr hG

/-- The only geometric premise needed by the aligned grains alternative is
the uncapped prism improvement endpoint. -/
theorem aligned_grains_of_prisms {σ ω h : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hR : R σ ω)
    (hPrism : ∀ ζ : ℝ,0<ζ → ζ≤ω/1000 → PrismImprovement σ ω ζ) (hh : 0 < h) :
    ∃ α : ℝ,0<α ∧ ∃ κ : ℝ,0<κ ∧ ∃ η : ℝ,0<η ∧ η≤h ∧
      ∀ d : ℝ,0<d → d≤1/100 → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ S Z ρ N y w f,RestoredGrains ω d h n x v Y S Z ρ N y w f := by
  apply aligned_grains_of_improvement hσ hσ2 hω hω1 hE _ hh
  intro ζ hζ hζω ε hε hεζ
  exact aligned_improvement_of_prisms hσ hσ2 hω hω1 hE hR hζ hζω hε hεζ (hPrism ζ hζ hζω)

end WangZahlLot.Obl.wz_broad_grains_improvement
