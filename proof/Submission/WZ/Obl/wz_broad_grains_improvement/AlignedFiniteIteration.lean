-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedFiniteIteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedImprovement
import Submission.WZ.Obl.wz_broad_grains_improvement.GrainPotential
import Submission.WZ.Obl.wz_broad_grains_initialization.Initialization

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory

/-- Backward induction on the remaining potential range chooses all error
budgets uniformly, while keeping the alignment of the fixed fine axes. -/
theorem aligned_terminal_of_potential_bound {σ ω ζ : ℝ}
    (hζ : 0 < ζ) (hζmax : ζ ≤ 2000)
    (hImprove : ∀ ε : ℝ,0<ε → ε≤ζ/100 → AlignedImprovement σ ω ζ ε) (N : ℕ) :
    ∀ ε : ℝ,0<ε → ε≤ζ/100 →
    ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ η≤ε ∧ 0<d₀ ∧ d₀≤1/100 ∧
      ∀ d : ℝ,0<d → d≤d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      ∀ ρ c,D ω ζ d η ρ c n x v Y false →
        -(N:ℝ)*grainIncrement ζ d ≤ grainPotential ζ ρ c →
        O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
          ∃ ρ' c',D ω ζ d ε ρ' c' n x v Y true := by
  induction N with
  | zero =>
    intro ε hε hεζ
    obtain ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀100,H⟩ := hImprove ε hε hεζ
    refine ⟨α,κ,η,d₀,hα,hκ,hη,hηε,hd₀,hd₀100,?_⟩
    intro d hd hdd n x v Y hA haxes ρ c hD hpot
    have hd1 : d < 1 := (hdd.trans hd₀100).trans_lt (by norm_num)
    have hinc := grain_increment_pos hζ hd hd1
    rcases H d hd hdd n x v Y hA haxes ρ c hD with hg | ht | hp
    · exact Or.inl hg
    · exact Or.inr ht
    · obtain ⟨ρ',c',hD',hprog⟩ := hp
      have hstep := grain_potential_progress hζ hζmax hd hd1 hD hD' hprog
      have htop := (grain_potential_bounds hζ.le hd hD').2
      norm_num only [Nat.cast_zero,neg_zero,zero_mul] at hpot
      exact (by linarith : False).elim
  | succ N ih =>
    intro ε hε hεζ
    obtain ⟨αR,κR,ηR,dR,hαR,hκR,hηR,hηRε,hdR,_,HR⟩ := ih ε hε hεζ
    obtain ⟨αI,κI,ηI,dI,hαI,hκI,hηI,hηIηR,hdI,hdI100,HI⟩ :=
      hImprove ηR hηR (hηRε.trans hεζ)
    refine ⟨min αI αR,min κI κR,ηI,min dI dR,by positivity,by positivity,hηI,
      hηIηR.trans hηRε,by positivity,(min_le_left _ _).trans hdI100,?_⟩
    intro d hd hdd n x v Y hA haxes ρ c hD hpot
    have hdI' := hdd.trans (min_le_left _ _)
    have hdR' := hdd.trans (min_le_right _ _)
    have hd1 : d < 1 := (hdI'.trans hdI100).trans_lt (by norm_num)
    have hgainI := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1.le
      (min_le_left αI αR) (min_le_left κI κR) (le_min hκI.le hκR.le)
    have hgainR := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1.le
      (min_le_right αI αR) (min_le_right κI κR) (le_min hκI.le hκR.le)
    rcases HI d hd hdI' n x v Y hA haxes ρ c hD with hg | ht | hp
    · exact Or.inl (hgainI.trans hg)
    · obtain ⟨ρ',c',hD'⟩ := ht
      exact Or.inr ⟨ρ',c',terminal_mono hd hd1.le hηRε hD'⟩
    · obtain ⟨ρ',c',hD',hprog⟩ := hp
      have hstep := grain_potential_progress hζ hζmax hd hd1 hD hD' hprog
      have hpot' : -(N:ℝ)*grainIncrement ζ d ≤ grainPotential ζ ρ' c' := by
        push_cast at hpot
        nlinarith only [hpot,hstep]
      rcases HR d hd hdR' n x v Y (admissible_mono hd hd1.le hηIηR hA)
          haxes ρ' c' hD' hpot' with hg | ht
      · exact Or.inl (hgainR.trans hg)
      · exact Or.inr ht

/-- Initialization and aligned improvement terminate after uniformly many
steps, because the logarithmic potential has a bounded range. -/
theorem aligned_terminal_of_improvement {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω)
    (hζ : 0 < ζ) (hζω : ζ ≤ ω/1000) (hε : 0 < ε)
    (hImprove : ∀ e : ℝ,0<e → e≤ζ/100 → AlignedImprovement σ ω ζ e) :
    ∃ α κ η d₀ : ℝ,0<α ∧ 0<κ ∧ 0<η ∧ η≤ε ∧ 0<d₀ ∧ d₀≤1/100 ∧
      ∀ d : ℝ,0<d → d≤d₀ → ∀ n (x v : Fin n → V) (Y : Fin n → Set V),
      A d η (d^(-η)) (d^(-η)) n x v Y → AlignedAxes x v →
      O (κ*d^(ω-α)*(n*d^2)*(n*d)^(-σ)) ≤ volume (⋃ i,Y i) ∨
        ∃ ρ c,D ω ζ d ε ρ c n x v Y true := by
  have hζmax : ζ ≤ 2000 := by linarith
  have hq : 0 < ζ*(ζ/2000) := by positivity
  obtain ⟨N,hN⟩ := exists_nat_gt ((4+ζ)/(ζ*(ζ/2000)))
  have hNbound : 4+ζ ≤ (N:ℝ)*(ζ*(ζ/2000)) :=
    ((div_lt_iff₀ hq).mp hN).le
  have he : 0 < min ε (ζ/100) := by positivity
  obtain ⟨αT,κT,ηT,dT,hαT,hκT,hηT,hηTe,hdT,hdT100,HT⟩ :=
    aligned_terminal_of_potential_bound hζ hζmax hImprove N
      (min ε (ζ/100)) he (min_le_right _ _)
  obtain ⟨αI,κI,ηI,dI,hαI,hκI,hηI,hηIηT,hdI,_,HI⟩ :=
    WangZahlLot.Obl.wz_broad_grains_initialization.initialization hσ hσ2 hω hω1 hE hζ hζω hηT
  refine ⟨min αI αT,min κI κT,ηI,min dT dI,by positivity,by positivity,hηI,
    (hηIηT.trans hηTe).trans (min_le_left _ _),by positivity,
    (min_le_left _ _).trans hdT100,?_⟩
  intro d hd hdd n x v Y hA haxes
  have hdT' := hdd.trans (min_le_left _ _)
  have hdI' := hdd.trans (min_le_right _ _)
  have hd1 : d < 1 := (hdT'.trans hdT100).trans_lt (by norm_num)
  have hgainI := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1.le
    (min_le_left αI αT) (min_le_left κI κT) (le_min hκI.le hκT.le)
  have hgainT := gain_mono (ω := ω) (σ := σ) (n := n) hd hd1.le
    (min_le_right αI αT) (min_le_right κI κT) (le_min hκI.le hκT.le)
  rcases HI d hd hdI' n x v Y hA with hg | ⟨ρ,c,hD⟩
  · exact Or.inl (hgainI.trans hg)
  · have hpot : -(N:ℝ)*grainIncrement ζ d ≤ grainPotential ζ ρ c := by
      apply le_trans (b := (4+ζ)*Real.log d) _ (grain_potential_bounds hζ.le hd hD).1
      have hh := mul_le_mul_of_nonpos_right hNbound (Real.log_neg hd hd1).le
      dsimp [grainIncrement]
      nlinarith only [hh]
    rcases HT d hd hdT' n x v Y (admissible_mono hd hd1.le hηIηT hA) haxes ρ c hD hpot with
        hg | ⟨ρ',c',hD'⟩
    · exact Or.inl (hgainT.trans hg)
    · exact Or.inr ⟨ρ',c',terminal_mono hd hd1.le (min_le_left _ _) hD'⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
