import Submission.Obl.k4_finite_path_candidate_conversion.Stages

/-!
The finite quantifier bookkeeping for the split. All difficult geometric
steps are premises. A common smaller input loss and later cutoff let the
greedy and realization interfaces use exactly the same supplied path.
-/

namespace Submission.Obl.k4_finite_path_candidate_conversion

noncomputable section

/-- Decreasing the input power loss preserves the supplied positive-narrowness path. -/
theorem positivePath_mono {ℓ Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ}
    {σ σ' : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ}
    {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C} {γ : Fin C → Fin W}
    {j : Fin C → ℕ} {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set Trajectory} {F : Fin C → Set Incidence}
    {lst : ℕ → Fin W → Observation → Finset (Fin C)}
    (hNk : 1 ≤ Nk) (hσ : σ ≤ σ')
    (h : PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst) :
    PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ'
      r T nw κ C lev par γ j c u Q R A F lst := by
  exact ⟨h.1, h.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNk hσ), h.2.2⟩

/-- The three smaller interfaces prove the exact frozen conclusion. -/
theorem assemble (hprep : PreparationStatement) (hgreedy : GreedyStatement)
    (hrealize : RealizationStatement) :
    Matching → CandidatePrinciple false (fun _ => True) → FiniteImprovement := by
  intro hmatch hengine d₁ κ₁ ℓ S η hd₀ hd₁ hκ₀ hκ₁ _hℓ₀ hS hη hℓ hS₁
  obtain ⟨α, ρ, hα, _hα₁, hρ, hρ₁, _hdρ, hrealize⟩ :=
    hrealize hmatch d₁ κ₁ ℓ S η hd₀ hd₁ hκ₀ hκ₁ hℓ hS hS₁ hη
  obtain ⟨m, s, gain, δ₀, hgrid, hgain, hgain₁, hδ₀, hδρ, hdiscover⟩ :=
    hprep hengine d₁ κ₁ ℓ S η ρ hd₀ hd₁ hκ₀ hκ₁ hℓ hS hS₁ hη hρ hρ₁
  refine ⟨m, s, hgrid.1.1, hgrid.1.2.1, hgrid.1.2.2.1, hgrid.1.2.2.2,
    α * gain, δ₀, mul_pos hα hgain, hδ₀, ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprofile Mp Dp
  change prob N K L d S η W ω ν E P B f g G at hprob
  obtain ⟨Mg, Dg, hcover⟩ :=
    hgreedy d₁ κ₁ ℓ S η ρ hd₀ hd₁ hκ₀ hκ₁ hℓ hS hS₁ hη hρ hρ₁
      m s gain δ₀ hgrid hgain hgain₁ hδ₀ hδρ hdiscover
      N K L d W ω ν E P B f g G hprob hprofile Mp Dp
  obtain ⟨Mi, Di, houtput⟩ :=
    hrealize m s gain δ₀ hgrid hgain hgain₁ hδ₀ hδρ
      N K L d W ω ν E P B f g G hprob hprofile Mp Dp Mg Dg
  refine ⟨Mi, Di, ?_⟩
  intro τ hτ
  obtain ⟨ε, σr, hε, hε₁, hσr, kr, hr⟩ := houtput τ hτ
  obtain ⟨σg, hσg, kg, hg⟩ := hcover ε hε hε₁
  refine ⟨min σg σr, lt_min hσg hσr, max kg kr, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst
    hκlow hκup hC hend hlevels hlists hdisjoint hcharts
  have hNk : 1 ≤ N k := le_trans (by norm_num) (hprob.1 k)
  have hpath : PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f
      κ₁ m s δ₀ Mp Dp (min σg σr) r T nw κ C lev par γ j c u Q R A F lst :=
    ⟨hκlow, hκup, hC, hend, hlevels, hlists, hdisjoint, hcharts⟩
  have hcovered := hg k ((le_max_left kg kr).trans hk)
    r T nw κ C lev par γ j c u Q R A F lst
    (positivePath_mono hNk (min_le_left σg σr) hpath)
  exact hr k ((le_max_right kg kr).trans hk)
    r T nw κ C lev par γ j c u Q R A F lst
    (positivePath_mono hNk (min_le_right σg σr) hpath) hcovered

end

end Submission.Obl.k4_finite_path_candidate_conversion
