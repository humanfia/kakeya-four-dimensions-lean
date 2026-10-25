import Submission.Obl.k4_finite_path_candidate_conversion.PrepDiagonal

/-! The preparation child states one finite prepared model with explicit
Mathlib fields. The bridge repacks those fields for the proved diagonal. -/

namespace Submission.Obl.k4_finite_path_candidate_conversion

noncomputable section

def FlatStageModel (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mc : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧
          H w ⊆ TerminalInc (W k) C m lev γ F w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod MeasureTheory.volume) (TerminalInc (W k) C m lev γ F w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
        ∃ (sN sK : ℝ) (sν : MeasureTheory.Measure Trajectory)
          (sμ sρ : MeasureTheory.Measure Incidence) (sπ : MeasureTheory.Measure ℝ)
          (sb : Trajectory → Fin 6 → ℝ) (sP : MvPolynomial (Fin 4) ℝ)
          (sT sn : ℝ → ℕ) (sj : (s : ℝ) → Fin (sn s) → Fin (2 ^ sT s))
          (sA sB : (s : ℝ) → Fin (sn s) → Set Trajectory)
          (sc : (s : ℝ) → Fin (sn s) → Fin 5 → ℝ)
          (sF : (s : ℝ) → Fin (sn s) → MvPolynomial (Fin 4) ℝ),
          (n : ℝ) + 2 ≤ sN ∧ (1 ≤ sK ∧ sK ≤ sN ^ (1 / ((n : ℝ) + 1))) ∧
          (Measurable (sb) ∧ MeasureTheory.IsProbabilityMeasure (sν) ∧ MeasureTheory.IsProbabilityMeasure (sπ) ∧ sμ ≤ ENNReal.ofReal (sK) • ((sν).prod MeasureTheory.volume) ∧ sρ ≤ sμ ∧ sμ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((sK)⁻¹) ≤ sρ Set.univ ∧ (sP).totalDegree ≤ 2 ∧ (∀ᵐ l ∂sν, |sb l 0| + |sb l 1| + |sb l 3| + |sb l 4| ≤ sK) ∧ (∀ᵐ p ∂sμ, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (exS sb p.1 t) (sP)| ≤ sK ∧ |MvPolynomial.eval (exS sb p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (sP))| ≤ sK ∧ |MvPolynomial.eval (exS sb p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (sP)))| ≤ sK) ∧ (sK)⁻¹ ≤ |MvPolynomial.eval (exS sb p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (sP))|)) ∧
          (∀ R : ℝ, 1 < R → R ≤ n → (∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, sπ {w : ℝ | ⌊w / (sN ^ (-v))⌋ = a} ≤ ENNReal.ofReal (sK * sN ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), sμ {p | zS sb (sN) r p = q ∧ ⌊(if h then MvPolynomial.eval (exS sb p.1 p.2) (sP) else (exS sb p.1 p.2) 3) / (sN ^ (-s))⌋ = a} ≤ ENNReal.ofReal (sK * sN ^ (-3 * r - d₁ * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), sμ {p | zS sb (sN) r p = q ∧ ⌊(if h then MvPolynomial.eval (exS sb p.1 p.2) (sP) else (exS sb p.1 p.2) 3) / (sN ^ (-s))⌋ = a ∧ ⌊sb p.1 3 / (sN ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (sK * sN ^ (-3 * r - d₁ * s)) * sπ {w : ℝ | ⌊w / (sN ^ (-v))⌋ = v₀})) ∧ (∀ s : ℝ, R⁻¹ ≤ s → s ≤ (1 : ℝ) → (fun (q : ℝ) (a g : ℝ → ℝ) => sN ^ (κ₁ * s) / sK ≤ (2 : ℝ) ^ sT s ∧ (2 : ℝ) ^ sT s ≤ sK * sN ^ (κ₁ * s) ∧ (∀ i, MeasurableSet (sA s i) ∧ MeasurableSet (sB s i) ∧ sB s i ⊆ sA s i) ∧ (∀ i i', i ≠ i' → sj s i = sj s i' → Disjoint (sA s i) (sA s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d₁ * q ^ 2 * g s / sK) ≤ sν (sA s i) ∧ sν (sA s i) ≤ ENNReal.ofReal (sK * a s ^ d₁ * q ^ 2 * g s) ∧ ENNReal.ofReal (q / sK) * sν (sA s i) ≤ sμ (sB s i ×ˢ IS (sT s) (sj s i)) ∧ (∀ e, |sc s i e| ≤ sK) ∧ (sF s i).totalDegree ≤ 2 ∧ (∀ l ∈ sA s i, ∀ t ∈ IS (sT s) (sj s i), |(exS sb l t) 1 - sc s i 0 - t * sc s i 1| ≤ sK * q ∧ |(exS sb l t) 2 - sc s i 2 - t * sc s i 3 - sc s i 4 * (exS sb l t) 1| ≤ sK * q * g s ∧ |sb l 4 - sc s i 3 - sc s i 4 * sb l 3| ≤ sK * g s) ∧ (∀ l ∈ sB s i, fitS sb (sK) (a s) (sF s i) l (IS (sT s) (sj s i))) ∧ (∀ᵐ p ∂sμ, p.1 ∈ sB s i → p.2 ∈ IS (sT s) (sj s i) → (sK)⁻¹ ≤ |MvPolynomial.eval (exS sb p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (sF s i))|) ∧ (false = true → sP = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂sμ, |sb p.1 4 + sb p.1 0| ≤ sN ^ (-(1 : ℝ))) ∧ |sc s i 3 + sc s i 0 + ((sj s i : ℕ) + (1 : ℝ) / 2) * q * sc s i 1| + |sc s i 4 - ((sj s i : ℕ) + (1 : ℝ) / 2) * q| ≤ sK * q ∧ (∃ L : Fin 4 → ℝ, sF s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ sK * (1 + a s / q ^ 2) ∧ ∀ l ∈ sB s i, ∀ t ∈ IS (sT s) (sj s i), |L 1 - (exS sb l t) 1 * L 3| + |L 2 + t * L 3| ≤ sK * (1 + a s / q)))) ∧ (∀ᵐ p ∂sμ, ∃ i, p.1 ∈ sB s i ∧ p.2 ∈ IS (sT s) (sj s i)) ∧ (∀ (i : Fin (sn s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → sμ {p | p.1 ∈ sB s i ∧ p.2 ∈ IS (sT s) (sj s i) ∧ ⌊sb p.1 3 / (sN ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (sK * q) * sν (sA s i) * sπ {w : ℝ | ⌊w / (sN ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(sT s : ℤ))) (fun s => sN ^ (-s)) (fun s => sN ^ (-ℓ * s))) ∧ (∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ (1 : ℝ) → ∀ i : Fin (sn t), ∃ h : Fin (sn s), sA t i ⊆ sA s h ∧ IS (sT t) (sj t i) ⊆ IS (sT s) (sj s h))) ∧
          (∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
            (∃ (s v : ℝ) (i : Fin (sn s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ (1 : ℝ) ∧ ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ sN ^ R * ((1 + ∑ e ∈ (sF s i).support, |(sF s i).coeff e|) + ∑ e ∈ (sP).support, |(sP).coeff e|) ^ R) ∧ ENNReal.ofReal (sN ^ (-d₁ * v - ε') / (2 : ℝ) ^ sT s) * sν (sA s i) ≤ sρ {p | p.1 ∈ sB s i ∧ p.2 ∈ IS (sT s) (sj s i) ∧ fitS sb (sN ^ ε') (sN ^ (-s - v)) Q p.1 (IS (sT s) (sj s i)) ∧ sN ^ (-ε') ≤ |MvPolynomial.eval (exS sb p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}) ∨ (∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ sN ^ R) ∧ ENNReal.ofReal (sN ^ (-ε') / (2 : ℝ) ^ sT s) * sν (sA s i) ≤ sρ {p | p.1 ∈ sB s i ∧ p.2 ∈ IS (sT s) (sj s i) ∧ |sb p.1 4 - z 0 - z 1 * sb p.1 3| ≤ sN ^ ε' * sN ^ (-ℓ * s - v)}))) →
            MixedCandidate (N k) L (W k) (ν k) (B k) Mc d₁ ρ gain ε
              r T C lev γ j u Q A H)

def FlatStageReady (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) : Prop :=
  ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
    FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
      FlatStageModel d₁ κ₁ ℓ S η ρ n m s gain δ₀

def FinitePreparationStatement : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, FlatStageReady d₁ κ₁ ℓ S η ρ n

theorem stageModels_of_flat (h : FinitePreparationStatement) : StageModels := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS1 hη hρ hρ' n
  obtain ⟨m, s, gain, δ₀, hgrid, hg, hg', hδ, hδ', hf⟩ :=
    h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS1 hη hρ hρ' n
  refine ⟨m, s, gain, δ₀, hgrid, hg, hg', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprofile Mp Dp
  obtain ⟨Mc, hf⟩ := hf N K L d W ω ν E P B f g G hprob hprofile Mp Dp
  refine ⟨Mc, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, hf⟩ := hf ε hε
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hHm
  obtain ⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF,
    hN, hK, h1, h234, hret⟩ :=
    hf k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hHm
  exact ⟨⟨sN, sK, sν, sμ, sρ, sπ, sb, sP, sT, sn, sj, sA, sB, sc, sF⟩,
    ⟨hN, hK, h1, h234⟩, hret⟩

end

end Submission.Obl.k4_finite_path_candidate_conversion
