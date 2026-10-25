import Submission.Obl.k4_clean_cover_graph_atlas.Core

/-!
# The per-sample analytic statement

`CleanBody` is the body of `CleanCover` at fixed witnesses `i h n old R' A' V U`.

`SampleCore` is the analytic content of `FiniteCore`, one sample at a time. It fixes `θ` and a
slack ratio `ϖ` from the analytic hypotheses (before `L`, the grid and the gain). For every
`ρ ≤ ϖ` and every grid it gives the exponent `Mc`. For every allowance `β` and every choice of the
density tolerance `τ` and the input thresholds `ε₀ ≤ β / 2`, `σ₀ ≤ β / 8` with total slack
`ε₀ + σ₀ + τ ≤ ϖ · gain · L`, it gives a late-sample threshold `N₀`; past it, every path with a
cleaned cover (unpacked) has a `CoreOutput` at the cover's old level and gain.

The outer layer (`FiniteCore` from `SampleCore`) only chooses `ρ`, `τ`, `ε₀`, `σ₀`.
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory

/-- The body of `CleanCover` at fixed witnesses. -/
def CleanBody (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (d₁ ρ gain δ₀ : ℝ) (m : ℕ) (s r : ℕ → ℝ) (T : ℕ → ℕ)
    (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (τ ε : ℝ)
    (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
    (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (U : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z : ℕ, h = gain + (z : ℝ) * (ρ * gain)) ∧
    r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ a, lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧
      (R' a).totalDegree ≤ 2 ∧ (∀ e, |(R' a).coeff e| ≤ Nk ^ Mg) ∧
      MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
      (∀ l ∈ A' a,
        ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i)
          (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
          |MvPolynomial.eval (x l t) (R' a)| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧
          |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R' a))| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧
          |MvPolynomial.eval (x l t)
            (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R' a)))| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧
      MeasurableSet (V a) ∧
      V a ⊆ {p | p ∈ U (old a) ∧ p.1 ∈ A' a ∧
        p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i)
          (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
        B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤
          |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' a))|} ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) /
        (2 * (2 : ℝ) ^ T i)) * ν (γ (old a)) (A (old a)) ≤
          ((ν (γ (old a))).prod MeasureTheory.volume) (V a) ∧
      ENNReal.ofReal (Nk ^ (-f (r i)) * |Matrix.det (Q (old a))| /
        (2 * (2 : ℝ) ^ T i * κ)) ≤
          ((ν (γ (old a))).prod MeasureTheory.volume) (U (old a)) ∧
      (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map
          (obs (B (γ (old a))) (δ Nk (menuDepth L (s i) h δ₀))) ≤
        ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) h δ₀) + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count) ∧
      (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map
          (obs (B (γ (old a))) (δ Nk L)) ≤
        ENNReal.ofReal (Nk ^ (-f L + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧
    (∀ b, MeasurableSet (U b) ∧ U b ⊆ F b ∧
      (((ν (γ b)).prod MeasureTheory.volume).restrict (U b)).map
          (obs (B (γ b)) (δ Nk (menuDepth L (s i) 0 δ₀))) ≤
        ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) 0 δ₀) + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧
    (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
    (∀ b : Fin C, ((Finset.univ.filter (fun a => old a = b)).card : ℝ) ≤
      Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧
    (∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a')) ∧
    ENNReal.ofReal (Nk ^ (-ε) / 2) ≤
      ∑ a, ENNReal.ofReal (ω (γ (old a))) *
        ((ν (γ (old a))).prod MeasureTheory.volume) (V a)

theorem cleanCover_iff_cleanBody (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (d₁ ρ gain δ₀ : ℝ) (m : ℕ) (s r : ℕ → ℝ) (T : ℕ → ℕ)
    (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (τ ε : ℝ) :
    CleanCover Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε ↔
      ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
        (R' : Fin n → MvPolynomial (Fin 4) ℝ)
        (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
        (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
        (U : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
        CleanBody Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε
          i h n old R' A' V U :=
  Iff.rfl

/-- **The per-sample analytic statement** (see the module docstring). -/
def SampleCore : Prop :=
  localGraph → stableSheets → algebraicRemez →
  ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
  ∃ θ ϖ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < ϖ ∧
  ∀ ρ : ℝ, 0 < ρ → ρ ≤ ϖ → d₁ + ρ < 1 →
  ∀ (L : ℝ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), 0 < L →
    (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ Mp Dp Mg Dg Mpr Dpr : ℕ, ∃ Mc : ℕ,
  ∀ β τ ε₀ σ₀ : ℝ, 0 < β → β ≤ 1 → 0 < τ → 0 < ε₀ → ε₀ ≤ β / 2 → 0 < σ₀ → σ₀ ≤ β / 8 →
    ε₀ + σ₀ + τ ≤ ϖ * gain * L →
  ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
  ∀ (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ),
    ScalarData Nk Mpr Dpr W ω ν E B →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
  ∀ ε σ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < σ → σ ≤ σ₀ →
  ∀ r T nw κ C lev par γ j c u Q R A F lst,
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
  ∀ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (U : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    CleanBody Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε
      i h n old R' A' V U →
  ∃ s₀ K' : ℕ,
    (2 : ℝ) ^ (T i + s₀) ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * gain) * L / 2) ∧
    (2 : ℝ) ^ s₀ ≤ Nk ^ Mc ∧ (K' : ℝ) ≤ Nk ^ Mc ∧
    CoreOutput Nk L W ω ν E B (r i) h θ β Mc γ j c u Q R old R' A' (T i) s₀ K'

end Submission.Obl.k4_clean_cover_graph_atlas
