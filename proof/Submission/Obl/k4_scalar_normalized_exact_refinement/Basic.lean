import Submission.Obl.k4_scalar_normalized_exact_refinement.WorldTails

/-!
# Named access to the scalar data and to the Refinement certificate

`Code` is the Sigma type of the frozen statement, with reducible accessors. `RefData` is the
literal Refinement certificate with named fields; `RefData.ofRefinement` extracts it.
The `ChartData` and `RawScalar`/`PureProfile`/`Exact` facts used later are projected here.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

/-- The Sigma type of scalar problems of the frozen statement. -/
abbrev Code : Type :=
  Σ W : ℕ → ℕ, (ℕ → ℝ) × (ℕ → ℝ) × ℕ × ℕ × ℝ × ℝ × ℝ × ℝ × ((k : ℕ) → Fin (W k) → ℝ) ×
    ((k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ))) ×
    ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) ×
    ((k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) ×
    ((k : ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) × (ℝ → ℝ)

namespace Code

variable (p : Code)

abbrev W : ℕ → ℕ := p.1
abbrev N : ℕ → ℝ := p.2.1
abbrev K : ℕ → ℝ := p.2.2.1
abbrev M : ℕ := p.2.2.2.1
abbrev D : ℕ := p.2.2.2.2.1
abbrev L : ℝ := p.2.2.2.2.2.1
abbrev d : ℝ := p.2.2.2.2.2.2.1
abbrev S : ℝ := p.2.2.2.2.2.2.2.1
abbrev U : ℝ := p.2.2.2.2.2.2.2.2.1
abbrev ω : (k : ℕ) → Fin (p.1 k) → ℝ := p.2.2.2.2.2.2.2.2.2.1
abbrev ν : (k : ℕ) → Fin (p.1 k) → Measure Line := p.2.2.2.2.2.2.2.2.2.2.1
abbrev E : (k : ℕ) → Fin (p.1 k) → Set Inc := p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev ρ : (k : ℕ) → Fin (p.1 k) → ℝ → Base → ℝ≥0∞ := p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev ρA : (k : ℕ) → Fin (p.1 k) → ℝ → Joint → ℝ≥0∞ := p.2.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev f : ℝ → ℝ := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The selected incidence law of a world. -/
abbrev mu (k : ℕ) (a : Fin (p.1 k)) : Measure Inc := ((p.ν k a).prod volume).restrict (p.E k a)

end Code

lemma spec_mu_eq (p : Code) (k : ℕ) (a : Fin (p.1 k)) : Spec.mu p k a = p.mu k a := rfl

/-! ## Raw, pure and exact facts -/

section Facts

variable {p : Code}

lemma RawScalar.N_ge (h : Spec.RawScalar p) (k : ℕ) : 2 ≤ p.N k := h.1.1 k
lemma RawScalar.N_tendsto (h : Spec.RawScalar p) : Tendsto p.N atTop atTop := h.1.2.1
lemma RawScalar.K_ge (h : Spec.RawScalar p) (k : ℕ) : 1 ≤ p.K k := h.1.2.2.1.1 k
lemma RawScalar.K_sub (h : Spec.RawScalar p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε := h.1.2.2.1.2
lemma RawScalar.L_pos (h : Spec.RawScalar p) : 0 < p.L := h.1.2.2.2.2.2.1
lemma RawScalar.S_pos (h : Spec.RawScalar p) : 0 < p.S := h.1.2.2.2.2.2.2.2.2.1
lemma RawScalar.U_pos (h : Spec.RawScalar p) : 0 < p.U := h.1.2.2.2.2.2.2.2.2.2
lemma RawScalar.ω_nonneg (h : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) : 0 ≤ p.ω k a :=
  (h.2 k).2.1 a
lemma RawScalar.ω_sum (h : Spec.RawScalar p) (k : ℕ) : ∑ a, p.ω k a = 1 := (h.2 k).2.2.1
lemma RawScalar.ν_prob (h : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    IsProbabilityMeasure (p.ν k a) := ((h.2 k).2.2.2.1 a).1
lemma RawScalar.E_meas (h : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    MeasurableSet (p.E k a) := ((h.2 k).2.2.2.1 a).2.2.2.1
lemma RawScalar.E_time (h : Spec.RawScalar p) (k : ℕ) (a : Fin (p.1 k)) :
    p.E k a ⊆ univ ×ˢ Icc (0 : ℝ) 1 := ((h.2 k).2.2.2.1 a).2.2.2.2.1
lemma RawScalar.mass_lower (h : Spec.RawScalar p) (k : ℕ) :
    ENNReal.ofReal ((p.K k)⁻¹) ≤ ∑ a, ENNReal.ofReal (p.ω k a) * p.mu k a univ :=
  (h.2 k).2.2.2.2

lemma PureProfile.law (h : Spec.PureProfile p) (k : ℕ) (a : Fin (p.1 k)) (s : ℝ)
    (hs0 : 0 ≤ s) (hsL : s ≤ p.L) :
    Measurable (p.ρ k a s) ∧ (p.mu k a).map (obs (p.N k) s) = BaseRef.withDensity (p.ρ k a s) :=
  h.1 k a s hs0 hsL

lemma PureProfile.mono (h : Spec.PureProfile p) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (htL : t ≤ p.L) : 0 ≤ p.f t - p.f s ∧ p.f t - p.f s ≤ t - s :=
  h.2.1 s t hs hst htL

lemma PureProfile.typical (h : Spec.PureProfile p) (s τ : ℝ) (hs : 0 ≤ s) (hsL : s ≤ p.L)
    (hτ : 0 < τ) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ a, ENNReal.ofReal (p.ω k a) * p.mu k a {z | p.ρ k a s (obs (p.N k) s z) <
        ENNReal.ofReal (p.N k ^ (-p.f s - τ)) ∨
        ENNReal.ofReal (p.N k ^ (-p.f s + τ)) < p.ρ k a s (obs (p.N k) s z)}) ≤
        ENNReal.ofReal (p.N k ^ (-c)) :=
  h.2.2 s τ hs hsL hτ

lemma Exact.raw (h : Spec.Exact p) : Spec.RawScalar p := h.1
lemma Exact.pure (h : Spec.Exact p) : Spec.PureProfile p := h.2.1

lemma Exact.joint (h : Spec.Exact p) (k : ℕ) (a : Fin (p.1 k)) (u : ℝ) (hu : 0 < u)
    (huU : u ≤ p.U) :
    Measurable (p.ρA k a u) ∧
      (p.mu k a).map (aug (p.N k) p.L u) = JointRef.withDensity (p.ρA k a u) :=
  h.2.2.1 k a u hu huU

lemma Exact.cap (h : Spec.Exact p) (s : ℝ) (hs : 0 ≤ s) (hsL : s ≤ p.L) :
    p.f p.L - p.f s ≤ p.d * (p.L - s) := h.2.2.2.1 s hs hsL

lemma Exact.angular (h : Spec.Exact p) (u τ : ℝ) (hu : 0 < u) (huU : u ≤ p.U) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ a, ENNReal.ofReal (p.ω k a) * p.mu k a {z |
        ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
          p.ρA k a u (aug (p.N k) p.L u z)}) ≤ ENNReal.ofReal (p.N k ^ (-c)) :=
  h.2.2.2.2 u τ hu huU hτ

end Facts

/-! ## The Refinement certificate -/

/-- The literal Refinement certificate, with named fields. -/
structure RefData (p q : Code) (r b h : ℝ) where
  φ : ℕ → ℕ
  ε : ℕ → ℝ
  B : ℕ
  T : ℕ → ℕ
  γ : (k : ℕ) → Fin (q.1 k) → Fin (p.1 (φ k))
  j : (k : ℕ) → Fin (q.1 k) → Fin (2 ^ T k)
  A : (k : ℕ) → Fin (q.1 k) → Set (ℕ × (Fin 5 → ℝ))
  C : (k : ℕ) → Fin (q.1 k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  u : (k : ℕ) → Fin (q.1 k) → ℝ
  v : (k : ℕ) → Fin (q.1 k) → ℝ
  J : (k : ℕ) → Fin (q.1 k) → ℝ
  P : (k : ℕ) → Fin (q.1 k) → MvPolynomial (Fin 2) ℝ
  Λ : (k : ℕ) → Fin (p.1 (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (q.1 k))
  θ : (k : ℕ) → Fin (q.1 k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))
  mono : StrictMono φ
  ε_pos : ∀ k, 0 < ε k
  ε_lim : Tendsto ε atTop (nhds 0)
  B_ge : 1 ≤ B
  N_eq : ∀ k, q.2.1 k = p.2.1 (φ k)
  chart : ∀ k, Spec.ChartData p B r b (h + ε k) (ε k) false (φ k) (T k) (q.1 k) (γ k) (j k)
    (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)
  θ_meas : ∀ k i, Measurable (θ k i)
  θ_tag : ∀ k i l, (θ k i l).1 = l.1
  θ_y : ∀ k i l t, Spec.y (θ k i l) ((t - (((j k i : Fin (2 ^ T k)) : ℕ) : ℝ) *
      ((2 : ℝ) ^ T k)⁻¹) / ((2 : ℝ) ^ T k)⁻¹) = (Spec.y l t - u k i - t * v k i) / J k i
  θ_x : ∀ k i l t, Spec.x (θ k i l) ((t - (((j k i : Fin (2 ^ T k)) : ℕ) : ℝ) *
      ((2 : ℝ) ^ T k)⁻¹) / ((2 : ℝ) ^ T k)⁻¹) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] (P k i)) / p.2.1 (φ k) ^ (-r)
  ν_eq : ∀ k i, q.2.2.2.2.2.2.2.2.2.2.1 k i = (p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) (A k i))⁻¹ •
      Measure.map (θ k i) ((p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i)).restrict (A k i))
  mu_eq : ∀ k i, Spec.mu q k i = (ENNReal.ofReal ((2 : ℝ) ^ T k)⁻¹ *
      p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) (A k i))⁻¹ •
      Measure.map (fun z => (θ k i z.1, (z.2 - (((j k i : Fin (2 ^ T k)) : ℕ) : ℝ) *
        ((2 : ℝ) ^ T k)⁻¹) / ((2 : ℝ) ^ T k)⁻¹))
        ((Spec.mu p (φ k) (γ k i)).restrict (C k i))
  Z_pos : ∀ k, 0 < ∑ i : Fin (q.1 k), p.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) * ((2 : ℝ) ^ T k)⁻¹ *
      (p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) (A k i)).toReal
  ω_eq : ∀ k i, q.2.2.2.2.2.2.2.2.2.1 k i = (p.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) *
      ((2 : ℝ) ^ T k)⁻¹ * (p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) (A k i)).toReal) /
      ∑ i : Fin (q.1 k), p.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) * ((2 : ℝ) ^ T k)⁻¹ *
        (p.2.2.2.2.2.2.2.2.2.2.1 (φ k) (γ k i) (A k i)).toReal

theorem RefData.nonempty {p q : Code} {r b h : ℝ} (href : Spec.Refinement p q r b h) :
    Nonempty (RefData p q r b h) := by
  obtain ⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ, hmono, hε, hεlim, hB, hchart, hθ, hω⟩ :=
    href
  refine ⟨⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ, hmono, hε, hεlim, hB,
    fun k => (hchart k).1, fun k => (hchart k).2,
    fun k i => (hθ k i).1, fun k i => (hθ k i).2.1,
    fun k i => (hθ k i).2.2.1, fun k i => (hθ k i).2.2.2.1,
    fun k i => (hθ k i).2.2.2.2.1, fun k i => (hθ k i).2.2.2.2.2,
    fun k => (hω k).1, fun k i => (hω k).2 i⟩⟩

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
