import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Interface

/-!
Concrete interfaces used by the o117 decomposition. The frozen children's
statements expand every definition below using only Mathlib and ChallengeDeps.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_quadratic_candidate_atlas_conversion
noncomputable section

def localGraph : Prop :=
  (∀ D : ℕ, ∀ d₀ : ℝ, 0 ≤ d₀ → d₀ < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ → ∀ n₁ n₂ : ℕ, ∀ (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ) (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ) (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ) (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))), (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) => (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) → (∀ i, P₁ i ≠ 0 ∧ (P₁ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₁ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₁ i z)) (P₁ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₁ i (emb x)).im = 0 ∧ ‖f₁ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, P₂ i ≠ 0 ∧ (P₂ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₂ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₂ i z)) (P₂ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₂ i (emb x)).im = 0 ∧ ‖f₂ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 → ENNReal.ofReal (R ^ (-ε)) ≤ μ Set.univ → μ Set.univ ≤ 1 → (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * MeasureTheory.volume U) → (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * MeasureTheory.volume U) → ¬ μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε) ∧ ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧ M * R ^ (-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}ᶜ = 0) (fun x => WithLp.toLp 2 (fun i => (x i : ℂ))))

def algebraicJets : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ K : ℕ, 1 ≤ K ∧
    ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), (∀ v ∈ V, ‖v‖ = 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
    ∀ (f : EuclideanSpace ℂ (Fin 3) → ℂ) (P : MvPolynomial (Fin 4) ℂ),
    P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) P = 0) →
    (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) =>
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f (emb x)).im = 0) →
      (∀ A : ℝ, 0 < A → (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖f (emb x)‖ ≤ A) →
        ∀ v ∈ V, ∀ m : ℕ, m ≤ K → |iteratedDeriv m (fun t : ℝ => (f (emb (t • v))).re) 0| ≤ B m * A) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
        c * ‖f (emb x)‖ ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1),
          |iteratedDeriv j (fun t : ℝ => (f (emb (t • v))).re) 0|)
      (fun x => WithLp.toLp 2 (fun j => (x j : ℂ)))

def stableSheets : Prop :=
  ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit a : ℝ), 2 ≤ A → 0 < a_fit →
    ∀ (b c : MvPolynomial (Fin 3) ℝ), b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
    (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
    |a| * a_fit ≤ A ^ (-20 : ℝ) →
    ∀ (u₀ : EuclideanSpace ℝ (Fin 3)) (w₀ : ℝ), ‖u₀‖ ≤ A →
    |a * w₀ ^ 2 + MvPolynomial.eval (fun j => u₀ j) b * w₀ + MvPolynomial.eval (fun j => u₀ j) c| ≤ a_fit * A →
    A ^ (-1 : ℝ) ≤ |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| →
    |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| ≤ A →
    ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
      DifferentiableOn ℂ f (Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ)))) ∧
      (∀ z ∈ Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ))),
        (a : ℂ) * (f z) ^ 2 + MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) b * f z +
          MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) c = 0) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < A ^ (-(C : ℝ)) →
        (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).im = 0 ∧
        A ^ (-(C : ℝ)) ≤ |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ∧
        |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ≤ A ^ (C : ℝ) ∧
        0 < (2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b) *
          (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b)) ∧
      (∀ (u : EuclideanSpace ℝ (Fin 3)) (w : ℝ), ‖u - u₀‖ < A ^ (-(C : ℝ)) →
        |a * w ^ 2 + MvPolynomial.eval (fun j => u j) b * w + MvPolynomial.eval (fun j => u j) c| ≤ a_fit * A →
        0 < (2 * a * w + MvPolynomial.eval (fun j => u j) b) * (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b) →
        |w - (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re| ≤ a_fit * A ^ (C : ℝ))

def algebraicRemez : Prop :=
  ∀ n D : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : MvPolynomial (Fin (n + 1)) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z)) P = 0) →
    (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → (f (WithLp.toLp 2 (fun j => (x j : ℂ)))).im = 0) →
    ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ), MeasurableSet E →
    E ⊆ Metric.closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
    ENNReal.ofReal θ * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ MeasureTheory.volume E →
    (∀ x ∈ E, ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ V) →
    ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
      ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ C * θ ^ (-C) * V

def greedyCover (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ)
    (d₁ ρ gain : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (ε : ℝ) : Prop :=
  ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
      (R' : Fin n → MvPolynomial (Fin 4) ℝ)
      (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
      (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z : ℕ, h = gain + (z : ℝ) * (ρ * gain)) ∧
    r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ a, lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧
      (R' a).totalDegree ≤ 2 ∧ (∀ e, |(R' a).coeff e| ≤ Nk ^ Mg) ∧
      MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
      (∀ l ∈ A' a, ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
        |MvPolynomial.eval (x l t) (R' a)| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R' a))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R' a)))| ≤ Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧
      MeasurableSet (V a) ∧ V a ⊆ {p | (∃ b : Fin C, lev b = m - 1 ∧ γ b = γ (old a) ∧ p ∈ F b) ∧
        p.1 ∈ A' a ∧ p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i) (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
        B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' a))|} ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) / (2 : ℝ) ^ T i) * ν (γ (old a)) (A (old a)) ≤
        ((ν (γ (old a))).prod MeasureTheory.volume) (V a)) ∧
    (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
    (∀ b : Fin C, ((Finset.univ.filter (fun a => old a = b)).card : ℝ) ≤ Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧
    (∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a')) ∧
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ a, ENNReal.ofReal (ω (γ (old a))) * ((ν (γ (old a))).prod MeasureTheory.volume) (V a)

def preImprovementAt (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (κ₁ Δ : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ (r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
      (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
      (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ)
      (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
      (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    r₂ + Δ * L ≤ L ∧
    ((Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ Nk ^ (κ₁ * Δ * L / 2)) ∨
      ∃ i, i < m ∧ r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * Δ * L / 2)) ∧
    (C₂ : ℝ) ≤ Nk ^ M ∧
    (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧
    (∀ w o, ((lst₂ w o).card : ℝ) ≤ Nk ^ ε) ∧
    (∀ w b, MeasurableSet {o | b ∈ lst₂ w o}) ∧
    (∀ b, chart Nk M D (Nk ^ ε) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True) ∧
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume)
      {p | p ∈ F₂ b ∧ b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)}

def temperedLaw (Nk : ℝ) (M D W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ Nk ^ M ∧ (∀ w, 0 ≤ ω w) ∧ (∑ w, ω w) = 1 ∧
    ∀ w, MeasureTheory.IsProbabilityMeasure (ν w) ∧ 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M ∧
      ∃ n : ℕ, (n : ℝ) ≤ Nk ^ M ∧ ∃ (c : Fin n → ℝ) (copy : Fin n → ℕ) (S : Fin n → Set (Fin 6 → ℝ)),
        (∀ a, 0 ≤ c a ∧ c a ≤ Nk ^ M ∧ (copy a : ℝ) ≤ Nk ^ M ∧ fmt 6 (Nk ^ M) D (S a) ∧
          (∀ z ∈ S a, ∀ e, |z e| ≤ Nk ^ M)) ∧
        ν w = ∑ a, ENNReal.ofReal (c a) • MeasureTheory.Measure.map (fun z => (copy a, z)) (MeasureTheory.volume.restrict (S a))

def GreedyCoverage : Prop :=
  ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain → discovery d₁ κ₁ S η ρ m s gain δ₀ →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mg Dg : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst,  path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      width (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mg Dg ε ∨ greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε

def AnalyticalConversion : Prop :=
  localGraph → algebraicJets → stableSheets → algebraicRemez →
    ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    ∃ α ρ : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < ρ ∧ d₁ + ρ < 1 ∧
    ∀ S η : ℝ, 0 < S → 0 < η →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp Mg Dg : ℕ, ∃ Mi Di : ℕ, ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
    ∃ ε σ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ ζ ∧ 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst,  path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst → greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε →
      preImprovementAt (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain) m r T nw Mi Di ζ

def OriginalEncoding : Prop :=
  ∀ L : ℝ, 0 < L → ∀ Mν Dν M D : ℕ, ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
    ∀ (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
      (B : Fin W → ℝ) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    temperedLaw Nk Mν Dν W ω ν B →
    ∀ (ε r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
      (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
      (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ)
      (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
      (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    0 < ε → ε ≤ τ / 4 → ε ≤ 1 / 8 → (C₂ : ℝ) ≤ Nk ^ M →
    (∀ w o, ((lst₂ w o).card : ℝ) ≤ Nk ^ ε) →
    (∀ w b, MeasurableSet {o | b ∈ lst₂ w o}) →
    (∀ b, chart Nk M D (Nk ^ ε) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True) →
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume)
      {p | p ∈ F₂ b ∧ b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)} →
    ∃ (F' : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
      (∀ b, F' b ⊆ F₂ b) ∧ (∀ w o, ((lst' w o).card : ℝ) ≤ Nk ^ τ) ∧
      (∀ b, chart Nk M' D' (Nk ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F' b)
        (∀ p ∈ F' b, b ∈ lst' (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p))) ∧
      ENNReal.ofReal (Nk ^ (-τ)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume) (F' b)

end
end Submission.Obl.k4_quadratic_candidate_atlas_conversion
