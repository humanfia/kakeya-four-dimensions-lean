-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/EStages.lean.
import Mathlib

/-!
# The general candidate principle along a sequence of stages

`EStage α` bundles the data of the general prepared model `CandidatePrinciple` at one index
(one stage of a diagonal). `EH1 … EH4` are its hypotheses at that index (`EH2 … EH4` for one
`R`), and `ECand` its candidate conclusion at that index; `candidates_of_stages` applies the
frozen principle `E false (fun _ => True)` to a sequence of stages. All predicates are the
frozen bodies, instantiated at one index, so the application is definitional.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_prepared_models

open MeasureTheory

noncomputable section

/-- One index of the data of the general prepared model. -/
structure EStage (α : Type) [MeasurableSpace α] where
  N : ℝ
  K : ℝ
  ν : Measure α
  μ : Measure (α × ℝ)
  ρ : Measure (α × ℝ)
  π : Measure ℝ
  b : α → Fin 6 → ℝ
  P : MvPolynomial (Fin 4) ℝ
  T : ℝ → ℕ
  nl : ℝ → ℕ
  j : (s : ℝ) → Fin (nl s) → Fin (2 ^ T s)
  A : (s : ℝ) → Fin (nl s) → Set α
  B : (s : ℝ) → Fin (nl s) → Set α
  c : (s : ℝ) → Fin (nl s) → Fin 5 → ℝ
  F : (s : ℝ) → Fin (nl s) → MvPolynomial (Fin 4) ℝ

/-- The model trajectory `x l t = (t, b₀ + t b₃, b₁ + t b₄, b₂ + t b₅)`. -/
def exS {α : Type} (b : α → Fin 6 → ℝ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b l 0 + t * b l 3, b l 1 + t * b l 4, b l 2 + t * b l 5]

/-- The dyadic time block. -/
def IS (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- The base cell of an incidence at scale `Nk^(-r)`. -/
def zS {α : Type} (b : α → Fin 6 → ℝ) (Nk r : ℝ) (p : α × ℝ) (e : Fin 3) : ℤ :=
  ⌊(![p.2, (exS b p.1 p.2) 1, (exS b p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋

/-- A whole-block fit at thickness `a` with slack `H`. -/
def fitS {α : Type} (b : α → Fin 6 → ℝ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α)
    (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |MvPolynomial.eval (exS b l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (exS b l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (exS b l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a

/-- The pointwise hypotheses of the model at one index. -/
def EH1 {α : Type} [MeasurableSpace α] (st : EStage α) : Prop :=
  Measurable (st.b) ∧ MeasureTheory.IsProbabilityMeasure (st.ν) ∧ MeasureTheory.IsProbabilityMeasure (st.π) ∧ st.μ ≤ ENNReal.ofReal (st.K) • ((st.ν).prod MeasureTheory.volume) ∧ st.ρ ≤ st.μ ∧ st.μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((st.K)⁻¹) ≤ st.ρ Set.univ ∧ (st.P).totalDegree ≤ 2 ∧ (∀ᵐ l ∂st.ν, |st.b l 0| + |st.b l 1| + |st.b l 3| + |st.b l 4| ≤ st.K) ∧ (∀ᵐ p ∂st.μ, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (exS st.b p.1 t) (st.P)| ≤ st.K ∧ |MvPolynomial.eval (exS st.b p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (st.P))| ≤ st.K ∧ |MvPolynomial.eval (exS st.b p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (st.P)))| ≤ st.K) ∧ (st.K)⁻¹ ≤ |MvPolynomial.eval (exS st.b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (st.P))|)

/-- The pure and joint caps at one index, for one range `R`. -/
def EH2 {α : Type} [MeasurableSpace α] (d S : ℝ) (st : EStage α) (R : ℝ) : Prop :=
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, st.π {w : ℝ | ⌊w / (st.N ^ (-v))⌋ = a} ≤ ENNReal.ofReal (st.K * st.N ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), st.μ {p | zS st.b (st.N) r p = q ∧ ⌊(if h then MvPolynomial.eval (exS st.b p.1 p.2) (st.P) else (exS st.b p.1 p.2) 3) / (st.N ^ (-s))⌋ = a} ≤ ENNReal.ofReal (st.K * st.N ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), st.μ {p | zS st.b (st.N) r p = q ∧ ⌊(if h then MvPolynomial.eval (exS st.b p.1 p.2) (st.P) else (exS st.b p.1 p.2) 3) / (st.N ^ (-s))⌋ = a ∧ ⌊st.b p.1 3 / (st.N ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (st.K * st.N ^ (-3 * r - d * s)) * st.π {w : ℝ | ⌊w / (st.N ^ (-v))⌋ = v₀})

/-- The true labels at one index, for one range `R`. -/
def EH3 {α : Type} [MeasurableSpace α] (d κ ℓ U e₀ : ℝ) (st : EStage α) (R : ℝ) : Prop :=
  ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → (fun (q : ℝ) (a g : ℝ → ℝ) => st.N ^ (κ * s) / st.K ≤ (2 : ℝ) ^ st.T s ∧ (2 : ℝ) ^ st.T s ≤ st.K * st.N ^ (κ * s) ∧ (∀ i, MeasurableSet (st.A s i) ∧ MeasurableSet (st.B s i) ∧ st.B s i ⊆ st.A s i) ∧ (∀ i i', i ≠ i' → st.j s i = st.j s i' → Disjoint (st.A s i) (st.A s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d * q ^ 2 * g s / st.K) ≤ st.ν (st.A s i) ∧ st.ν (st.A s i) ≤ ENNReal.ofReal (st.K * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / st.K) * st.ν (st.A s i) ≤ st.μ (st.B s i ×ˢ IS (st.T s) (st.j s i)) ∧ (∀ e, |st.c s i e| ≤ st.K) ∧ (st.F s i).totalDegree ≤ 2 ∧ (∀ l ∈ st.A s i, ∀ t ∈ IS (st.T s) (st.j s i), |(exS st.b l t) 1 - st.c s i 0 - t * st.c s i 1| ≤ st.K * q ∧ |(exS st.b l t) 2 - st.c s i 2 - t * st.c s i 3 - st.c s i 4 * (exS st.b l t) 1| ≤ st.K * q * g s ∧ |st.b l 4 - st.c s i 3 - st.c s i 4 * st.b l 3| ≤ st.K * g s) ∧ (∀ l ∈ st.B s i, fitS st.b (st.K) (a s) (st.F s i) l (IS (st.T s) (st.j s i))) ∧ (∀ᵐ p ∂st.μ, p.1 ∈ st.B s i → p.2 ∈ IS (st.T s) (st.j s i) → (st.K)⁻¹ ≤ |MvPolynomial.eval (exS st.b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (st.F s i))|) ∧ (false = true → st.P = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂st.μ, |st.b p.1 4 + st.b p.1 0| ≤ st.N ^ (-e₀)) ∧ |st.c s i 3 + st.c s i 0 + ((st.j s i : ℕ) + (1 : ℝ) / 2) * q * st.c s i 1| + |st.c s i 4 - ((st.j s i : ℕ) + (1 : ℝ) / 2) * q| ≤ st.K * q ∧ (∃ L : Fin 4 → ℝ, st.F s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ st.K * (1 + a s / q ^ 2) ∧ ∀ l ∈ st.B s i, ∀ t ∈ IS (st.T s) (st.j s i), |L 1 - (exS st.b l t) 1 * L 3| + |L 2 + t * L 3| ≤ st.K * (1 + a s / q)))) ∧ (∀ᵐ p ∂st.μ, ∃ i, p.1 ∈ st.B s i ∧ p.2 ∈ IS (st.T s) (st.j s i)) ∧ (∀ (i : Fin (st.nl s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → st.μ {p | p.1 ∈ st.B s i ∧ p.2 ∈ IS (st.T s) (st.j s i) ∧ ⌊st.b p.1 3 / (st.N ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (st.K * q) * st.ν (st.A s i) * st.π {w : ℝ | ⌊w / (st.N ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(st.T s : ℤ))) (fun s => st.N ^ (-s)) (fun s => st.N ^ (-ℓ * s))

/-- Nesting of the true labels at one index, for one range `R`. -/
def EH4 {α : Type} [MeasurableSpace α] (U : ℝ) (st : EStage α) (R : ℝ) : Prop :=
  ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (st.nl t), ∃ h : Fin (st.nl s), st.A t i ⊆ st.A s h ∧ IS (st.T t) (st.j t i) ⊆ IS (st.T s) (st.j s h)

/-- A candidate at one index, for range `R` and loss `ε`. -/
def ECand {α : Type} [MeasurableSpace α] (d ℓ U : ℝ) (st : EStage α) (R ε : ℝ) : Prop :=
  ∃ (s v : ℝ) (i : Fin (st.nl s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ U ∧ ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ st.N ^ R * ((1 + ∑ e ∈ (st.F s i).support, |(st.F s i).coeff e|) + ∑ e ∈ (st.P).support, |(st.P).coeff e|) ^ R) ∧ ENNReal.ofReal (st.N ^ (-d * v - ε) / (2 : ℝ) ^ st.T s) * st.ν (st.A s i) ≤ st.ρ {p | p.1 ∈ st.B s i ∧ p.2 ∈ IS (st.T s) (st.j s i) ∧ fitS st.b (st.N ^ ε) (st.N ^ (-s - v)) Q p.1 (IS (st.T s) (st.j s i)) ∧ st.N ^ (-ε) ≤ |MvPolynomial.eval (exS st.b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}) ∨ (∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ st.N ^ R) ∧ ENNReal.ofReal (st.N ^ (-ε) / (2 : ℝ) ^ st.T s) * st.ν (st.A s i) ≤ st.ρ {p | p.1 ∈ st.B s i ∧ p.2 ∈ IS (st.T s) (st.j s i) ∧ |st.b p.1 4 - z 0 - z 1 * st.b p.1 3| ≤ st.N ^ ε * st.N ^ (-ℓ * s - v)}))

end

end Submission.Obl.k4_finite_positive_prepared_models
