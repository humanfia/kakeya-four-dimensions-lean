/- Adapted within this LOT tree from o227/x0811, commit 4016c77324508a766a6b97514cd97561473aacc6,
Submission/Obl/k4_horizontal_three_projection_wide_return/Model.lean. Removed the supercritical restriction and used o250's existential buffered mesh premise; all original laws and labels are retained. -/
import Submission.Obl.k4_horizontal_wide_interval_return.Preparation

set_option autoImplicit false

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set Filter

abbrev ReturnPrinciple : Prop :=
  (fun (construct : Bool) (regime : ℝ → Prop) => ((fun (horizontal : Bool) (regime : ℝ → Prop) => ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ), (fun (x : ℕ → α → ℝ → Fin 4 → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → (fun (q : ℝ) (a g : ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i, fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k, p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i : ℕ) + (1 : ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ K k * q ∧ (∃ L : Fin 4 → ℝ, F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i, ∀ t ∈ I (T k s) (j k s i), |L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(T k s : ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ((fun projected : Prop => if construct = true then projected else projected → (∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s v : ℝ) (i : Fin (n k s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ U ∧ ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ N k ^ R * ((1 + ∑ e ∈ (F k s i).support, |(F k s i).coeff e|) + ∑ e ∈ (P k).support, |(P k).coeff e|) ^ R) ∧ ENNReal.ofReal (N k ^ (-d * v - ε) / (2 : ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ fit k (N k ^ ε) (N k ^ (-s - v)) Q p.1 (I (T k s) (j k s i)) ∧ N k ^ (-ε) ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}) ∨ (∃ z : Fin 2 → ℝ, (∀ e, |z e| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-ε) / (2 : ℝ) ^ T k s) * ν k (A k s i) ≤ ρ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ |b k p.1 4 - z 0 - z 1 * b k p.1 3| ≤ N k ^ ε * N k ^ (-ℓ * s - v)})))) (∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ, 0 < s₀ ∧ buffer * s₀ < U ∧ buffer * s₀ < e₀ ∧ s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - d) * u / 4 ∧ s + u < U ∧ s + u < 3 * s₀ / 2 ∧ (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀) ∧ (10 / (1 - d) + 3) * u < κ * s ∧ 1 < R ∧ ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < U ∧ buffer * M < e₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (fun (χ D : ℝ) (depth : Fin 3 → ℝ) => ∃ (ρstar : MeasureTheory.Measure (α × ℝ)) (np : Fin 3 → ℕ) (Cp : (h : Fin 3) → Fin (np h) → Set α) (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ) (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ), ρstar ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ρstar Set.univ ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧ (∀ h i, MeasurableSet (Cp h i)) ∧ (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧ (∀ h i, (∀ l ∈ Cp h i, ⌊b k l 3 / χ⌋ = qp h i 0 ∧ ⌊b k l 0 / χ⌋ = qp h i 1 ∧ ⌊b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |b k l e| ≤ N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ N k ^ ε ∧ (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (Gp h i)| ≤ N k ^ ε) ∧ (∀ l ∈ Cp h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ N k ^ ε * D ∧ |(x k l t) 3 - MvPolynomial.eval ![t, (x k l t) 2] (Gp h i)| ≤ N k ^ ε * N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d / N k ^ ε) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ ρ k (Cp h i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N k ^ ε))) (N k ^ (-M)) (N k ^ (-2 * κ * s₀)) ![s, s + u, s + v]))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2, (x k p.1 p.2) 1, (x k p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t, b k l 0 + t * b k l 3, b k l 1 + t * b k l 4, b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))) true regime) false (fun _ => True)

/-- The original parent data, with every original label and law retained. -/
structure Data (α : Type) [MeasurableSpace α] where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
  ℓ : ℝ
  S : ℝ
  U : ℝ
  e₀ : ℝ
  ν : ℕ → Measure α
  μ : ℕ → Measure (α × ℝ)
  ρ : ℕ → Measure (α × ℝ)
  π : ℕ → Measure ℝ
  b : ℕ → α → Fin 6 → ℝ
  P : ℕ → MvPolynomial (Fin 4) ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α
  c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ
  F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def x (k : ℕ) (l : α) (t : ℝ) : Fin 4 → ℝ :=
  ![t, cfg.b k l 0 + t * cfg.b k l 3, cfg.b k l 1 + t * cfg.b k l 4,
    cfg.b k l 2 + t * cfg.b k l 5]

def I (_cfg : Data α) (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)

noncomputable def z (k : ℕ) (Nk r : ℝ) (p : α × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, (cfg.x k p.1 p.2) 1, (cfg.x k p.1 p.2) 2] : Fin 3 → ℝ) e /
    Nk ^ (-r)⌋

def fit (k : ℕ) (H a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (l : α) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, |MvPolynomial.eval (cfg.x k l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (cfg.x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (cfg.x k l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a

def Basic : Prop :=
  (∀ k, Measurable (cfg.b k) ∧ MeasureTheory.IsProbabilityMeasure (cfg.ν k) ∧ MeasureTheory.IsProbabilityMeasure (cfg.π k) ∧ cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • ((cfg.ν k).prod MeasureTheory.volume) ∧ cfg.ρ k ≤ cfg.μ k ∧ cfg.μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((cfg.K k)⁻¹) ≤ cfg.ρ k Set.univ ∧ (cfg.P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂cfg.ν k, |cfg.b k l 0| + |cfg.b k l 1| + |cfg.b k l 3| + |cfg.b k l 4| ≤ cfg.K k) ∧ (∀ᵐ p ∂cfg.μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (cfg.x k p.1 t) (cfg.P k)| ≤ cfg.K k ∧ |MvPolynomial.eval (cfg.x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k))| ≤ cfg.K k ∧ |MvPolynomial.eval (cfg.x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k)))| ≤ cfg.K k) ∧ (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.P k))|))

def Caps : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) / (cfg.N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), cfg.μ k {p | cfg.z k (cfg.N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) else (cfg.x k p.1 p.2) 3) / (cfg.N k ^ (-s))⌋ = a ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * s)) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀}))

def Prepared : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ cfg.U → (fun (q : ℝ) (a g : ℝ → ℝ) => cfg.N k ^ (cfg.κ * s) / cfg.K k ≤ (2 : ℝ) ^ cfg.T k s ∧ (2 : ℝ) ^ cfg.T k s ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) ∧ (∀ i, MeasurableSet (cfg.A k s i) ∧ MeasurableSet (cfg.B k s i) ∧ cfg.B k s i ⊆ cfg.A k s i) ∧ (∀ i i', i ≠ i' → cfg.j k s i = cfg.j k s i' → Disjoint (cfg.A k s i) (cfg.A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ cfg.d * q ^ 2 * g s / cfg.K k) ≤ cfg.ν k (cfg.A k s i) ∧ cfg.ν k (cfg.A k s i) ≤ ENNReal.ofReal (cfg.K k * a s ^ cfg.d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / cfg.K k) * cfg.ν k (cfg.A k s i) ≤ cfg.μ k (cfg.B k s i ×ˢ cfg.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ e, |cfg.c k s i e| ≤ cfg.K k) ∧ (cfg.F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ cfg.A k s i, ∀ t ∈ cfg.I (cfg.T k s) (cfg.j k s i), |(cfg.x k l t) 1 - cfg.c k s i 0 - t * cfg.c k s i 1| ≤ cfg.K k * q ∧ |(cfg.x k l t) 2 - cfg.c k s i 2 - t * cfg.c k s i 3 - cfg.c k s i 4 * (cfg.x k l t) 1| ≤ cfg.K k * q * g s ∧ |cfg.b k l 4 - cfg.c k s i 3 - cfg.c k s i 4 * cfg.b k l 3| ≤ cfg.K k * g s) ∧ (∀ l ∈ cfg.B k s i, cfg.fit k (cfg.K k) (a s) (cfg.F k s i) l (cfg.I (cfg.T k s) (cfg.j k s i))) ∧ (∀ᵐ p ∂cfg.μ k, p.1 ∈ cfg.B k s i → p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) → (cfg.K k)⁻¹ ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (cfg.F k s i))|) ∧ (true = true → cfg.P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧ |cfg.c k s i 3 + cfg.c k s i 0 + ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q * cfg.c k s i 1| + |cfg.c k s i 4 - ((cfg.j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ cfg.K k * q ∧ (∃ L : Fin 4 → ℝ, cfg.F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ cfg.K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ cfg.B k s i, ∀ t ∈ cfg.I (cfg.T k s) (cfg.j k s i), |L 1 - (cfg.x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ cfg.K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂cfg.μ k, ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i)) ∧ (∀ (i : Fin (cfg.n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → cfg.μ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧ ⌊cfg.b k p.1 3 / (cfg.N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (cfg.K k * q) * cfg.ν k (cfg.A k s i) * cfg.π k {w : ℝ | ⌊w / (cfg.N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(cfg.T k s : ℤ))) (fun s => cfg.N k ^ (-s)) (fun s => cfg.N k ^ (-cfg.ℓ * s)))

def Nested : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ cfg.U → ∀ i : Fin (cfg.n k t), ∃ h : Fin (cfg.n k s), cfg.A k t i ⊆ cfg.A k s h ∧ cfg.I (cfg.T k t) (cfg.j k t i) ⊆ cfg.I (cfg.T k s) (cfg.j k s h))

def Projected : Prop :=
  (∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ, 0 < s₀ ∧ buffer * s₀ < cfg.U ∧ buffer * s₀ < cfg.e₀ ∧ s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - cfg.d) * u / 4 ∧ s + u < cfg.U ∧ s + u < 3 * s₀ / 2 ∧ (10 / (1 - cfg.d) + 3) * u < 2 * cfg.κ * (s - s₀) ∧ (10 / (1 - cfg.d) + 3) * u < cfg.κ * s ∧ 1 < R ∧ ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < cfg.U ∧ buffer * M < cfg.e₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (fun (χ D : ℝ) (depth : Fin 3 → ℝ) => ∃ (ρstar : MeasureTheory.Measure (α × ℝ)) (np : Fin 3 → ℕ) (Cp : (h : Fin 3) → Fin (np h) → Set α) (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ) (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ), ρstar ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ ρstar Set.univ ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧ (∀ h i, MeasurableSet (Cp h i)) ∧ (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧ (∀ h i, (∀ l ∈ Cp h i, ⌊cfg.b k l 3 / χ⌋ = qp h i 0 ∧ ⌊cfg.b k l 0 / χ⌋ = qp h i 1 ∧ ⌊cfg.b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |cfg.b k l e| ≤ cfg.N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ cfg.N k ^ ε ∧ (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ cfg.N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (Gp h i)| ≤ cfg.N k ^ ε) ∧ (∀ l ∈ Cp h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(cfg.x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ cfg.N k ^ ε * D ∧ |(cfg.x k l t) 3 - MvPolynomial.eval ![t, (cfg.x k l t) 2] (Gp h i)| ≤ cfg.N k ^ ε * cfg.N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d / cfg.N k ^ ε) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ cfg.ρ k (Cp h i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (cfg.N k ^ (-depth h)) ^ cfg.d) * cfg.π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (cfg.N k ^ ε))) (cfg.N k ^ (-M)) (cfg.N k ^ (-2 * cfg.κ * s₀)) ![s, s + u, s + v])

def Conclusion : Prop :=
  (∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s v : ℝ) (i : Fin (cfg.n k s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ cfg.U ∧ ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ cfg.N k ^ R * ((1 + ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e|) + ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e|) ^ R) ∧ ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤ cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧ cfg.fit k (cfg.N k ^ ε) (cfg.N k ^ (-s - v)) Q p.1 (cfg.I (cfg.T k s) (cfg.j k s i)) ∧ cfg.N k ^ (-ε) ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}) ∨ (∃ direction : Fin 2 → ℝ, (∀ e, |direction e| ≤ cfg.N k ^ R) ∧ ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤ cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧ |cfg.b k p.1 4 - direction 0 - direction 1 * cfg.b k p.1 3| ≤ cfg.N k ^ ε * cfg.N k ^ (-cfg.ℓ * s - v)})))

def CandidateAt (R ε : ℝ) (k : ℕ) : Prop :=
  ∃ (s v : ℝ) (i : Fin (cfg.n k s)), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ v ∧ v ≤ R ∧ s + v ≤ cfg.U ∧ ((∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ cfg.N k ^ R * ((1 + ∑ e ∈ (cfg.F k s i).support, |(cfg.F k s i).coeff e|) + ∑ e ∈ (cfg.P k).support, |(cfg.P k).coeff e|) ^ R) ∧ ENNReal.ofReal (cfg.N k ^ (-cfg.d * v - ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤ cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧ cfg.fit k (cfg.N k ^ ε) (cfg.N k ^ (-s - v)) Q p.1 (cfg.I (cfg.T k s) (cfg.j k s i)) ∧ cfg.N k ^ (-ε) ≤ |MvPolynomial.eval (cfg.x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Q)|}) ∨ (∃ direction : Fin 2 → ℝ, (∀ e, |direction e| ≤ cfg.N k ^ R) ∧ ENNReal.ofReal (cfg.N k ^ (-ε) / (2 : ℝ) ^ cfg.T k s) * cfg.ν k (cfg.A k s i) ≤ cfg.ρ k {p | p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) ∧ |cfg.b k p.1 4 - direction 0 - direction 1 * cfg.b k p.1 3| ≤ cfg.N k ^ ε * cfg.N k ^ (-cfg.ℓ * s - v)}))

structure Valid : Prop where
  resolution_lower : ∀ k, 2 ≤ cfg.N k
  resolution_tendsto : Tendsto cfg.N atTop atTop
  loss_lower : ∀ k, 1 ≤ cfg.K k
  loss_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  narrow_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  range_pos : 0 < cfg.U
  contact_pos : 0 < cfg.e₀
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  prepared : cfg.Prepared
  nested : cfg.Nested

end Data

/-- The structured model has exactly the original hypotheses and output. -/
theorem returnPrinciple_of_model
    (h : ∀ (α : Type) [MeasurableSpace α] (cfg : Data α),
      cfg.Valid → cfg.Projected → cfg.Conclusion) : ReturnPrinciple := by
  intro N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hℓκ
    α _ ν μ ρ π b P T n j A B c F
  dsimp only
  intro hbasic hcaps hprep hnest
  simp only [Bool.false_eq_true, ↓reduceIte]
  intro hproj
  let cfg : Data α := ⟨N, K, d, κ, ℓ, S, U, e₀, ν, μ, ρ, π, b, P, T, n, j, A, B, c, F⟩
  have hv : cfg.Valid := ⟨hN, hNt, hK.1, hK.2, hd, hd1, hκ, hκ1, hℓ,
    hS, hS1, hU, he₀, hℓκ rfl, hbasic, hcaps, hprep, hnest⟩
  exact h α cfg hv hproj


/-- Typed interface for the remaining all-rate analytic construction. -/
def ModelPreparation : Prop :=
  Row → Submission.Lib.K4QuadSheetMatching.TwoColorStatement →
  ∀ (α : Type) [MeasurableSpace α] (cfg : Data α), cfg.Valid → cfg.Projected →
    UniformCellExtraction cfg.N cfg.d cfg.U cfg.ν cfg.ρ cfg.b cfg.T cfg.n cfg.j cfg.A cfg.B

theorem preparation_of_model (h : ModelPreparation) : WidePreparation := by
  intro hRow hMatching N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he₀ hreg hℓκ
    α _ ν μ ρ π b P T n j A B c F hbasic hcaps hprep hnest hproj
  let cfg : Data α := ⟨N, K, d, κ, ℓ, S, U, e₀, ν, μ, ρ, π, b, P, T, n, j, A, B, c, F⟩
  have hv : cfg.Valid := ⟨hN, hNt, hK.1, hK.2, hd, hd1, hκ, hκ1, hℓ,
    hS, hS1, hU, he₀, hℓκ rfl, hbasic, hcaps, hprep, hnest⟩
  exact h hRow hMatching α cfg hv hproj

theorem Data.conclusion_of_extraction {α : Type} [MeasurableSpace α] (cfg : Data α)
    (hScalar : Scalar) (hv : cfg.Valid)
    (h : UniformCellExtraction cfg.N cfg.d cfg.U cfg.ν cfg.ρ cfg.b
      cfg.T cfg.n cfg.j cfg.A cfg.B) : cfg.Conclusion := by
  obtain ⟨R, hR, hmain⟩ := candidates_of_uniform_extraction hScalar cfg.N cfg.d cfg.U
    cfg.ν cfg.ρ cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.F
    hv.resolution_lower hv.resolution_tendsto hv.dimension_nonneg hv.dimension_lt_one h
  refine ⟨R, hR, fun ε hε => ?_⟩
  apply (hmain ε hε).mono
  intro k hk
  obtain ⟨s, v, i, hslo, hshi, hvlo, hvhi, hsv, hcandidate⟩ := hk
  refine ⟨s, v, i, hslo, hshi, hvlo, hvhi, hsv, Or.inl ?_⟩
  simpa only [NativeCandidate, originalBlock, lineZ, lineY, lineX,
    Data.x, Data.I, Data.fit] using hcandidate

end Submission.Obl.k4_horizontal_wide_interval_return
