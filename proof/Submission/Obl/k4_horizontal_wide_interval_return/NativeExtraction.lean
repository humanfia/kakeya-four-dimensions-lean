import Submission.Obl.k4_horizontal_wide_interval_return.GeometricExtraction
import Submission.Obl.k4_horizontal_wide_interval_return.FieldPrinciple
import Submission.Obl.k4_horizontal_wide_interval_return.LongComparison

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_horizontal_wide_interval_return

/-- The geometric input with its frame coordinates written explicitly. -/
def ExplicitGeometryAt {α : Type} [MeasurableSpace α]
    (N θ d κ s v m J : ℝ) (ν : MeasureTheory.Measure α)
    (ρ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    (T n : ℕ) (j : Fin n → Fin (2 ^ T)) (A B : Fin n → Set α)
    (c : Fin n → Fin 5 → ℝ) : Prop :=
  ∃ (i : Fin n) (lam : MeasureTheory.Measure (α × ℝ)) (Bs : Set α)
    (L C : Fin 4 → ℝ),
  let t₀ : ℝ := (j i : ℕ) / (2 : ℝ) ^ T
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  let g : ℝ := N ^ (-κ * s)
  let a : ℝ := N ^ (-s)
  let zt : ℝ → ℝ := fun t => (t - t₀) / q
  let zZ : α → ℝ → ℝ := fun l t => (b l 0 + t * b l 3 - c i 0 - t * c i 1) / q
  let tr : α → ℝ → ℝ := fun l t =>
    (b l 1 + t * b l 4 - c i 2 - t * c i 3 - c i 4 * (b l 0 + t * b l 3)) / (q * g)
  let resid : α → ℝ → ℝ := fun l t =>
    (b l 2 + t * b l 5 - (L 0 + L 1 * t + L 2 * (b l 0 + t * b l 3) +
      L 3 * (b l 1 + t * b l 4))) / a
  MeasurableSet Bs ∧ Bs ⊆ B i ∧ lam ≤ ρ ∧
  (∀ᵐ p ∂lam, p.1 ∈ Bs ∧ p.2 ∈ Set.Icc t₀ (t₀ + q)) ∧
  ENNReal.ofReal (N ^ (-θ)) * (ENNReal.ofReal q * ν (A i)) ≤ lam Set.univ ∧
  (∀ e, |L e| ≤ N ^ J) ∧ (∀ e, |C e| ≤ N ^ θ) ∧
  (∀ l ∈ Bs, ∀ t ∈ Set.Icc t₀ (t₀ + q),
    |zZ l t| ≤ N ^ θ ∧ |tr l t| ≤ N ^ θ ∧ |resid l t| ≤ N ^ θ) ∧
  ∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
    (Fs.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ θ * (N ^ (-v)) ^ (-d) ∧
    ∀ᵐ p ∂lam,
      ((![⌊zt p.2 / (N ^ (-m))⌋, ⌊zZ p.1 p.2 / (N ^ (-m))⌋] : Fin 2 → ℤ),
        ⌊(resid p.1 p.2 -
          ((C 0 + C 1 * zt p.2 + C 2 * zZ p.1 p.2) * tr p.1 p.2 +
            C 3 * (tr p.1 p.2) ^ 2)) / (N ^ (-v))⌋) ∈ Fs

/-- Uniform positive scales precede every arbitrary power loss. -/
def ExplicitUniformGeometry {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d κ U : ℝ) (ν : ℕ → MeasureTheory.Measure α)
    (ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (b : ℕ → α → Fin 6 → ℝ)
    (T n : ℕ → ℝ → ℕ)
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
    (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) : Prop :=
  ∃ s v m U' J : ℝ, 0 < s ∧ 0 < v ∧ v < m ∧ κ * s ≤ m ∧
    0 < U' ∧ U' < m ∧ s + v ≤ U ∧ 17 ≤ J ∧
    ∀ θ : ℝ, 0 < θ → ∀ᶠ k in Filter.atTop,
      ExplicitGeometryAt (N k) θ d κ s v m J (ν k) (ρ k) (b k)
        (T k s) (n k s) (j k s) (A k s) (B k s) (c k s)

/-- The original all-rate three-layer prefix, with only a geometric/list
output. The local field principle is the separate input to its theorem. -/
def NativePreparation : Prop :=
  Row → Submission.Lib.K4QuadSheetMatching.TwoColorStatement →
  (fun (construct : Bool) (regime : ℝ → Prop) => ((fun (horizontal : Bool) (regime : ℝ → Prop) => ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ), (fun (x : ℕ → α → ℝ → Fin 4 → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → (fun (q : ℝ) (a g : ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i, fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k, p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i : ℕ) + (1 : ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ K k * q ∧ (∃ L : Fin 4 → ℝ, F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i, ∀ t ∈ I (T k s) (j k s i), |L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(T k s : ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ((fun projected : Prop => projected → ExplicitUniformGeometry N d κ U ν ρ b T n j A B c) (∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ, 0 < s₀ ∧ buffer * s₀ < U ∧ buffer * s₀ < e₀ ∧ s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - d) * u / 4 ∧ s + u < U ∧ s + u < 3 * s₀ / 2 ∧ (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀) ∧ (10 / (1 - d) + 3) * u < κ * s ∧ 1 < R ∧ ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < U ∧ buffer * M < e₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (fun (χ D : ℝ) (depth : Fin 3 → ℝ) => ∃ (ρstar : MeasureTheory.Measure (α × ℝ)) (np : Fin 3 → ℕ) (Cp : (h : Fin 3) → Fin (np h) → Set α) (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ) (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ), ρstar ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ρstar Set.univ ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧ (∀ h i, MeasurableSet (Cp h i)) ∧ (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧ (∀ h i, (∀ l ∈ Cp h i, ⌊b k l 3 / χ⌋ = qp h i 0 ∧ ⌊b k l 0 / χ⌋ = qp h i 1 ∧ ⌊b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |b k l e| ≤ N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ N k ^ ε ∧ (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (Gp h i)| ≤ N k ^ ε) ∧ (∀ l ∈ Cp h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ N k ^ ε * D ∧ |(x k l t) 3 - MvPolynomial.eval ![t, (x k l t) 2] (Gp h i)| ≤ N k ^ ε * N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d / N k ^ ε) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ ρ k (Cp h i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N k ^ ε))) (N k ^ (-M)) (N k ^ (-2 * κ * s₀)) ![s, s + u, s + v]))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2, (x k p.1 p.2) 1, (x k p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t, b k l 0 + t * b k l 3, b k l 1 + t * b k l 4, b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))) true regime) false (fun _ => True)

/-- The native extraction input after the full-strip comparison has been
proved for this same prepared parent. Only its local three-layer datum
is strengthened; the original parent and reference weights are unchanged. -/
def ComparedNativePreparation : Prop :=
  Row → Submission.Lib.K4QuadSheetMatching.TwoColorStatement →
  (fun (construct : Bool) (regime : ℝ → Prop) => ((fun (horizontal : Bool) (regime : ℝ → Prop) => ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < ℓ → 0 < S → S ≤ 1 → 0 < U → 0 < e₀ → regime κ → (horizontal = true → ℓ = κ) → ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ)) (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ), (fun (x : ℕ → α → ℝ → Fin 4 → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ => (fun fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop => (∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → (fun (q : ℝ) (a g : ℝ → ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧ (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (a s ^ d * q ^ 2 * g s / K k) ≤ ν k (A k s i) ∧ ν k (A k s i) ≤ ENNReal.ofReal (K k * a s ^ d * q ^ 2 * g s) ∧ ENNReal.ofReal (q / K k) * ν k (A k s i) ≤ μ k (B k s i ×ˢ I (T k s) (j k s i)) ∧ (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧ |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤ K k * q * g s ∧ |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g s) ∧ (∀ l ∈ B k s i, fit k (K k) (a s) (F k s i) l (I (T k s) (j k s i))) ∧ (∀ᵐ p ∂μ k, p.1 ∈ B k s i → p.2 ∈ I (T k s) (j k s i) → (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|) ∧ (horizontal = true → P k = MvPolynomial.X (3 : Fin 4) ∧ (∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)) ∧ |c k s i 3 + c k s i 0 + ((j k s i : ℕ) + (1 : ℝ) / 2) * q * c k s i 1| + |c k s i 4 - ((j k s i : ℕ) + (1 : ℝ) / 2) * q| ≤ K k * q ∧ (∃ L : Fin 4 → ℝ, F k s i = MvPolynomial.X (3 : Fin 4) - (MvPolynomial.C (L 0) + MvPolynomial.C (L 1) * MvPolynomial.X (0 : Fin 4) + MvPolynomial.C (L 2) * MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (L 3) * MvPolynomial.X (2 : Fin 4)) ∧ |L 3| ≤ K k * (1 + a s / q ^ 2) ∧ ∀ l ∈ B k s i, ∀ t ∈ I (T k s) (j k s i), |L 1 - (x k l t) 1 * L 3| + |L 2 + t * L 3| ≤ K k * (1 + a s / q)))) ∧ (∀ᵐ p ∂μ k, ∃ i, p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i)) ∧ (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R → μ k {p | p.1 ∈ B k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * q) * ν k (A k s i) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) ((2 : ℝ) ^ (-(T k s : ℤ))) (fun s => N k ^ (-s)) (fun s => N k ^ (-ℓ * s))) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ I (T k t) (j k t i) ⊆ I (T k s) (j k s h)) → ((fun projected : Prop => projected → ExplicitUniformGeometry N d κ U ν ρ b T n j A B c) (∀ buffer : ℝ, 100 < buffer → ∃ s₀ s u v R : ℝ, 0 < s₀ ∧ buffer * s₀ < U ∧ buffer * s₀ < e₀ ∧ s₀ < s ∧ 0 < u ∧ 0 < v ∧ v < u ∧ v < (1 - d) * u / 4 ∧ s + u < U ∧ s + u < 3 * s₀ / 2 ∧ (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀) ∧ (10 / (1 - d) + 3) * u < κ * s ∧ 1 < R ∧ ∃ M : ℝ, buffer * s₀ < M ∧ buffer * M < U ∧ buffer * M < e₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (fun (χ D : ℝ) (depth : Fin 3 → ℝ) => ∃ (ρstar : MeasureTheory.Measure (α × ℝ)) (np : Fin 3 → ℕ) (Cp : (h : Fin 3) → Fin (np h) → Set α) (qp : (h : Fin 3) → Fin (np h) → Fin 3 → ℤ) (Gp : (h : Fin 3) → Fin (np h) → MvPolynomial (Fin 2) ℝ), ρstar ≤ ρ k ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ρstar Set.univ ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, ∃ i, p.1 ∈ Cp h i) ∧ (∀ h i, MeasurableSet (Cp h i)) ∧ (∀ h i i', i ≠ i' → Disjoint (Cp h i) (Cp h i')) ∧ (∀ h i, (∀ l ∈ Cp h i, ⌊b k l 3 / χ⌋ = qp h i 0 ∧ ⌊b k l 0 / χ⌋ = qp h i 1 ∧ ⌊b k l 1 / D⌋ = qp h i 2 ∧ (∀ e, |b k l e| ≤ N k ^ ε)) ∧ |(qp h i 0 : ℝ) * χ| + |(qp h i 1 : ℝ) * χ| + |(qp h i 2 : ℝ) * D| ≤ N k ^ ε ∧ (Gp h i).totalDegree ≤ 2 ∧ (∀ e, |(Gp h i).coeff e| ≤ N k ^ R) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, (qp h i 2 : ℝ) * D - t * ((qp h i 1 : ℝ) * χ) + D * w] (Gp h i)| ≤ N k ^ ε) ∧ (∀ l ∈ Cp h i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(x k l t) 2 - (qp h i 2 : ℝ) * D + t * ((qp h i 1 : ℝ) * χ)| ≤ N k ^ ε * D ∧ |(x k l t) 3 - MvPolynomial.eval ![t, (x k l t) 2] (Gp h i)| ≤ N k ^ ε * N k ^ (-depth h)) ∧ ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d / N k ^ ε) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ)) ≤ ρ k (Cp h i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ (∀ h, (∑ i : Fin (np h), ENNReal.ofReal (χ * D * (N k ^ (-depth h)) ^ d) * π k (Set.Ico ((qp h i 0 : ℝ) * χ) (((qp h i 0 : ℝ) + 1) * χ))) ≤ ENNReal.ofReal (N k ^ ε)) ∧ (∀ᵐ p ∂ρstar, ∀ h : Fin 3, h ≠ 0 →
      ∀ (i₀ : Fin (np 0)) (ih : Fin (np h)),
        p.1 ∈ Cp 0 i₀ → p.1 ∈ Cp h ih →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1,
          |MvPolynomial.eval
            (![t, (qp 0 i₀ 2 : ℝ) * D - t * ((qp 0 i₀ 1 : ℝ) * χ) + D * w] : Fin 2 → ℝ)
            (Gp h ih - Gp 0 i₀)| ≤
              N k ^ (ε + (10 / (1 - d)) * u) * N k ^ (-s))) (N k ^ (-M)) (N k ^ (-2 * κ * s₀)) ![s, s + u, s + v]))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧ |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r p e => ⌊(![p.2, (x k p.1 p.2) 1, (x k p.1 p.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun k l t => ![t, b k l 0 + t * b k l 3, b k l 1 + t * b k l 4, b k l 2 + t * b k l 5]) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))) true regime) false (fun _ => True)

/-- Supply the strengthened local datum using a proved comparison principle. -/
theorem nativePreparation_of_compared
    (hc : NativeComparison) (hn : ComparedNativePreparation) : NativePreparation := by
  intro hRow hMatching N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1
    hU he₀ hreg hℓκ α _ ν μ ρ π b P T n j A B c F
  dsimp only
  intro hbasic hcaps hprep hnest hproj
  exact hn hRow hMatching N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1
    hU he₀ hreg hℓκ α ν μ ρ π b P T n j A B c F hbasic hcaps hprep hnest
    (hc hMatching N K hN hNt hK d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1
      hU he₀ hreg hℓκ α ν μ ρ π b P T n j A B c F hbasic hcaps hprep hnest hproj)

open MeasureTheory Set Filter

/-- Reconstruct the cell frame from the explicit Mathlib-only interface. -/
theorem Data.geometricExtractionAt_of_explicit {α : Type} [MeasurableSpace α]
    (cfg : Data α) (k : ℕ) (θ s v m J : ℝ)
    (h : ExplicitGeometryAt (cfg.N k) θ cfg.d cfg.κ s v m J (cfg.ν k) (cfg.ρ k)
      (cfg.b k) (cfg.T k s) (cfg.n k s) (cfg.j k s) (cfg.A k s) (cfg.B k s) (cfg.c k s)) :
    cfg.GeometricExtractionAt k θ s v m J := by
  obtain ⟨i, lam, Bs, L, C, hBs, hsub, hlam, hsupp, hmass, hL, hC, hgeom,
    Fs, hcount, hcode⟩ := h
  let F : CellFrame := ⟨(cfg.j k s i : ℕ) / (2 : ℝ) ^ cfg.T k s,
    ((2 : ℝ) ^ cfg.T k s)⁻¹, cfg.N k ^ (-cfg.κ * s), cfg.N k ^ (-s), cfg.c k s i, L, C⟩
  exact ⟨i, lam, Bs, F, hBs, hsub, hlam, hsupp, hmass,
    rfl, rfl, rfl, rfl, rfl, hL, hC, hgeom, Fs, hcount, hcode⟩

/-- Convert the explicit frozen child into the existing checked geometric
preparation interface without an analytic step. -/
theorem geometricPreparation_of_native (h : NativePreparation) : GeometricPreparation := by
  intro hRow hMatching α _ cfg hv hp
  have hexp := h hRow hMatching cfg.N cfg.K hv.resolution_lower hv.resolution_tendsto
    ⟨hv.loss_lower, hv.loss_subpower⟩ cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀
    hv.dimension_nonneg hv.dimension_lt_one hv.rate_pos hv.rate_le_one hv.narrow_pos
    hv.palette_pos hv.palette_le_one hv.range_pos hv.contact_pos trivial
    (fun _ => hv.horizontal_rate) α cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n
    cfg.j cfg.A cfg.B cfg.c cfg.F hv.basic hv.caps hv.prepared hv.nested hp
  obtain ⟨s, v, m, U', J, hs, hv', hvm, hκm, hU', hUm, hsU, hJ, hexp⟩ := hexp
  refine ⟨s, v, m, U', J, hs, hv', hvm, hκm, hU', hUm, hsU, hJ, ?_⟩
  intro θ hθ
  exact (hexp θ hθ).mono fun k hk => cfg.geometricExtractionAt_of_explicit k θ s v m J hk

end Submission.Obl.k4_horizontal_wide_interval_return
