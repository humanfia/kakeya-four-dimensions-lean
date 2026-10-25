/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

/- Interface adapted from this obligation, session x0266, branch x0266.
Only the noncomputable section declaration has been added here. -/
import Mathlib
import ChallengeDeps

/-! Explicit Mathlib interfaces for the three parts of the endpoint crop. -/
noncomputable section

namespace Submission.Obl.k4_dyadic_crop_affine_laws

abbrev Line  : Type :=
  ℕ × (Fin 6 → ℝ)

abbrev Inc  : Type :=
  Line × ℝ

abbrev Base  : Type :=
  EuclideanSpace ℝ (Fin 3) × ℤ

abbrev Joint  : Type :=
  Base × (Fin 2 → ℤ)

def Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε

def SingleFormat (N K : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure Line) (E : ℕ → Set Inc) : Prop :=
  (∃ M D : ℕ, ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂(ν k), ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K k) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ (((ν k).prod MeasureTheory.volume).restrict (E k)) Set.univ)

def FamilyFormat (N K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) : Prop :=
  (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ)

def Scale (N : ℕ → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ))

def Cell (a : ℝ) (q : Fin 4 → ℤ) : Set Line :=
  {l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧ ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3}

def Crop (a : ℝ) (q : Fin 4 → ℤ) (l : Line) : Line :=
  (l.1, ![l.2 0 / a - (q 0 : ℝ), l.2 1 / a - (q 1 : ℝ), l.2 2, l.2 3 / a - (q 2 : ℝ), l.2 4 / a - (q 3 : ℝ), l.2 5])

def CropInc (a : ℝ) (q : Fin 4 → ℤ) (p : Inc) : Inc :=
  (Crop a q p.1, p.2)

def Selected (ν : MeasureTheory.Measure Line) (E : Set Inc) : MeasureTheory.Measure Inc :=
  (ν.prod MeasureTheory.volume).restrict E

def Point (p : Inc) : Fin 4 → ℝ :=
  ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]

def Obs (N : ℕ → ℝ) (k : ℕ) (r : ℝ) (p : Inc) : Base :=
  ((WithLp.toLp 2 ![p.2, (Point p) 1, (Point p) 2] : EuclideanSpace ℝ (Fin 3)), ⌊(Point p) 3 / Scale N k r⌋)

def JointObs (N : ℕ → ℝ) (k : ℕ) (r u : ℝ) (p : Inc) : Joint :=
  (Obs N k r p, fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / Scale N k u⌋)

def BaseRef  : MeasureTheory.Measure Base :=
  MeasureTheory.volume.prod MeasureTheory.Measure.count

def JointRef  : MeasureTheory.Measure Joint :=
  BaseRef.prod MeasureTheory.Measure.count

def FiniteSource (ν : ℕ → MeasureTheory.Measure Line) (E : ℕ → Set Inc) : Prop :=
  ∀ k, MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasurableSet (E k) ∧ E k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1

def CropRelations (N : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure Line) (E₀ : ℕ → Set Inc) (u₀ β : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ)) (ρ : ℕ → ℝ) : Prop :=
  
  (∀ k, Function.Injective (q k)) ∧
  (∀ k γ, 0 < p k γ ∧ p k γ = ((ν₀ k) (Cell (Scale N k u₀) (q k γ))).toReal ∧
    ν k γ = (ENNReal.ofReal (p k γ))⁻¹ • MeasureTheory.Measure.map (Crop (Scale N k u₀) (q k γ)) ((ν₀ k).restrict (Cell (Scale N k u₀) (q k γ))) ∧
    E k γ = (CropInc (Scale N k u₀) (q k γ)) '' (E₀ k ∩ (Cell (Scale N k u₀) (q k γ) ×ˢ Set.univ))) ∧
  (∀ k, 0 < ρ k ∧ (∑ γ, p k γ) = ρ k ∧ ∀ γ, ω k γ = p k γ / ρ k) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (ρ k)⁻¹ ≤ N k ^ ε) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, ∀ γ, N k ^ (-β - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-β + ε))

def JointDensities (N : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure Line) (E : ℕ → Set Inc) : Prop :=
  ∀ k (r u : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → ∃ G : Joint → ENNReal, Measurable G ∧ MeasureTheory.Measure.map (JointObs N k r u) (Selected (ν k) (E k)) = JointRef.withDensity G

def JointTypical (N : ℕ → ℝ) (ν : ℕ → MeasureTheory.Measure Line) (E : ℕ → Set Inc) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ r u τ : ℝ, 0 ≤ r → r ≤ 1 → 0 ≤ u → u ≤ 4 → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, ∀ G : Joint → ENNReal, Measurable G → MeasureTheory.Measure.map (JointObs N k r u) (Selected (ν k) (E k)) = JointRef.withDensity G → (Selected (ν k) (E k)) {p | G (JointObs N k r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨ ENNReal.ofReal (N k ^ (-F r u + τ)) < G (JointObs N k r u p)} ≤ ENNReal.ofReal (N k ^ (-c))

def SlopeCeiling (ν : ℕ → MeasureTheory.Measure Line) (Λ : ℕ → ℝ) : Prop :=
  ∀ k (Z : Set (EuclideanSpace ℝ (Fin 3))), (ν k) {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤ ENNReal.ofReal (Λ k) * MeasureTheory.volume Z

def CropDensities (N : ℕ → ℝ) (L u₀ : ℝ) (W : ℕ → ℕ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (g : (k : ℕ) → Fin (W k) → ℝ → Base → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal) : Prop :=
  (∀ k γ r, 0 ≤ r → r ≤ 1 → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (Obs N k r) (Selected (ν k γ) (E k γ)) = BaseRef.withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u₀ + u < 4 → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (JointObs N k L u) (Selected (ν k γ) (E k γ)) = JointRef.withDensity (G k γ u))

def BaseTypical (N : ℕ → ℝ) (f : ℝ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (g : (k : ℕ) → Fin (W k) → ℝ → Base → ENNReal) : Prop :=
  ∀ r τ : ℝ, 0 ≤ r → r ≤ 1 → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (Selected (ν k γ) (E k γ)) {p | g k γ r (Obs N k r p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r (Obs N k r p)}) ≤ ENNReal.ofReal (N k ^ (-c))

def AngularTypical (N : ℕ → ℝ) (L : ℝ) (h : ℝ → ℝ) (u₀ : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal) : Prop :=
  ∀ u τ : ℝ, 0 < u → u₀ + u < 4 → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (Selected (ν k γ) (E k γ)) {p | G k γ u (JointObs N k L u p) < ENNReal.ofReal (N k ^ (-h u - τ)) ∨ ENNReal.ofReal (N k ^ (-h u + τ)) < G k γ u (JointObs N k L u p)}) ≤ ENNReal.ofReal (N k ^ (-c))

def CropWorldsStatement : Prop :=
  ∀ (N₀ K₀ : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure Line) (E₀ : ℕ → Set Inc) (u₀ : ℝ), (∀ k, 2 ≤ N₀ k) → Filter.Tendsto N₀ Filter.atTop Filter.atTop → Subpower N₀ K₀ → SingleFormat N₀ K₀ ν₀ E₀ → 0 ≤ u₀ → u₀ ≤ 4 → ∃ (ψ : ℕ → ℕ) (K : ℕ → ℝ) (β : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ)) (ρ : ℕ → ℝ), StrictMono ψ ∧ Subpower (N₀ ∘ ψ) K ∧ FamilyFormat (N₀ ∘ ψ) K W ω ν E (fun _ _ => MvPolynomial.X (3 : Fin 4)) (fun _ _ => 1) ∧ CropRelations (N₀ ∘ ψ) (ν₀ ∘ ψ) (E₀ ∘ ψ) u₀ β W ω ν E p q ρ

def CropAffineStatement : Prop :=
  ∀ (N Λ₀ : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure Line) (E₀ : ℕ → Set Inc) (L u₀ β : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc) (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ)) (ρ : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → FiniteSource ν₀ E₀ → 0 ≤ L → L ≤ 1 → 0 ≤ u₀ → u₀ < 4 → CropRelations N ν₀ E₀ u₀ β W ω ν E p q ρ → JointDensities N ν₀ E₀ → SlopeCeiling ν₀ Λ₀ → (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ₀ k ≤ N k ^ ε) → ∃ (g : (k : ℕ) → Fin (W k) → ℝ → Base → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal) (Λ : ℕ → ℝ), CropDensities N L u₀ W ν E g G ∧ (∀ k γ (Z : Set (EuclideanSpace ℝ (Fin 3))), ν k γ {l | (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5] : EuclideanSpace ℝ (Fin 3)) ∈ Z} ≤ ENNReal.ofReal (Λ k) * MeasureTheory.volume Z) ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Λ k ≤ N k ^ (β - 2 * u₀ + ε))

end Submission.Obl.k4_dyadic_crop_affine_laws
