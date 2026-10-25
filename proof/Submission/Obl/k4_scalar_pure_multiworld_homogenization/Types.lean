import Mathlib
import ChallengeDeps

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal

abbrev Trajectory := ℕ × (Fin 5 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := (Fin 2 → ℝ) × ℤ

abbrev Problem := Σ W : ℕ → ℕ,
  (ℕ → ℝ) × (ℕ → ℝ) × ℕ × ℕ × ℝ × ℝ × ℝ × ℝ ×
  ((k : ℕ) → Fin (W k) → ℝ) ×
  ((k : ℕ) → Fin (W k) → Measure Trajectory) ×
  ((k : ℕ) → Fin (W k) → Set Incidence) ×
  ((k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal) ×
  ((k : ℕ) → Fin (W k) → ℝ → (Observation × ℤ) → ENNReal) ×
  (ℝ → ℝ)

abbrev resolution (p : Problem) := p.2.1
abbrev loss (p : Problem) := p.2.2.1
abbrev sizeBudget (p : Problem) := p.2.2.2.1
abbrev degreeBudget (p : Problem) := p.2.2.2.2.1
abbrev length (p : Problem) := p.2.2.2.2.2.1
abbrev rate (p : Problem) := p.2.2.2.2.2.2.1
abbrev angularRate (p : Problem) := p.2.2.2.2.2.2.2.1
abbrev angularLength (p : Problem) := p.2.2.2.2.2.2.2.2.1
abbrev weight (p : Problem) := p.2.2.2.2.2.2.2.2.2.1
abbrev prior (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.1
abbrev event (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.1
abbrev density (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.1
abbrev profile (p : Problem) := p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

abbrev y (l : Trajectory) (t : ℝ) : ℝ := l.2 0 + t * l.2 1
abbrev x (l : Trajectory) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4
abbrev observe (N r : ℝ) (z : Incidence) : Observation :=
  (![z.2, y z.1 z.2], ⌊x z.1 z.2 / N ^ (-r)⌋)
abbrev reference : Measure Observation := volume.prod Measure.count
abbrev law (p : Problem) (k : ℕ) (a : Fin (p.1 k)) : Measure Incidence :=
  ((prior p k a).prod volume).restrict (event p k a)

abbrev Format (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ B ∧ ∃ P : Fin m → MvPolynomial (Fin n) ℝ,
    (∀ j, (P j).totalDegree ≤ D ∧ ∀ b, |(P j).coeff b| ≤ B) ∧
    ∃ S : Set (Fin m → SignType),
      A = {z | (fun j => SignType.sign (MvPolynomial.eval z (P j))) ∈ S}

abbrev Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

abbrev RawScalar (p : Problem) : Prop :=
  ((∀ k, 2 ≤ resolution p k) ∧ Tendsto (resolution p) atTop atTop ∧
    Subpower (resolution p) (loss p) ∧
    1 ≤ sizeBudget p ∧ 1 ≤ degreeBudget p ∧ 0 < length p ∧
    0 ≤ rate p ∧ rate p < 1 ∧ 0 < angularRate p ∧ 0 < angularLength p) ∧
  ((∀ k, (p.1 k : ℝ) ≤ resolution p k ^ (sizeBudget p : ℝ) ∧
    (∀ a, 0 ≤ weight p k a) ∧ (∑ a, weight p k a) = 1 ∧
    (∀ a, IsProbabilityMeasure (prior p k a) ∧
      (∃ n : ℕ, (n : ℝ) ≤ resolution p k ^ (sizeBudget p : ℝ) ∧
        ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)),
          (∀ j, 0 ≤ h j ∧ h j ≤ resolution p k ^ (sizeBudget p : ℝ) ∧
            (i j : ℝ) ≤ resolution p k ^ (sizeBudget p : ℝ) ∧
            Format 5 (resolution p k ^ (sizeBudget p : ℝ)) (degreeBudget p) (B j) ∧
            (∀ b ∈ B j, ∀ e, |b e| ≤ resolution p k ^ (sizeBudget p : ℝ))) ∧
          prior p k a = ∑ j, ENNReal.ofReal (h j) •
            Measure.map (fun b => (i j, b)) (volume.restrict (B j))) ∧
      (∀ᵐ l ∂prior p k a, ∀ e, |l.2 e| ≤ loss p k) ∧
      MeasurableSet (event p k a) ∧ event p k a ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧
      (∀ z ∈ event p k a, (z.1.1 : ℝ) ≤ resolution p k ^ (sizeBudget p : ℝ)) ∧
      (∀ i : ℕ, Format 6 (resolution p k ^ (sizeBudget p : ℝ)) (degreeBudget p)
        {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ event p k a})) ∧
      ENNReal.ofReal ((loss p k)⁻¹) ≤
      ∑ a, ENNReal.ofReal (weight p k a) * law p k a univ))

abbrev PureProfile (p : Problem) : Prop :=
  (∀ k a r, 0 ≤ r → r ≤ length p → Measurable (density p k a r) ∧
    (law p k a).map (observe (resolution p k) r) =
      reference.withDensity (density p k a r)) ∧
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ length p →
    0 ≤ profile p s - profile p r ∧ profile p s - profile p r ≤ s - r) ∧
  (∀ r τ : ℝ, 0 ≤ r → r ≤ length p → 0 < τ →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ a, ENNReal.ofReal (weight p k a) * law p k a
        {z | density p k a r (observe (resolution p k) r z) <
            ENNReal.ofReal (resolution p k ^ (-profile p r - τ)) ∨
          ENNReal.ofReal (resolution p k ^ (-profile p r + τ)) <
            density p k a r (observe (resolution p k) r z)}) ≤
        ENNReal.ofReal (resolution p k ^ (-c)))

abbrev selectedProblem (p : Problem) (φ : ℕ → ℕ) (K : ℕ → ℝ) (M D : ℕ)
    (E : (k : ℕ) → Fin (p.1 (φ k)) → Set Incidence)
    (ρ : (k : ℕ) → Fin (p.1 (φ k)) → ℝ → Observation → ENNReal)
    (F : ℝ → ℝ) : Problem :=
  ⟨(fun k => p.1 (φ k)), (fun k => resolution p (φ k)), K, M, D,
    length p, rate p, angularRate p, angularLength p,
    (fun k => weight p (φ k)), (fun k => prior p (φ k)), E, ρ,
    (fun _ _ _ _ => 0), F⟩

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
