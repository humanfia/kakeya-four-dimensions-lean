import Submission.Obl.k4_raw_earlier_witness_normalization.Coordinates

namespace Submission.Obl.k4_raw_earlier_witness_normalization

open MeasureTheory
open scoped ENNReal BigOperators

abbrev Poly := MvPolynomial (Fin 4) ℝ

def scalarY (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 1

def scalarX (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

def normalizedBounds (K δ : ℝ) (P S : Poly) (p : Point) : Prop :=
  ‖baseProjection p‖ ≤ K ∧
  |MvPolynomial.eval (fun i => p i) P| ≤ K * δ ∧
  K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 P)| ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 P)| ≤ K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K / δ ∧
  |MvPolynomial.eval (fun i => p i) S| ≤ K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 S)| ≤ K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 S))| ≤ K

def rawBounds (K δ t₀ q B : ℝ) (c u : Plane) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (P S : Poly) (p : Point) : Prop :=
  ‖baseProjection (earlierCoordinates t₀ q B c u D p)‖ ≤ K ∧
  |MvPolynomial.eval (fun i => p i) P| ≤ K * δ ∧
  B * K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 P)| ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 P)| ≤ B * K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ B ^ 2 * (K / δ) ∧
  |MvPolynomial.eval (fun i => p i) S| ≤ K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 S)| ≤ B * K ∧
  |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 S))| ≤ B ^ 2 * K

def Support (N χ d s m : ℝ) (C : ℕ) (R : Fin C → ENNReal)
    (μ : Fin C → Measure Incidence) (b : Fin C → (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ) : Prop :=
  ∃ (J : ℕ) (w : Fin J → ENNReal) (Λ : Fin J → Measure Point)
    (P S : Fin J → Poly) (tag : Fin C → Incidence → Fin J)
    (A : Fin C → Set Incidence) (z : Fin C → Fin J → Incidence → Point),
    (∑ e, w e) ≤ 1 ∧ 2 ≤ N ^ χ ∧
    (∀ e, IsProbabilityMeasure (Λ e) ∧ (P e).totalDegree ≤ 2 ∧ (S e).totalDegree ≤ 2 ∧
      (Λ e).map baseProjection ≤ ENNReal.ofReal (N ^ χ) • volume ∧
      ∀ᵐ p ∂Λ e, normalizedBounds (N ^ χ) (N ^ (-s + χ)) (P e) (S e) p) ∧
    (∀ a, 0 < R a ∧ Measurable (tag a) ∧ MeasurableSet (A a) ∧
      μ a (A a)ᶜ = 0 ∧ ∀ e, Measurable (z a e)) ∧
    (∀ e, (∑ a, R a • (μ a |>.restrict {p | p ∈ A a ∧ tag a p = e}).map (z a e)) ≤
      w e • Λ e) ∧
    (∀ a p, p ∈ A a → scalarX (b a p.1) p.2 =
      MvPolynomial.eval (fun i => z a (tag a p) p i) (S (tag a p))) ∧
    (∀ a t y, ((@Finset.filter (Fin J) (fun e => ∃ p ∈ A a,
      |p.2 - t| ≤ N ^ (-m) ∧ |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e) (fun _ => Classical.propDecidable _) Finset.univ).card : ℝ) ≤
      N ^ (d * s + χ)) ∧
    ∀ a p, p ∈ A a → ∀ p', p' ∈ A a → tag a p = tag a p' →
      |p.2 - p'.2| ≤ N ^ (-m) → |scalarY (b a p.1) p.2 - scalarY (b a p'.1) p'.2| ≤ N ^ (-m) →
      ‖baseProjection (z a (tag a p) p) - baseProjection (z a (tag a p) p')‖ ≤ N ^ (-s + χ)

def RawSupport (N χ d s m : ℝ) (C : ℕ) (R : Fin C → ENNReal)
    (μ : Fin C → Measure Incidence) (b : Fin C → (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ) : Prop :=
  0 < χ ∧ 2 ≤ N ∧ 2 ≤ N ^ χ ∧
  ∃ (J : ℕ) (w : Fin J → ENNReal) (ρ : Fin J → Measure Point)
    (P S : Fin J → Poly) (t₀ q B : Fin J → ℝ) (c u : Fin J → Plane)
    (D : Fin J → Matrix (Fin 2) (Fin 2) ℝ) (tag : Fin C → Incidence → Fin J)
    (A : Fin C → Set Incidence) (z : Fin C → Incidence → Point)
    (n center velocity : Fin C → Plane) (thickness α : Fin C → ℝ),
    (∑ e, w e * ρ e Set.univ) ≤ 1 ∧
    (∀ e, 0 < q e ∧ 0 < B e ∧ (D e).det ≠ 0 ∧
      0 < ρ e Set.univ ∧ ρ e Set.univ < ⊤ ∧ (P e).totalDegree ≤ 2 ∧ (S e).totalDegree ≤ 2 ∧
      (ρ e).map baseProjection ≤
        (ENNReal.ofReal (N ^ χ / (q e * |(D e).det|)) * ρ e Set.univ) • volume ∧
      ∀ᵐ p ∂ρ e, rawBounds (N ^ χ) (N ^ (-s + χ)) (t₀ e) (q e) (B e) (c e) (u e) (D e)
        (P e) (S e) p) ∧
    (∀ a, 0 < R a ∧ Measurable (tag a) ∧ MeasurableSet (A a) ∧
      μ a (A a)ᶜ = 0 ∧ Measurable (z a)) ∧
    (∀ e, (∑ a, R a • (μ a |>.restrict {p | p ∈ A a ∧ tag a p = e}).map (z a)) ≤ w e • ρ e) ∧
    (∀ a p, p ∈ A a → scalarX (b a p.1) p.2 = MvPolynomial.eval (fun i => z a p i) (S (tag a p))) ∧
    (∀ a t y (I : Finset (Fin J)), (∀ e ∈ I, ∃ p ∈ A a,
      |p.2 - t| ≤ N ^ (-m) ∧ |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e) →
      ∃ v : ℝ, 0 < v ∧ (∀ e ∈ I, ENNReal.ofReal v ≤ ρ e Set.univ) ∧
      (∑ e ∈ I, ρ e Set.univ) ≤ ENNReal.ofReal (v * N ^ (d * s + χ))) ∧
    ∀ a, ‖n a‖ = 1 ∧ 0 ≤ thickness a ∧
      (∀ p ∈ A a, z a p 0 = p.2 ∧
        scalarY (b a p.1) p.2 = α a + inner ℝ (normalTangent (n a)) (rawPlanar (z a p)) ∧
        |inner ℝ (n a) (rawPlanar (z a p) - center a - p.2 • velocity a)| ≤ thickness a) ∧
      ∀ e, (∃ p ∈ A a, tag a p = e) →
        |(q e)⁻¹| + ‖Matrix.toEuclideanLin (D e)⁻¹ (normalTangent (n a))‖ +
          ‖Matrix.toEuclideanLin (D e)⁻¹ ((inner ℝ (n a) (velocity a)) • n a - u e)‖ ≤
          N ^ (m - s + χ) / 8 ∧
        thickness a * ‖Matrix.toEuclideanLin (D e)⁻¹ (n a)‖ ≤ N ^ (-s + χ) / 8

end Submission.Obl.k4_raw_earlier_witness_normalization
