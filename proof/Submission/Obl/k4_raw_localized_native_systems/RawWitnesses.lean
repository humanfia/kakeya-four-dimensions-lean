/- Adapted from this LOT tree, o197, session x0721, RawWitnesses.lean,
   commit d876ce83 (retaining the original attribution below). -/
import Submission.Obl.k4_raw_localized_native_systems.SplitInterfaces

/-! A raw earlier-witness interface for the proposed split. Raw laws retain
their actual mass, their original graph coordinates, and the actual earlier
affine frames. The output certificate will normalize both coordinates and laws.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

def rawPlanar (p : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p 1, p 2]

def normalTangent (n : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![n 1, -n 0]

def earlierCoordinates (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![(p 0 - t₀) / q,
    (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - (p 0) • u)) 0,
    (Matrix.toEuclideanLin D⁻¹ (rawPlanar p - c - (p 0) • u)) 1, B * p 3]

/-- Local packing is expressed in the original witness masses. The actual
cardinality of tags and the normalized base diameter are conclusions of the
witness-normalization theorem, not hypotheses here. -/
def RawSupport : CertificateType := fun N χ d s m C R μ b =>
  0 < χ ∧ 2 ≤ N ∧ 2 ≤ N ^ χ ∧
  ∃ (J : ℕ) (w : Fin J → ENNReal)
    (ρ : Fin J → Measure (EuclideanSpace ℝ (Fin 4)))
    (P S : Fin J → MvPolynomial (Fin 4) ℝ)
    (t₀ q B : Fin J → ℝ) (c u : Fin J → EuclideanSpace ℝ (Fin 2))
    (D : Fin J → Matrix (Fin 2) (Fin 2) ℝ)
    (tag : Fin C → ((ℕ × (Fin 6 → ℝ)) × ℝ) → Fin J)
    (A : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (z : Fin C → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 4))
    (n center velocity : Fin C → EuclideanSpace ℝ (Fin 2))
    (thickness α : Fin C → ℝ),
    (∑ e, w e * ρ e Set.univ) ≤ 1 ∧
    (∀ e, 0 < q e ∧ 0 < B e ∧ Matrix.det (D e) ≠ 0 ∧
      0 < ρ e Set.univ ∧ ρ e Set.univ < ⊤ ∧
      (P e).totalDegree ≤ 2 ∧ (S e).totalDegree ≤ 2 ∧
      Measure.map base4 (ρ e) ≤
        (toE (N ^ χ / (q e * |Matrix.det (D e)|)) * ρ e Set.univ) • volume ∧
      ∀ᵐ p ∂ρ e,
        ‖base4 (earlierCoordinates (t₀ e) (q e) (B e) (c e) (u e) (D e) p)‖ ≤ N ^ χ ∧
        |MvPolynomial.eval (fun i => p i) (P e)| ≤ N ^ χ * N ^ (-s + χ) ∧
        B e * (N ^ χ)⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (P e))| ∧
        |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (P e))| ≤ B e * N ^ χ ∧
        |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P e)))| ≤ (B e) ^ 2 * (N ^ χ / N ^ (-s + χ)) ∧
        |MvPolynomial.eval (fun i => p i) (S e)| ≤ N ^ χ ∧
        |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (S e))| ≤ B e * N ^ χ ∧
        |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (S e)))| ≤ (B e) ^ 2 * N ^ χ) ∧
    (∀ a, 0 < R a ∧ Measurable (tag a) ∧ MeasurableSet (A a) ∧ μ a (A a)ᶜ = 0 ∧
      Measurable (z a)) ∧
    (∀ e, (∑ a, R a • Measure.map (z a) ((μ a).restrict {p | p ∈ A a ∧ tag a p = e})) ≤ w e • ρ e) ∧
    (∀ a p, p ∈ A a → scalarX (b a p.1) p.2 =
      MvPolynomial.eval (fun i => z a p i) (S (tag a p))) ∧
    (∀ a t y (I : Finset (Fin J)),
      (∀ e ∈ I, ∃ p ∈ A a, |p.2 - t| ≤ N ^ (-m) ∧
        |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e) →
      ∃ v : ℝ, 0 < v ∧ (∀ e ∈ I, toE v ≤ ρ e Set.univ) ∧
        (∑ e ∈ I, ρ e Set.univ) ≤ toE (v * N ^ (d * s + χ))) ∧
    (∀ a, ‖n a‖ = 1 ∧ 0 ≤ thickness a ∧
      (∀ p ∈ A a, z a p 0 = p.2 ∧
        scalarY (b a p.1) p.2 = α a + inner ℝ (normalTangent (n a)) (rawPlanar (z a p)) ∧
        |inner ℝ (n a) (rawPlanar (z a p) - center a - p.2 • velocity a)| ≤ thickness a) ∧
      ∀ e, (∃ p ∈ A a, tag a p = e) →
        |(q e)⁻¹| + ‖Matrix.toEuclideanLin (D e)⁻¹ (normalTangent (n a))‖ +
          ‖Matrix.toEuclideanLin (D e)⁻¹ ((inner ℝ (n a) (velocity a)) • n a - u e)‖ ≤
            N ^ (m - s + χ) / 8 ∧
        thickness a * ‖Matrix.toEuclideanLin (D e)⁻¹ (n a)‖ ≤ N ^ (-s + χ) / 8)

def RawLocalizationStatement : Prop :=
  initialRaw → ∀ ds kr S η : ℝ, 0 < S → 0 < η →
    es ds kr S η → ¬ widthRaw ds kr S η → LocalizedSystemsWith RawSupport ds kr S η

def WitnessNormalizationStatement : Prop :=
  ∀ N χ d s m C R μ b, RawSupport N χ d s m C R μ b →
    SupportCertificate N χ d s m C R μ b

theorem statement_of_raw_and_normalization
    (hraw : RawLocalizationStatement) (hnorm : WitnessNormalizationStatement) : Statement := by
  intro hi ds kr S η hS hη hes hnb
  exact (localizedSystemsWith_support_iff ds kr S η).mp
    (localizedSystemsWith_mono hnorm (hraw hi ds kr S η hS hη hes hnb))

end
end Submission.Obl.k4_raw_localized_native_systems
