-- Lane B: the restoration in normalized coordinates, from the data at single events.
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EventNumerator
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.AeTransfer
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.BranchRestoration
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.GraphExtensions
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.NormalizedRestorationProof

/-!
# Restoration in normalized coordinates (lane B, step 4)

The zoomed branch `f`, a law of retained events `μe` on `Core` with base points `X e` (relative
density at most `A`), and, at every retained event, seven tubes of group points of its fine state
with the potential's cubic tests at their anchors, give a quadratic `Q` in `(u, w)` on a ball
carrying a fixed power of the law (the quadratic is certified on the doubled ball): small on the tube of the graph `w = f u`, with a regular
signed hidden derivative and a curvature at most `A^C / Eb`, where `Eb = εc + b + Mz hδ` is the
total test precision (potential cubic tests, tube width, potential transfer).

The affine scale `s0` of `f` on the unit ball decides: if `s0 ≤ A^C Eb` the affine approximant is
the quadratic (curvature zero); otherwise the per-event tests (`event_cleared_bound`, through the
potential when `s0 ≥ Mz`, directly otherwise) hold almost everywhere (`AeTransfer`) and
`branch_restoration` applies.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial FubiniHessian QuadraticTube
open scoped ENNReal

/-- **Normalized restoration.** -/
theorem normalized_restoration (hR : DenseJet.SheetRemezAssertion) (d : ℕ) :
    ∃ (Ab : ℝ) (CW : ℕ), 2 ≤ Ab ∧ 1 ≤ CW ∧
    ∀ (A : ℝ), Ab ≤ A →
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ 2 * (d + 1) →
      U.totalDegree ≤ 2 * (d + 1) → V.totalDegree ≤ 2 * (d + 1) →
      W.totalDegree ≤ 2 * (d + 1) → Δ ≠ 0 → W ≠ 0 →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      DifferentiableOn ℂ sq (ball 0 4) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, eval (fun i => z i) W ≠ 0) →
      ContDiffOn ℂ ⊤ F (ball 0 4) → ContDiffOn ℝ 6 f (ball 0 3) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      HasRealExtension (864 * (2 * (d + 1)) + 2) f →
    ∀ {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ Vc a : ℝ}
      {Bδ Cδ : MvPolynomial (Fin 3) ℝ},
      S0.totalDegree ≤ 2 → P0.totalDegree ≤ d →
      2 ≤ A₁ → A₁ ≤ A → 0 < εfit → 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹ →
      (∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
        eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
        a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
        2 * a * w + eval (fun i => z i) Bδ) →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μe : Measure Ω) (Core : Set Ω) (X : Ω → Base),
      MeasurableSet Core → Measurable X → μe Core ≠ 0 → μe Core ≠ ⊤ →
      (∀ E : Set Base, MeasurableSet E →
        μe (Core ∩ X ⁻¹' E) ≤ ENNReal.ofReal A * μe Core * volume E) →
    ∀ (b hδ εc Mz Vf : ℝ), 0 < b → 0 ≤ hδ → 0 ≤ εc → 0 ≤ Mz → 0 ≤ Vf →
      (∀ m, |P0.coeff m| ≤ Mz) →
      εfit * A₁ ^ 19 ≤ A * b →
      hδ * A ^ CW ≤ 1 → (εc + b + Mz * hδ) * A ^ CW ≤ 1 →
      (∀ e ∈ Core, X e ∈ ball (0 : Base) (1 / 2) ∧ |f (X e)| ≤ Vf ∧
        (2 * A₁)⁻¹ ≤ |2 * a * f (X e) + eval (fun i => X e i) Bδ| ∧
        ∃ p y : Fin 7 → Base, (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) ∧
          (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
            A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) ∧
          (∀ i, CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc A 1 hδ (X e) (p i)) ∧
          (∀ i, ‖y i‖ ≤ 1 ∧ ‖X e - y i‖ ≤ hδ ∧
            |iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i)| ≤ εc)) →
    ∃ (c : Base) (r : ℝ) (Q : Poly), ‖c‖ ≤ 1 / 2 ∧ (A ^ CW)⁻¹ ≤ r ∧ r ≤ 1 / 2 ∧
      Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ A ^ CW * (1 + Vf + (εc + b + Mz * hδ)⁻¹) ^ 5) ∧
      μe Core ≤ ENNReal.ofReal (A ^ CW) * μe (Core ∩ X ⁻¹' ball c r) ∧
      ∀ u ∈ closedBall c (2 * r), ∀ w : ℝ, A ^ CW * |w - f u| ≤ εc + b + Mz * hδ →
        |ev Q u w| ≤ A ^ CW * (εc + b + Mz * hδ + |w - f u|) ∧
        (A ^ CW)⁻¹ ≤ ev (pderiv (3 : Fin 4) Q) u w ∧ ev (pderiv (3 : Fin 4) Q) u w ≤ A ^ CW ∧
        |ev (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) u w| ≤ A ^ CW / (εc + b + Mz * hδ) := by
  exact normalized_restoration_verified hR d

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
