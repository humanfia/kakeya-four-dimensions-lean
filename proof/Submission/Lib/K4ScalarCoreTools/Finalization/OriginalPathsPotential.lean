/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/OriginalPathsPotential.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: o062/x0511,3449a92e, OriginalPathsPotential.lean.
Mass-curl and polynomial primitives are imported; the original long-row fit is accepted K4ScalarActualSwitching.LongRowPotential.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.RelativeMassCurl
import Submission.Lib.K4ScalarCoreTools.Simulation.ConservativePotential
import Submission.Lib.K4ScalarActualSwitching.LongRowPotential

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching
open Submission.Lib.K4ScalarCoreTools.Simulation
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Lib.K4PolynomialPotential

/-- Raw original path success, base domination and the physical endpoint
cover give a bounded, almost conservative, explicitly specified potential. -/
theorem exists_original_path_potential_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K L M p area ε : ℝ, 1 ≤ K → 1 ≤ L → 1 ≤ M →
        0 < p → p ≤ 1 → 0 ≤ area → 0 ≤ ε →
        (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z A| ≤ K ∧ |eval z B| ≤ K) →
        ∀ (Θ : Type*) [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
          (μ : Measure (Θ × (Fin 4 → ℝ))) (S : Set (Θ × (Fin 4 → ℝ)))
          (x : Θ → Fin 2 → ℝ) (v : Θ → Fin 4 → ℝ) (X₀ : Θ → ℝ)
          (ι : Type*) (F : Finset ι) (E : Θ → ι → Set (Fin 2 → ℝ)) (c : Θ → ι → ℝ),
          Measurable x → MeasurableSet S →
          ν.map x ≤ ENNReal.ofReal (M * (ν univ).toReal) • volume →
          μ ≤ ENNReal.ofReal L • (ν.prod volume) →
          ENNReal.ofReal (p * (ν univ).toReal) ≤ μ S →
          (∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1) →
          (∀ z ∈ S, x z.1 ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧
              1 / K ≤ |v z.1 3 - v z.1 2|) →
          (∀ θ, ∀ i ∈ F, MeasurableSet (E θ i)) →
          (∀ θ, (∑ i ∈ F, volume (E θ i)) ≤ ENNReal.ofReal area) →
          (∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x z.1) (v z.1) z.2 ∈ E z.1 i ∧
            |X₀ z.1 + eval z.2 (brokenHeight A B (x z.1) (v z.1)) - c z.1 i| ≤ ε) →
          let P := polynomialPotential A B
          P.totalDegree ≤ D + 2 ∧ pderiv 1 P = B ∧ eval (0 : Fin 2 → ℝ) P = 0 ∧
          ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ 2 * K ∧
            |eval z (pderiv 0 P) - eval z A| ≤
              C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := by
  obtain ⟨C, hC, hcurl⟩ := exists_original_relative_mass_curl_constant D
  refine ⟨((D : ℝ) + 1) ^ 2 * C, by positivity, ?_⟩
  intro A B hA hB K L M p area ε hK hL hM hp hp1 harea hε hnorm
    Θ _ ν _ _ μ S x v X₀ ι F E c hx hS hbase hdom hmass hbox hdata hE hareaSum hcover
  let R := C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoeff : ∀ e : Fin 2 →₀ ℕ, |(pderiv 0 B - pderiv 1 A).coeff e| ≤ R :=
    hcurl A B hA hB K L M p area ε hK hL hM hp hp1 harea hε
      Θ ν μ S x v X₀ ι F E c hx hS hbase hdom hmass hbox hdata hE hareaSum hcover
  have hdegree : (pderiv 0 B - pderiv 1 A).totalDegree ≤ D := by
    apply (totalDegree_sub _ _).trans
    exact max_le
      ((Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le B 0).trans
        ((Nat.sub_le _ _).trans hB))
      ((Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le A 1).trans
        ((Nat.sub_le _ _).trans hA))
  have hvalue : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv 0 B - pderiv 1 A)| ≤ ((D + 1) ^ 2 : ℕ) * R := by
    intro z hz
    exact (eval_le_coefficientMass_on_unit _ z hz).trans
      (Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientMass.coefficientMass_le_of_coeff_bound
        _ hdegree hR hcoeff)
  refine ⟨polynomialPotential_totalDegree A B hA hB, polynomialPotential_spatial A B,
    polynomialPotential_eval_zero A B, ?_⟩
  intro z hz
  refine ⟨polynomialPotential_eval_bound A B (by linarith)
    (fun y hy => (hnorm y hy).1) (fun y hy => (hnorm y hy).2) z hz, ?_⟩
  calc
    _ ≤ (((D + 1) ^ 2 : ℕ) * R) * |z 1| := polynomialPotential_time_error_bound A B hvalue z hz
    _ ≤ ((D + 1) ^ 2 : ℕ) * R := mul_le_of_le_one_right (by positivity)
      (abs_le.mpr ⟨hz.1 1, hz.2 1⟩)
    _ = (((D : ℝ) + 1) ^ 2 * C) * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε /
        p ^ (6 * D + 1) := by
      dsimp [R]
      push_cast
      ring

/-- Qualification on an original long row yields an explicit quadratic
fit to the common potential along that entire affine line. The row need
not contain any interval or any fixed sample tuple. -/
theorem polynomialPotential_fit_of_original_long_row
    (A B : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D)
    (S : Polynomial ℝ) (hS : S.natDegree ≤ 2) (u v : ℝ)
    (T : Set ℝ) {η δ R : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hT : T ⊆ Icc (-1 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume T)
    (hpath : ∀ t ∈ T, (![t, u + t * v] : Fin 2 → ℝ) ∈ Icc (-1 : Fin 2 → ℝ) 1)
    (hrow : ∀ t ∈ T, |S.derivative.eval t - (eval ![t, u + t * v] A +
      v * eval ![t, u + t * v] B)| ≤ δ)
    (hgradient : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv 0 (polynomialPotential A B)) - eval z A| ≤ R) :
    (Submission.Lib.K4ScalarActualSwitching.potentialLineQuadratic
      (polynomialPotential A B) S u).natDegree ≤ 2 ∧
    ∀ t ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v] (polynomialPotential A B) -
        (Submission.Lib.K4ScalarActualSwitching.potentialLineQuadratic
          (polynomialPotential A B) S u).eval t| ≤
        (16 * ((D : ℝ) + 5) / η) ^ (D + 4) * (δ + R) := by
  refine ⟨Submission.Lib.K4ScalarActualSwitching.natDegree_potentialLineQuadratic _ S u hS, ?_⟩
  intro t ht
  have hfit := Submission.Lib.K4ScalarActualSwitching.potential_fit_of_long_row_gradient_bounds
    (polynomialPotential A B) A B (D + 2) (polynomialPotential_totalDegree A B hA hB)
    S hS u v T hη hη1 hδ hR (show (0 : ℝ) ≤ 0 by rfl) hT hmass hrow
    (fun s hs => hgradient _ (hpath s hs))
    (fun s hs => by rw [polynomialPotential_spatial]; simp) t ht
  norm_num [Nat.cast_add, add_assoc, Nat.add_assoc] at hfit
  exact hfit

end Submission.Lib.K4ScalarCoreTools.Finalization
