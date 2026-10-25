import Submission.Obl.k4_finite_width_output_exclusion.Models
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_raw_native_atlas_normalization

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Frame := Matrix (Fin 2) (Fin 2) ℝ
abbrev Test := MvPolynomial (Fin 4) ℝ

/-- The part of validity that does not assert density homogeneity. -/
def Raw (p : Data) : Prop :=
  (∀ k, 2 ≤ p.N k) ∧ Tendsto p.N atTop atTop ∧
  ((∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε) ∧
  0 < p.L ∧ 0 < p.d ∧ p.d < 1 ∧ 0 < p.S ∧ 0 < p.η ∧
  (∃ M D : ℕ, ∀ k,
    (p.W k : ℝ) ≤ p.N k ^ M ∧
    (∀ γ, 0 ≤ p.ω k γ) ∧ (∑ γ, p.ω k γ) = 1 ∧
    (∀ γ, IsProbabilityMeasure (p.ν k γ) ∧
      0 < p.B k γ ∧ p.B k γ ≤ p.N k ^ M ∧ (p.B k γ)⁻¹ ≤ p.N k ^ M ∧
      (p.P k γ).totalDegree ≤ 2 ∧ (∀ b, |(p.P k γ).coeff b| ≤ p.N k ^ M) ∧
      (∃ m : ℕ, (m : ℝ) ≤ p.N k ^ M ∧
        ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)),
          (∀ j, 0 ≤ c j ∧ c j ≤ p.N k ^ M ∧ (i j : ℝ) ≤ p.N k ^ M ∧
            fmt 6 (p.N k ^ M) D (A j) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ p.N k ^ M)) ∧
          p.ν k γ = ∑ j, ENNReal.ofReal (c j) •
            Measure.map (fun x => (i j, x)) (volume.restrict (A j))) ∧
      MeasurableSet (p.E k γ) ∧ p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
      (∀ z ∈ p.E k γ, (z.1.1 : ℝ) ≤ p.N k ^ M ∧ ∀ e, |z.1.2 e| ≤ p.N k ^ M) ∧
      (∀ i, fmt 7 (p.N k ^ M) D
        {z : Fin 7 → ℝ | ((i, fun j => z j.castSucc), z 6) ∈ p.E k γ}) ∧
      (∀ᵐ l ∂p.ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖y l t‖ + ‖v l‖ ≤ p.K k ∧ |MvPolynomial.eval (x l t) (p.P k γ)| ≤ p.K k ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))| ≤ p.K k * p.B k γ ∧
        |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4)
          (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ)))| ≤ p.K k * (p.B k γ) ^ 2) ∧
      (∀ᵐ z ∂((p.ν k γ).prod volume).restrict (p.E k γ),
        p.B k γ / p.K k ≤
          |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4) (p.P k γ))|)) ∧
    ENNReal.ofReal ((p.K k)⁻¹) ≤
      ∑ γ, ENNReal.ofReal (p.ω k γ) * (((p.ν k γ).prod volume).restrict (p.E k γ)) Set.univ)

/-- The explicit raw normalization certificate in the frozen statement. -/
def Certificate (p q : Data) (r h w : ℝ) : Prop :=
  ∃ (φ : ℕ → ℕ) (M D : ℕ) (κ : ℕ → ℝ) (T C : ℕ → ℕ)
    (γ : (k : ℕ) → Fin (C k) → Fin (p.W (φ k)))
    (j : (k : ℕ) → Fin (C k) → Fin (2 ^ T k))
    (c u : (k : ℕ) → Fin (C k) → Plane)
    (Q : (k : ℕ) → Fin (C k) → Frame)
    (R : (k : ℕ) → Fin (C k) → Test)
    (A : (k : ℕ) → Fin (C k) → Set Trajectory)
    (F : (k : ℕ) → Fin (C k) → Set Incidence)
    (β : (k : ℕ) → Fin (q.W k) ≃ Fin (C k)) (error : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (q.W k) → Trajectory ≃ᵐ Trajectory)
    (lst : (k : ℕ) → Fin (p.W (φ k)) → Observation → Finset (Fin (C k))) (Z : ℕ → ℝ),
    StrictMono φ ∧ (∀ k, q.N k = p.N (φ k)) ∧ Raw q ∧
    q.L = p.L - r ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
    (∀ k, 0 < error k) ∧ (∀ k, error k ≤ 1) ∧ Tendsto error atTop (nhds 0) ∧
    (∀ k, (C k : ℝ) ≤ p.N (φ k) ^ M ∧
      (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' → Disjoint (A k b) (A k b')) ∧
      ∀ b, chart (p.N (φ k)) M D (κ k) (T k) (j k b : ℝ) r
        (p.B (φ k) (γ k b)) (p.E (φ k) (γ k b)) (c k b) (u k b) (Q k b) (R k b)
        (A k b) (F k b) (∀ z ∈ F k b,
          b ∈ lst k (γ k b) (obs (p.B (φ k) (γ k b)) (δ (p.N (φ k)) p.L) z))) ∧
    (∀ k, 1 ≤ κ k) ∧ (∀ k, p.K (φ k) ≤ κ k) ∧
    (∀ k, κ k ≤ p.N (φ k) ^ error k) ∧
    (∀ k, (2 : ℝ) ^ T k ≤ p.N (φ k) ^ (h + error k)) ∧
    (∀ k b, |Matrix.det (Q k b)| * (4 : ℝ) ^ T k ≤ p.N (φ k) ^ (-w + error k)) ∧
    (∀ k b l, (θ k b l).1 = l.1) ∧
    (∀ k b l t, y (θ k b l) t = Matrix.toEuclideanLin (Q k (β k b))⁻¹
      (y l ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) -
        c k (β k b) - ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) • u k (β k b))) ∧
    (∀ k b l t, x (θ k b l) t 3 =
      x l ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) 3) ∧
    (∀ k b, 0 < p.ν (φ k) (γ k (β k b)) (A k (β k b))) ∧
    (∀ k b, (p.ν (φ k) (γ k (β k b)) (A k (β k b))).toReal⁻¹ ≤ p.N (φ k) ^ M) ∧
    (∀ k b, q.ν k b = (p.ν (φ k) (γ k (β k b)) (A k (β k b)))⁻¹ •
      Measure.map (θ k b) ((p.ν (φ k) (γ k (β k b))).restrict (A k (β k b)))) ∧
    (∀ k b z, z ∈ q.E k b →
      ((θ k b).symm z.1, (j k (β k b) : ℝ) / (2 : ℝ) ^ T k + z.2 / (2 : ℝ) ^ T k) ∈ F k (β k b)) ∧
    (∀ k b, q.B k b = p.B (φ k) (γ k (β k b)) / δ (p.N (φ k)) r) ∧
    (∀ k, 0 < Z k) ∧ (∀ k, (κ k)⁻¹ ≤ Z k) ∧ (∀ k, Z k ≤ 1) ∧
    (∀ k, Z k = ∑ b, p.ω (φ k) (γ k b) / (2 : ℝ) ^ T k *
      (p.ν (φ k) (γ k b) (A k b)).toReal) ∧
    (∀ k b, q.ω k b = (p.ω (φ k) (γ k (β k b)) / (2 : ℝ) ^ T k *
      (p.ν (φ k) (γ k (β k b)) (A k (β k b))).toReal) / Z k) ∧
    (∀ k γ₀ o, ((lst k γ₀ o).card : ℝ) ≤ κ k) ∧
    (∀ k b (z : Fin 4 → ℝ), (fun t : ℝ => MvPolynomial.eval z (q.P k b) =
      MvPolynomial.eval ![t,
        (c k (β k b)) 0 + t * (u k (β k b)) 0 + (Q k (β k b)) 0 0 * z 1 + (Q k (β k b)) 0 1 * z 2,
        (c k (β k b)) 1 + t * (u k (β k b)) 1 + (Q k (β k b)) 1 0 * z 1 + (Q k (β k b)) 1 1 * z 2,
        z 3] (R k (β k b)) / δ (p.N (φ k)) r)
        ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + z 0 / (2 : ℝ) ^ T k))

end Submission.Obl.k4_raw_native_atlas_normalization
