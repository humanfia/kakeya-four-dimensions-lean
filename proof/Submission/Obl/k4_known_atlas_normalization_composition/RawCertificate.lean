import Submission.Obl.k4_known_atlas_normalization_composition.CutCertificate

/-! Raw native normalization, before choosing any homogeneous density profile.
The terminal-observation lists remain part of this certificate. -/
namespace Submission.Obl.k4_known_atlas_normalization_composition

open MeasureTheory Filter

/-- The numerical, fixed-format, geometric and retained-mass problem clauses;
no homogeneous profile or density-law assumptions occur here. -/
def RawProblem (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (P : (k : ℕ) → Fin (W k) → Test)
    (B : (k : ℕ) → Fin (W k) → ℝ) : Prop :=
  (∀ k, 2 ≤ N k) ∧
  Filter.Tendsto N Filter.atTop Filter.atTop ∧
  ((∀ k, 1 ≤ K k) ∧
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
  0 < L ∧
  0 < d ∧
  d < 1 ∧
  0 < S ∧
  0 < η ∧
  (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧
  (∀ γ, 0 ≤ ω k γ) ∧
  (∑ γ, ω k γ) = 1 ∧
  (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧
  0 < B k γ ∧
  B k γ ≤ N k ^ M ∧
  (B k γ)⁻¹ ≤ N k ^ M ∧
  (P k γ).totalDegree ≤ 2 ∧
  (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧
  (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧
  ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧
  c j ≤ N k ^ M ∧
  (i j : ℝ) ≤ N k ^ M ∧
  (fmt 6 (N k ^ M) D (A j)) ∧
  (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧
  ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧
  MeasurableSet (E k γ) ∧
  E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
  (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧
  ∀ e, |p.1.2 e| ≤ N k ^ M) ∧
  (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧
  (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧
  |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧
  (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧
  ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ)) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))

/-- Native full-assignment normalization with the original terminal lists.
The final test identity is the actual affine quadratic normalization. -/
def RawCertificate (p q : Data) (r h w : ℝ) : Prop :=
  ∃ (φ : ℕ → ℕ) (M D : ℕ) (κ : ℕ → ℝ) (T C : ℕ → ℕ)
    (γ : (k : ℕ) → Fin (C k) → Fin (p.W (φ k)))
    (j : (k : ℕ) → Fin (C k) → Fin (2 ^ T k))
    (c u : (k : ℕ) → Fin (C k) → Spatial)
    (Q : (k : ℕ) → Fin (C k) → Frame)
    (R : (k : ℕ) → Fin (C k) → Test)
    (A : (k : ℕ) → Fin (C k) → Set Trajectory)
    (F : (k : ℕ) → Fin (C k) → Set Incidence)
    (β : (k : ℕ) → Fin (q.W k) ≃ Fin (C k))
    (error : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (q.W k) → Trajectory ≃ᵐ Trajectory)
    (lst : (k : ℕ) → Fin (p.W (φ k)) → Observation → Finset (Fin (C k)))
    (Z : ℕ → ℝ),
  StrictMono φ ∧
  (∀ k, q.N k = p.N (φ k)) ∧
  RawProblem q.N q.K q.L q.d q.S q.η q.W q.ω q.ν q.E q.P q.B ∧ q.L = p.L - r ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
  (∀ k, 0 < error k) ∧ (∀ k, error k ≤ 1) ∧ Tendsto error atTop (nhds 0) ∧
  (∀ k, (C k : ℝ) ≤ p.N (φ k) ^ M ∧
    (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' →
      Disjoint (A k b) (A k b')) ∧
    ∀ b, Chart (p.N (φ k)) M D (κ k) (T k) (j k b : ℝ) r
      (p.B (φ k) (γ k b)) (p.E (φ k) (γ k b))
      (c k b) (u k b) (Q k b) (R k b) (A k b) (F k b)
      (∀ z ∈ F k b, b ∈ lst k (γ k b) (obs (p.B (φ k) (γ k b)) (δ (p.N (φ k)) p.L) z))) ∧
  (∀ k, 1 ≤ κ k) ∧ (∀ k, p.K (φ k) ≤ κ k) ∧
  (∀ k, κ k ≤ p.N (φ k) ^ error k) ∧
  (∀ k, (2 : ℝ) ^ T k ≤ p.N (φ k) ^ (h + error k)) ∧
  (∀ k b, |Matrix.det (Q k b)| * (4 : ℝ) ^ T k ≤ p.N (φ k) ^ (-w + error k)) ∧
  (∀ k b l, (θ k b l).1 = l.1) ∧
  (∀ k b l t, y (θ k b l) t = Matrix.toEuclideanLin (Q k (β k b))⁻¹
    (y l ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) -
      c k (β k b) -
      ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) • u k (β k b))) ∧
  (∀ k b l t, x (θ k b l) t 3 =
    x l ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + t / (2 : ℝ) ^ T k) 3) ∧
  (∀ k b, 0 < p.ν (φ k) (γ k (β k b)) (A k (β k b))) ∧
  (∀ k b, (p.ν (φ k) (γ k (β k b)) (A k (β k b))).toReal⁻¹ ≤ p.N (φ k) ^ M) ∧
  (∀ k b, q.ν k b =
    (p.ν (φ k) (γ k (β k b)) (A k (β k b)))⁻¹ •
      Measure.map (θ k b) ((p.ν (φ k) (γ k (β k b))).restrict (A k (β k b)))) ∧
  (∀ k b z, z ∈ q.E k b →
    ((θ k b).symm z.1,
      (j k (β k b) : ℝ) / (2 : ℝ) ^ T k + z.2 / (2 : ℝ) ^ T k) ∈ F k (β k b)) ∧
  (∀ k b, q.B k b = p.B (φ k) (γ k (β k b)) / δ (p.N (φ k)) r) ∧
  (∀ k, 0 < Z k) ∧ (∀ k, (κ k)⁻¹ ≤ Z k) ∧ (∀ k, Z k ≤ 1) ∧
  (∀ k, Z k = ∑ b, p.ω (φ k) (γ k b) / (2 : ℝ) ^ T k *
    (p.ν (φ k) (γ k b) (A k b)).toReal) ∧
  (∀ k b, q.ω k b =
    (p.ω (φ k) (γ k (β k b)) / (2 : ℝ) ^ T k *
      (p.ν (φ k) (γ k (β k b)) (A k (β k b))).toReal) / Z k) ∧
  (∀ k γ₀ o, ((lst k γ₀ o).card : ℝ) ≤ κ k) ∧
  (∀ k b (z : Fin 4 → ℝ),
    (fun t : ℝ => MvPolynomial.eval z (q.P k b) =
      MvPolynomial.eval
        ![t, (c k (β k b)) 0 + t * (u k (β k b)) 0 +
            (Q k (β k b)) 0 0 * z 1 + (Q k (β k b)) 0 1 * z 2,
          (c k (β k b)) 1 + t * (u k (β k b)) 1 +
            (Q k (β k b)) 1 0 * z 1 + (Q k (β k b)) 1 1 * z 2, z 3]
        (R k (β k b)) / δ (p.N (φ k)) r)
      ((j k (β k b) : ℝ) / (2 : ℝ) ^ T k + z 0 / (2 : ℝ) ^ T k))

end Submission.Obl.k4_known_atlas_normalization_composition
