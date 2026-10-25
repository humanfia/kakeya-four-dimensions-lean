import Submission.Obl.k4_finite_width_output_exclusion.Interfaces

/-! Models of the raw certificate and the calibrated remainder. The exact native
problem and chart predicates are imported from accepted o153. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

abbrev Data := Submission.Obl.k4_finite_width_output_exclusion.Data
abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ
abbrev JointObservation := Observation × (Fin 2 → ℤ)
abbrev Spatial := EuclideanSpace ℝ (Fin 2)
abbrev Test := MvPolynomial (Fin 4) ℝ
abbrev Frame := Matrix (Fin 2) (Fin 2) ℝ

/-- The raw predicate from the frozen hypothesis, before any density profile. -/
noncomputable def RawProblem := (fun (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) => (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ)) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)))

noncomputable def RawValid (p : Data) : Prop :=
  RawProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B

/-- All the geometry retained through subsequences, world selection, and
incidence selection. No density conclusion is included here. -/
structure RemainderGeometry (p q : Data) (r h w : ℝ) where
  φ : ℕ → ℕ
  increasing : StrictMono φ
  same_base : ∀ k, q.N k = p.N (φ k)
  length : q.L = p.L - r
  density_cap : q.d = p.d
  angular_rate : q.S = p.S
  angular_range : q.η = p.η
  M : ℕ
  D : ℕ
  κ : ℕ → ℝ
  parent : (k : ℕ) → Atlas p (φ k)
  worlds : (k : ℕ) → Fin (q.W k) ≃ Fin (parent k).C
  error : ℕ → ℝ
  error_pos : ∀ k, 0 < error k
  error_le_one : ∀ k, error k ≤ 1
  error_limit : Tendsto error atTop (nhds 0)
  parent_valid : ∀ k,
    ((parent k).C : ℝ) ≤ p.N (φ k) ^ M ∧
    (∀ b b', b ≠ b' → (parent k).γ b = (parent k).γ b' →
      (parent k).j b = (parent k).j b' → Disjoint ((parent k).A b) ((parent k).A b')) ∧
    ∀ b, chart (p.N (φ k)) M D (κ k) (parent k).T ((parent k).j b : ℝ) r
      (p.B (φ k) ((parent k).γ b)) (p.E (φ k) ((parent k).γ b))
      ((parent k).c b) ((parent k).u b) ((parent k).Q b) ((parent k).R b)
      ((parent k).A b) ((parent k).F b) True
  slack_one : ∀ k, 1 ≤ κ k
  old_slack : ∀ k, p.K (φ k) ≤ κ k
  slack_bound : ∀ k, κ k ≤ p.N (φ k) ^ error k
  time_bound : ∀ k, (2 : ℝ) ^ (parent k).T ≤ p.N (φ k) ^ (h + error k)
  width_bound : ∀ k b, |Matrix.det ((parent k).Q b)| * (4 : ℝ) ^ (parent k).T ≤
    p.N (φ k) ^ (-w + error k)
  θ : (k : ℕ) → Fin (q.W k) → Trajectory ≃ᵐ Trajectory
  index_preserved : ∀ k b l, (θ k b l).1 = l.1
  planar_map : ∀ k b l t,
    y (θ k b l) t = Matrix.toEuclideanLin ((parent k).Q (worlds k b))⁻¹
      (y l (((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
        t / (2 : ℝ) ^ (parent k).T) - (parent k).c (worlds k b) -
        (((parent k).j (worlds k b) : ℝ) / (2 : ℝ) ^ (parent k).T +
          t / (2 : ℝ) ^ (parent k).T) • (parent k).u (worlds k b))
  hidden_map : ∀ k b l t,
    x (θ k b l) t 3 = x l (((parent k).j (worlds k b) : ℝ) /
      (2 : ℝ) ^ (parent k).T + t / (2 : ℝ) ^ (parent k).T) 3
  prior_pos : ∀ k b, 0 < p.ν (φ k) ((parent k).γ (worlds k b))
    ((parent k).A (worlds k b))
  prior_inverse_bound : ∀ k b,
    (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal⁻¹ ≤
      p.N (φ k) ^ M
  conditioned_prior : ∀ k b, q.ν k b =
    (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b)))⁻¹ •
      Measure.map (θ k b)
        ((p.ν (φ k) ((parent k).γ (worlds k b))).restrict ((parent k).A (worlds k b)))
  selected_pullback : ∀ k b z, z ∈ q.E k b →
    ((θ k b).symm z.1, ((parent k).j (worlds k b) : ℝ) /
      (2 : ℝ) ^ (parent k).T + z.2 / (2 : ℝ) ^ (parent k).T) ∈
      (parent k).F (worlds k b)
  derivative_unit : ∀ k b, q.B k b = p.B (φ k) ((parent k).γ (worlds k b)) /
    δ (p.N (φ k)) r
  Z : ℕ → ℝ
  normalizer_pos : ∀ k, 0 < Z k
  normalizer_lower : ∀ k, (κ k)⁻¹ ≤ Z k
  normalizer_upper : ∀ k, Z k ≤ 1
  normalizer_sum : ∀ k, Z k = ∑ b,
    p.ω (φ k) ((parent k).γ b) / (2 : ℝ) ^ (parent k).T *
      (p.ν (φ k) ((parent k).γ b) ((parent k).A b)).toReal
  world_weights : ∀ k b, q.ω k b =
    (p.ω (φ k) ((parent k).γ (worlds k b)) / (2 : ℝ) ^ (parent k).T *
      (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal) / Z k

/-- The full raw hypothesis: geometric transport, a tempered family, and the
original terminal observation lists. -/
structure RawRemainder (p q : Data) (r h w : ℝ) extends RemainderGeometry p q r h w where
  raw_valid : RawValid q
  listed : ∀ k b z, z ∈ (parent k).F b →
    b ∈ (parent k).lst ((parent k).γ b)
      (obs (p.B (φ k) ((parent k).γ b)) (δ (p.N (φ k)) p.L) z)
  list_bound : ∀ k a o, (((parent k).lst a o).card : ℝ) ≤ κ k

/-- The desired genuine remainder has within-world terminal calibration. -/
structure CalibratedRemainder (p q : Data) (r h w : ℝ) extends RemainderGeometry p q r h w where
  valid : Valid q
  terminal_calibration : ∀ k b,
    p.N (φ k) ^ (-p.f p.L) * |Matrix.det ((parent k).Q (worlds k b))| ≤
      κ k * (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal *
        q.N k ^ (-q.f q.L)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
