import Submission.Obl.k4_known_atlas_normalization_composition.Remainder

/-! The concrete remainder certificate, with its Atlas records expanded into
arrays. This provides a Mathlib-only child interface when Data projections and
the predicates are expanded in the frozen types. It adds no lifting hypothesis.
The certificate is that of o151/x0508, commit eb10049. -/

namespace Submission.Obl.k4_known_atlas_normalization_composition

open MeasureTheory Filter

/-- Array form of the calibrated remainder, used to freeze the two cuts. -/
def CutCertificate (p q : Data) (r h w : ℝ) : Prop :=
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
    (Z : ℕ → ℝ),
  StrictMono φ ∧
  (∀ k, q.N k = p.N (φ k)) ∧
  q.Valid ∧ q.L = p.L - r ∧ q.d = p.d ∧ q.S = p.S ∧ q.η = p.η ∧
  (∀ k, 0 < error k) ∧ (∀ k, error k ≤ 1) ∧ Tendsto error atTop (nhds 0) ∧
  (∀ k, (C k : ℝ) ≤ p.N (φ k) ^ M ∧
    (∀ b b', b ≠ b' → γ k b = γ k b' → j k b = j k b' →
      Disjoint (A k b) (A k b')) ∧
    ∀ b, Chart (p.N (φ k)) M D (κ k) (T k) (j k b : ℝ) r
      (p.B (φ k) (γ k b)) (p.E (φ k) (γ k b))
      (c k b) (u k b) (Q k b) (R k b) (A k b) (F k b) True) ∧
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
  (∀ k b, p.N (φ k) ^ (-p.f p.L) * |Matrix.det (Q k (β k b))| ≤
    κ k * (p.ν (φ k) (γ k (β k b)) (A k (β k b))).toReal * q.N k ^ (-q.f q.L))

/-- Bundling or unbundling the certificate changes none of its hypotheses. -/
theorem cutCertificate_iff (p q : Data) (r h w : ℝ) :
    CutCertificate p q r h w ↔ Nonempty (Remainder p q r h w) := by
  constructor
  · rintro ⟨φ, M, D, κ, T, C, γ, j, c, u, Q, R, A, F, β, error, θ, Z,
      hφ, hN, hq, hL, hd, hS, hη, he, he1, he0, hparent, hκ1, hK, hκ,
      hT, hQ, hi, hy, hx, hprior, hpriorInv, hν, hE, hB, hZ0, hZlo,
      hZhi, hZ, hω, hcal⟩
    exact ⟨{
      φ := φ, increasing := hφ, same_base := hN, valid := hq,
      length := hL, density_cap := hd, angular_rate := hS, angular_range := hη,
      M := M, D := D,
      parent := fun k => ⟨κ k, T k, C k, γ k, j k, c k, u k, Q k, R k, A k, F k⟩,
      worlds := β, error := error, error_pos := he, error_le_one := he1,
      error_limit := he0, parent_valid := hparent, slack_one := hκ1,
      old_slack := hK, slack_bound := hκ, time_bound := hT, width_bound := hQ,
      coefficient_map := θ, index_preserved := hi, planar_map := hy,
      hidden_map := hx, prior_pos := hprior, prior_inverse_bound := hpriorInv,
      conditioned_prior := hν, selected_pullback := hE, derivative_unit := hB,
      Z := Z, normalizer_pos := hZ0, normalizer_lower := hZlo,
      normalizer_upper := hZhi, normalizer_sum := hZ, world_weights := hω,
      terminal_calibration := hcal }⟩
  · rintro ⟨a⟩
    exact ⟨a.φ, a.M, a.D, fun k => (a.parent k).κ, fun k => (a.parent k).T,
      fun k => (a.parent k).C, fun k => (a.parent k).γ, fun k => (a.parent k).j,
      fun k => (a.parent k).c, fun k => (a.parent k).u, fun k => (a.parent k).Q,
      fun k => (a.parent k).R, fun k => (a.parent k).A, fun k => (a.parent k).F,
      a.worlds, a.error, a.coefficient_map, a.Z, a.increasing, a.same_base,
      a.valid, a.length, a.density_cap, a.angular_rate, a.angular_range,
      a.error_pos, a.error_le_one, a.error_limit, a.parent_valid, a.slack_one,
      a.old_slack, a.slack_bound, a.time_bound, a.width_bound, a.index_preserved,
      a.planar_map, a.hidden_map, a.prior_pos, a.prior_inverse_bound,
      a.conditioned_prior, a.selected_pullback, a.derivative_unit,
      a.normalizer_pos, a.normalizer_lower, a.normalizer_upper, a.normalizer_sum,
      a.world_weights, a.terminal_calibration⟩

end Submission.Obl.k4_known_atlas_normalization_composition
