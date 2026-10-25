import Submission.Obl.k4_scalar_grid_cartesian_field.CoreStatement

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set MvPolynomial

/-- A reviewable packet carrying exactly the hypotheses of the Cartesian interpolation core. -/
structure CorePacket (M : ℕ) where
  N : ℝ
  Λ : ℝ
  h : ℝ
  a : ℝ
  y₀ : ℝ
  εT : ℝ
  rT : ℝ
  B : ℝ
  L : ℝ
  ξ : ℝ
  δv : ℝ
  δs : ℝ
  ρ : Measure Incidence
  θ : Measure Trajectory
  ν : Measure Trajectory
  π : Measure ℝ
  E : Set Incidence
  S₀ : Set Incidence
  A : Set Trajectory
  G : (Fin 3 → ℤ) → Fin 2 → ℝ
  hN : 2 ≤ N
  hΛ : 1 ≤ Λ
  hh : 0 < h
  hh_one : h ≤ 1
  ha : 0 ≤ a
  ha_one : a + h ≤ 1
  hεT : εT = N ^ (-rT)
  hξ : 0 < ξ
  hδv : 0 < δv
  hδs : 0 < δs
  fit_precision : h ^ M ≤ εT
  graph_precision : Λ * N ^ (-L) ≤ εT
  layer_precision : Λ ^ 2 * N ^ (-1 : ℝ) ≤ εT
  base_precision : Λ ^ 4 * ξ ≤ εT
  velocity_precision : Λ ^ 2 * δv ≤ ξ
  fine_precision : Λ ^ 4 * N ^ (-B) ≤ ξ * h
  separation_budget : 1 ≤ Λ * δs
  separation_small : δs ≤ 1
  finite_ρ : IsFiniteMeasure ρ
  finite_θ : IsFiniteMeasure θ
  sigma_ν : SigmaFinite ν
  probability_π : IsProbabilityMeasure π
  measurable_E : MeasurableSet E
  measurable_S₀ : MeasurableSet S₀
  measurable_A : MeasurableSet A
  subset_E : S₀ ⊆ E
  subset_packet : S₀ ⊆ {p | p.1 ∈ A ∧ p.2 ∈ Icc a (a + h)}
  positive_mass : 0 < ρ S₀
  original_density : ρ.restrict S₀ ≤ ENNReal.ofReal Λ • ν.prod volume
  original_mass : ENNReal.ofReal h * ν A ≤ ENNReal.ofReal Λ * ρ S₀
  lower_graph_density : (θ.prod volume).restrict E ≤ ENNReal.ofReal Λ • ρ.restrict E
  upper_graph_density : ρ.restrict E ≤ ENNReal.ofReal Λ • (θ.prod volume).restrict E
  coefficient_bound : ∀ l ∈ A, ∀ e, |l.2 e| ≤ Λ
  base_bound : ∀ l ∈ A, ∀ t ∈ Icc a (a + h), |scalarY l t - y₀| ≤ Λ * h
  hidden_layer : ∀ l ∈ A, ∀ l' ∈ A, ∀ t ∈ Icc a (a + h), ∀ t' ∈ Icc a (a + h),
    |scalarX l t - scalarX l' t'| ≤ Λ * N ^ (-1 : ℝ) +
      Λ / h * (|t - t'| + |scalarY l t - scalarY l' t'|)
  graph_bound : ∀ p ∈ E, (∀ e, |G (physCube N B p) e| ≤ Λ) ∧
    |p.1.2 3 + 2 * p.2 * p.1.2 4 - G (physCube N B p) 0 -
      G (physCube N B p) 1 * p.1.2 1| ≤ Λ * N ^ (-L)
  coarse_lists : ∀ q : Fin 3 → ℤ, ({w : Fin 2 → ℤ | ρ.restrict E
    {p | physCube N rT p = q ∧ rowBin N rT (G (physCube N B p)) = w} ≠ 0}.ncard : ℝ) ≤ Λ
  separation : ∀ (q : Fin 3 → ℤ) (c : ℤ),
    16 * ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δs⌋ = c} ≤
      ρ.restrict S₀ {p | physCube N B p = q}
  palette : ∀ (q : Fin 3 → ℤ) (c : ℤ),
    ρ.restrict S₀ {p | physCube N B p = q ∧ ⌊p.1.2 1 / δv⌋ = c} ≤
      ENNReal.ofReal Λ * ρ.restrict S₀ {p | physCube N B p = q} * π {w | ⌊w / δv⌋ = c}
  qualified : ∀ p ∈ S₀, ∃ P : Fin 2 → Polynomial ℝ,
    (∀ e, (P e).natDegree ≤ M ∧ ∀ i, |(P e).coeff i| ≤ Λ) ∧
    (∀ e, |G (physCube N B p) e - (P e).eval p.2| ≤ h ^ M) ∧
    ENNReal.ofReal (h / Λ) ≤ volume {t | (p.1, t) ∈ E ∧ t ∈ Icc a (a + h) ∧
      ∀ e, |G (physCube N B (p.1, t)) e - (P e).eval t| ≤ h ^ M}
  base_ceiling : ∀ c : Fin 2 → ℤ, ρ.restrict S₀
    {p | ∀ e, ⌊normalizedBase h ![a, y₀] p e / ξ⌋ = c e} ≤
      ENNReal.ofReal (Λ * ξ ^ 2) * ρ S₀

/-- The core output uses the frozen field residual on every time of the original block. -/
def CorePacket.Output {M : ℕ} (p : CorePacket M) (C : ℝ) (q : ℕ) : Prop :=
  ∃ (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (S₁ : Set Incidence),
    MeasurableSet S₁ ∧ S₁ ⊆ p.S₀ ∧
    (∀ e, (𝒯 e).totalDegree ≤ 2 * M) ∧
    (∀ e b, |(𝒯 e).coeff b| ≤ C * p.Λ ^ q) ∧
    ENNReal.ofReal (1 / (C * p.Λ ^ q)) * p.ρ p.S₀ ≤ p.ρ S₁ ∧
    ∀ x ∈ S₁, ∀ t ∈ Icc p.a (p.a + p.h),
      |coreResidual 𝒯 p.h ![p.a, p.y₀] x.1 t| ≤ C * p.Λ ^ q * p.εT

/-- Package the curried core interface without strengthening any assumption. -/
theorem core_packet_output {M : ℕ} (hcore : CartesianCoreStatement M) :
    ∃ (C : ℝ) (q q₀ : ℕ), 0 < C ∧ ∀ p : CorePacket M,
      C * p.Λ ^ q₀ * p.εT ≤ 1 → p.Output C q := by
  obtain ⟨C, q, q₀, hC, hc⟩ := hcore
  refine ⟨C, q, q₀, hC, fun p hsmall => ?_⟩
  exact hc p.N p.Λ p.h p.a p.y₀ p.εT p.rT p.B p.L p.ξ p.δv p.δs
    p.ρ p.θ p.ν p.π p.E p.S₀ p.A p.G p.hN p.hΛ p.hh p.hh_one p.ha p.ha_one
    p.hεT p.hξ p.hδv p.hδs hsmall p.fit_precision p.graph_precision p.layer_precision
    p.base_precision p.velocity_precision p.fine_precision p.separation_budget p.separation_small
    p.finite_ρ p.finite_θ p.sigma_ν p.probability_π p.measurable_E p.measurable_S₀ p.measurable_A
    p.subset_E p.subset_packet p.positive_mass p.original_density p.original_mass
    p.lower_graph_density p.upper_graph_density p.coefficient_bound p.base_bound p.hidden_layer
    p.graph_bound p.coarse_lists p.separation p.palette p.qualified p.base_ceiling

end Submission.Obl.k4_scalar_grid_cartesian_field
