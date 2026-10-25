import Submission.Obl.k4_general_wide_layer_offset_comparison.Model
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/Lists/Interface.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

/-!
# Normalized scalar frames of the native signal

The downstream interface of the wide-interval argument (paper Prop. 8.4,
final third): one original true block, normalized to unit time, carrying the
native signal minus a quadratic background in the original base.

`ListFrame` is the input produced by the common transverse field
(velocity-wise residual lists); `ReadyFrame` is a complete Scalar input.
These are the general-parent analogues of the frames of accepted o248
(`k4_wide_velocity_lists_scalar_preparation`), with the native signal
`P(x)` in place of the hidden coordinate.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter

noncomputable section

abbrev scalarY := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY
abbrev scalarX := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarX
abbrev scalarCell := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell
abbrev ScalarAdmissible {α : Type} [MeasurableSpace α] :=
  @Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarAdmissible α _

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The native signal along a trajectory. -/
def signal (k : ℕ) (l : α) (t : ℝ) : ℝ :=
  MvPolynomial.eval (p.x k l t) (p.P k)

/-- The original base point of a trajectory. -/
def base (k : ℕ) (l : α) (t : ℝ) : Fin 3 → ℝ :=
  p.x k l t ∘ Fin.castSucc

/-- One incoming velocity-list frame: the native residual against a quadratic
background, normalized to the unit time of one original true block. Its law is
normalized by the full original assignment reference of that block. -/
structure ListFrame (k : ℕ) (r v m ε : ℝ) where
  parent : Fin (p.n k r)
  t₀ : ℝ
  q : ℝ
  z₀ : ℝ
  zv : ℝ
  background : MvPolynomial (Fin 3) ℝ
  prior : Measure α
  law : Measure (α × ℝ)
  coeff : α → Fin 5 → ℝ
  good : Set α
  good_measurable : MeasurableSet good
  good_subset : good ⊆ p.B k r parent
  coeff_measurable : Measurable coeff
  prior_probability : IsProbabilityMeasure prior
  law_domination : law ≤ ENNReal.ofReal (p.N k ^ ε) • (prior.prod volume)
  time_support : law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  good_ae : ∀ᵐ ω ∂law, ω.1 ∈ good
  coeff_bound : ∀ l i, |coeff l i| ≤ p.N k ^ ε
  mass_lower : ENNReal.ofReal (p.N k ^ (-ε)) ≤ law univ
  q_pos : 0 < q
  q_eq : q = ((2 : ℝ) ^ p.T k r)⁻¹
  time_eq : block (p.T k r) (p.j k r parent) = Icc t₀ (t₀ + q)
  background_degree : background.totalDegree ≤ 2
  background_bound : (∑ e ∈ background.support, |background.coeff e|) ≤ p.N k ^ (m / 10)
  frame_bound : 1 + |q⁻¹| * (2 + |t₀| + |z₀| + |zv|) ≤ p.N k ^ (m / 10)
  scalarY_eq : ∀ l ∈ good, ∀ u,
    scalarY (coeff l) u = (p.x k l (t₀ + q * u) 1 - z₀ - zv * (t₀ + q * u)) / q
  scalarX_eq : ∀ l ∈ good, ∀ u,
    scalarX (coeff l) u = p.signal k l (t₀ + q * u) -
      MvPolynomial.eval (p.base k l (t₀ + q * u)) background
  original_domination :
    (ENNReal.ofReal q * p.ν k (p.A k r parent)) •
      law.map (fun ω => (ω.1, t₀ + q * ω.2)) ≤ p.ρ k
  lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)
  lists_bound : ∀ a : ℤ, ((lists a).card : ℝ) * (p.N k ^ (-m)) ^ 2 ≤
    p.N k ^ ε * p.N k ^ (p.d * v)
  lists_ae : ∀ᵐ ω ∂law,
    (scalarCell (coeff ω.1) ω.2 (p.N k ^ (-m)),
      ⌊scalarX (coeff ω.1) ω.2 / p.N k ^ (-r - v)⌋) ∈
      lists ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋

/-- Admissible fixed exponents for a list frame: the scalar mesh `N^(-m)`
resolves the parent's transverse width, and there is room below `U` for the
deep original labels used in palette pooling. -/
def ListExponents (r v m : ℝ) : Prop :=
  0 < r ∧ 0 < v ∧ v < r ∧ 100 * (r + v) < m ∧ p.ℓ * r ≤ m ∧ r + 3 * m / p.κ < p.U

/-- Velocity-wise residual lists at fixed depth `r`, gain `v` and mesh `m`,
for every requested loss, available at arbitrarily small fixed exponents. -/
def VelocityLists : Prop :=
  ∀ U' : ℝ, 0 < U' → ∃ r v m : ℝ, p.ListExponents r v m ∧ m ≤ U' ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Nonempty (p.ListFrame k r v m ε)

/-- Native-signal confinement on deep original labels at one depth `t`:
after deleting a frame set of mass at most `N^(-ε)/4`, two groups split every
deep label into pieces whose native signal varies by at most `N^(-(r+v))/2`.
Only losses `ε ≤ ε₀` are requested.
This replaces the four-coordinate diameter bound used in the horizontal
model (accepted o248), where the signal is the hidden coordinate itself. -/
def DeepConfinement (r v m : ℝ) : Prop :=
  ∃ t ε₀ : ℝ, r + 3 * m / p.κ ≤ t ∧ t ≤ p.U ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ᶠ k in atTop, ∀ f : p.ListFrame k r v m ε,
      ∃ (grp : α × ℝ → Fin 2) (bad : Set (α × ℝ)), Measurable grp ∧ MeasurableSet bad ∧
        f.law bad ≤ ENNReal.ofReal (p.N k ^ (-ε) / 4) ∧
        ∀ (i : Fin (p.n k t)) (ω ω' : α × ℝ),
          ω.1 ∈ p.B k t i → ω'.1 ∈ p.B k t i →
          f.t₀ + f.q * ω.2 ∈ block (p.T k t) (p.j k t i) →
          f.t₀ + f.q * ω'.2 ∈ block (p.T k t) (p.j k t i) →
          ω ∉ bad → ω' ∉ bad → grp ω = grp ω' →
          |p.signal k ω.1 (f.t₀ + f.q * ω.2) - p.signal k ω'.1 (f.t₀ + f.q * ω'.2)| ≤
            p.N k ^ (-(r + v)) / 2

/-- A complete Scalar input retaining the original block, the original
reference factor and the full-time trajectory identities. -/
structure ReadyFrame (k : ℕ) (r v m C₀ S₀ U₀ height η : ℝ) where
  parent : Fin (p.n k r)
  t₀ : ℝ
  q : ℝ
  z₀ : ℝ
  zv : ℝ
  background : MvPolynomial (Fin 3) ℝ
  prior : Measure α
  law : Measure (α × ℝ)
  coeff : α → Fin 5 → ℝ
  good : Set α
  good_measurable : MeasurableSet good
  good_subset : good ⊆ p.B k r parent
  good_ae : ∀ᵐ ω ∂law, ω.1 ∈ good
  admissible : ScalarAdmissible (p.N k) η p.d (r + v) m C₀ S₀ U₀
    (p.N k ^ (p.d * r)) prior coeff law
  mass_lower : ENNReal.ofReal (p.N k ^ (-η)) ≤ law univ
  q_pos : 0 < q
  q_eq : q = ((2 : ℝ) ^ p.T k r)⁻¹
  time_eq : block (p.T k r) (p.j k r parent) = Icc t₀ (t₀ + q)
  background_degree : background.totalDegree ≤ 2
  background_bound : (∑ e ∈ background.support, |background.coeff e|) ≤ p.N k ^ height
  frame_bound : 1 + |q⁻¹| * (2 + |t₀| + |z₀| + |zv|) ≤ p.N k ^ height
  scalarY_eq : ∀ l ∈ good, ∀ u,
    scalarY (coeff l) u = (p.x k l (t₀ + q * u) 1 - z₀ - zv * (t₀ + q * u)) / q
  scalarX_eq : ∀ l ∈ good, ∀ u,
    scalarX (coeff l) u = p.signal k l (t₀ + q * u) -
      MvPolynomial.eval (p.base k l (t₀ + q * u)) background
  original_domination :
    (ENNReal.ofReal q * p.ν k (p.A k r parent)) •
      law.map (fun ω => (ω.1, t₀ + q * ω.2)) ≤ p.ρ k

/-- Scalar readiness at fixed depth, gain and Scalar parameters. -/
def ScalarReadiness : Prop :=
  ∃ r v m C₀ S₀ U₀ height : ℝ,
    0 < r ∧ 0 < v ∧ r + v ≤ p.U ∧ r + v < m ∧
    0 < C₀ ∧ 0 < S₀ ∧ 0 < U₀ ∧ U₀ < m ∧ 1 ≤ height ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, Nonempty (p.ReadyFrame k r v m C₀ S₀ U₀ height η)

end Parent

end

end Submission.Obl.k4_general_wide_layer_offset_comparison
