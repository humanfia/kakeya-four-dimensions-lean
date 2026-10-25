import Submission.Obl.k4_critical_conditional_row_preparation.Model
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter

noncomputable section

/-- The accepted original-data record is independent of its critical-regime
validity predicate. We retain that record and impose the present hypotheses. -/
abbrev Data := Submission.Obl.k4_critical_conditional_row_preparation.Data

abbrev scalarY := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY
abbrev scalarX := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarX
abbrev scalarCell := Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarCell
abbrev ScalarAdmissible {α : Type} [MeasurableSpace α] :=
  @Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarAdmissible α _

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

structure Valid : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Tendsto cfg.N atTop atTop
  loss_lower : ∀ k, 1 ≤ cfg.K k
  loss_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  supercritical : 1 < 2 * cfg.κ
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.Atlas
  nested : cfg.Nested

def Diameter : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ cfg.U → ∀ᶠ k in atTop,
    ∀ i : Fin (cfg.n k s), ∀ l ∈ cfg.B k s i, ∀ l' ∈ cfg.B k s i,
    ∀ t ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k s) (cfg.j k s i),
    ∀ t' ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k s) (cfg.j k s i),
    ∀ e : Fin 4, |cfg.x k l t e - cfg.x k l' t' e| ≤
      48 * cfg.K k ^ 4 * ((2 : ℝ) ^ cfg.T k s)⁻¹

/-- One incoming velocity-list frame. Its law is normalized by the full
original parent reference, and its trajectory identities hold for all time. -/
structure ListFrame (k : ℕ) (r v m ε : ℝ) where
  parent : Fin (cfg.n k r)
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
  good_subset : good ⊆ cfg.B k r parent
  coeff_measurable : Measurable coeff
  prior_probability : IsProbabilityMeasure prior
  law_domination : law ≤ ENNReal.ofReal (cfg.N k ^ ε) • (prior.prod volume)
  time_support : law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  good_ae : ∀ᵐ p ∂law, p.1 ∈ good
  coeff_bound : ∀ l i, |coeff l i| ≤ cfg.N k ^ ε
  mass_lower : ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ law univ
  q_pos : 0 < q
  q_eq : q = ((2 : ℝ) ^ cfg.T k r)⁻¹
  time_eq : Submission.Obl.k4_critical_conditional_row_preparation.Data.I
    (cfg.T k r) (cfg.j k r parent) = Icc t₀ (t₀ + q)
  background_degree : background.totalDegree ≤ 2
  background_bound : (∑ e ∈ background.support, |background.coeff e|) ≤ cfg.N k ^ (m / 10)
  frame_bound : 1 + |q⁻¹| * (2 + |t₀| + |z₀| + |zv|) ≤ cfg.N k ^ (m / 10)
  scalarY_eq : ∀ l ∈ good, ∀ u,
    scalarY (coeff l) u = (cfg.x k l (t₀ + q * u) 1 - z₀ - zv * (t₀ + q * u)) / q
  scalarX_eq : ∀ l ∈ good, ∀ u,
    scalarX (coeff l) u = cfg.x k l (t₀ + q * u) 3 -
      MvPolynomial.eval (cfg.x k l (t₀ + q * u) ∘ Fin.castSucc) background
  original_domination :
    (ENNReal.ofReal q * cfg.ν k (cfg.A k r parent)) •
      law.map (fun p => (p.1, t₀ + q * p.2)) ≤ cfg.ρ k
  lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)
  lists_bound : ∀ a : ℤ, ((lists a).card : ℝ) * (cfg.N k ^ (-m)) ^ 2 ≤
    cfg.N k ^ ε * cfg.N k ^ (cfg.d * v)
  lists_ae : ∀ᵐ p ∂law,
    (scalarCell (coeff p.1) p.2 (cfg.N k ^ (-m)),
      ⌊scalarX (coeff p.1) p.2 / cfg.N k ^ (-r - v)⌋) ∈
      lists ⌊cfg.b k p.1 3 / cfg.N k ^ (-m)⌋

def VelocityLists : Prop :=
  ∃ r v m : ℝ, 0 < r ∧ 0 < v ∧ v < r ∧ 100 * (r + v) < m ∧
    10 * m < cfg.U ∧ 10 * m < cfg.e₀ ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Nonempty (cfg.ListFrame k r v m ε)

end Data

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
