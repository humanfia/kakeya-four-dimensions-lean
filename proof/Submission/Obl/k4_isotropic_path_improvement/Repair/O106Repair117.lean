-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0678's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/O106Repair117.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair
import Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair170
import Submission.Obl.k4_quadratic_finite_greedy_cover
import Submission.Obl.k4_stable_quadratic_hidden_sheets
import Submission.Obl.k4_algebraic_sheet_remez
import Submission.Obl.k4_original_observation_atlas_encoding
import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_algebraic_real_jet_comparison
import Submission.Obl.k4_quadratic_atlas_normalization

set_option linter.unusedVariables false

/-!
# o117' of the repaired o106 split, modulo o173's frozen statement

`conversion2_of_analytical : AnalyticalConversion → O106Repair.O117'`, where
`AnalyticalConversion` is the frozen statement of o173 (`k4_quadratic_cover_to_analytical_atlas`,
not yet accepted) and `O117'` is the proposed o117' of `O106Repair` (`frozen117`).

This is o117's own glue with two changes: the greedy cover is `greedy_coverage2` (accepted
o170's proof with discovery's width exit at `gainW`, `O106Repair170`), and the width branch is
passed through at `gainW` (`width_improvementAt2`), with the global depth margin `r₂ + gainW L ≤ L`.

Adapted from this LOT tree, o117 (`k4_quadratic_candidate_atlas_conversion`), branch `x0682`
(commit c789d4c), files `Certificates.lean` (the interface definitions below, verbatim),
`JetControl.lean` (`algebraicJets_available`, verbatim), `Width.lean` (`width_improvementAt`),
`Monotonicity.lean` (`path_mono_exponent`, `improvementAt_mono`) and `Assembly.lean`
(`prob_temperedLaw`, `conversion_of_analytical`); those files say they were adapted from o117
split s061 (x0516, origin/x0441, commit c9fb590). Accepted children o170, o171, o172, o174 and
accepted o112, o149, o115 are imported.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair117

noncomputable section

abbrev matching := Submission.Obl.k4_quadratic_finite_greedy_cover.matching
abbrev x := Submission.Obl.k4_quadratic_finite_greedy_cover.x
abbrev y := Submission.Obl.k4_quadratic_finite_greedy_cover.y
abbrev v := Submission.Obl.k4_quadratic_finite_greedy_cover.v
abbrev δ := Submission.Obl.k4_quadratic_finite_greedy_cover.δ
abbrev obs := Submission.Obl.k4_quadratic_finite_greedy_cover.obs
abbrev fmt := Submission.Obl.k4_quadratic_finite_greedy_cover.fmt
abbrev chart := Submission.Obl.k4_quadratic_finite_greedy_cover.chart
abbrev prob := Submission.Obl.k4_quadratic_finite_greedy_cover.prob
abbrev path := Submission.Obl.k4_quadratic_finite_greedy_cover.path
abbrev system := Submission.Obl.k4_quadratic_finite_greedy_cover.system
abbrev width := Submission.Obl.k4_quadratic_finite_greedy_cover.width
abbrev candidate := Submission.Obl.k4_quadratic_finite_greedy_cover.candidate
abbrev discovery := Submission.Obl.k4_quadratic_finite_greedy_cover.discovery

def localGraph : Prop :=
  (∀ D : ℕ, ∀ d₀ : ℝ, 0 ≤ d₀ → d₀ < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ → ∀ n₁ n₂ : ℕ, ∀ (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ) (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ) (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ) (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))), (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) => (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) → (∀ i, P₁ i ≠ 0 ∧ (P₁ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₁ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₁ i z)) (P₁ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₁ i (emb x)).im = 0 ∧ ‖f₁ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, P₂ i ≠ 0 ∧ (P₂ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₂ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₂ i z)) (P₂ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₂ i (emb x)).im = 0 ∧ ‖f₂ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 → ENNReal.ofReal (R ^ (-ε)) ≤ μ Set.univ → μ Set.univ ≤ 1 → (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * MeasureTheory.volume U) → (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * MeasureTheory.volume U) → ¬ μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε) ∧ ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧ M * R ^ (-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}ᶜ = 0) (fun x => WithLp.toLp 2 (fun i => (x i : ℂ))))

def algebraicJets : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ K : ℕ, 1 ≤ K ∧
    ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), (∀ v ∈ V, ‖v‖ = 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
    ∀ (f : EuclideanSpace ℂ (Fin 3) → ℂ) (P : MvPolynomial (Fin 4) ℂ),
    P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) P = 0) →
    (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) =>
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f (emb x)).im = 0) →
      (∀ A : ℝ, 0 < A → (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖f (emb x)‖ ≤ A) →
        ∀ v ∈ V, ∀ m : ℕ, m ≤ K → |iteratedDeriv m (fun t : ℝ => (f (emb (t • v))).re) 0| ≤ B m * A) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
        c * ‖f (emb x)‖ ≤ ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1),
          |iteratedDeriv j (fun t : ℝ => (f (emb (t • v))).re) 0|)
      (fun x => WithLp.toLp 2 (fun j => (x j : ℂ)))

def stableSheets : Prop :=
  ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit a : ℝ), 2 ≤ A → 0 < a_fit →
    ∀ (b c : MvPolynomial (Fin 3) ℝ), b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
    (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) →
    |a| * a_fit ≤ A ^ (-20 : ℝ) →
    ∀ (u₀ : EuclideanSpace ℝ (Fin 3)) (w₀ : ℝ), ‖u₀‖ ≤ A →
    |a * w₀ ^ 2 + MvPolynomial.eval (fun j => u₀ j) b * w₀ + MvPolynomial.eval (fun j => u₀ j) c| ≤ a_fit * A →
    A ^ (-1 : ℝ) ≤ |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| →
    |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| ≤ A →
    ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
      DifferentiableOn ℂ f (Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ)))) ∧
      (∀ z ∈ Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ))),
        (a : ℂ) * (f z) ^ 2 + MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) b * f z +
          MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) c = 0) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < A ^ (-(C : ℝ)) →
        (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).im = 0 ∧
        A ^ (-(C : ℝ)) ≤ |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ∧
        |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ≤ A ^ (C : ℝ) ∧
        0 < (2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b) *
          (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b)) ∧
      (∀ (u : EuclideanSpace ℝ (Fin 3)) (w : ℝ), ‖u - u₀‖ < A ^ (-(C : ℝ)) →
        |a * w ^ 2 + MvPolynomial.eval (fun j => u j) b * w + MvPolynomial.eval (fun j => u j) c| ≤ a_fit * A →
        0 < (2 * a * w + MvPolynomial.eval (fun j => u j) b) * (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b) →
        |w - (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re| ≤ a_fit * A ^ (C : ℝ))

def algebraicRemez : Prop :=
  ∀ n D : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : MvPolynomial (Fin (n + 1)) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ),
    P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) →
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z)) P = 0) →
    (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → (f (WithLp.toLp 2 (fun j => (x j : ℂ)))).im = 0) →
    ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ), MeasurableSet E →
    E ⊆ Metric.closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
    ENNReal.ofReal θ * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ MeasureTheory.volume E →
    (∀ x ∈ E, ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ V) →
    ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
      ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ C * θ ^ (-C) * V

abbrev greedyCover := Submission.Obl.k4_quadratic_finite_greedy_cover.RoundedCoverage

def preImprovementAt (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (κ₁ Δ : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (M D : ℕ) (ε : ℝ) : Prop :=
  ∃ (r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
      (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
      (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ)
      (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
      (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    r₂ + Δ * L ≤ L ∧
    ((Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ Nk ^ (κ₁ * Δ * L / 2)) ∨
      ∃ i, i < m ∧ r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * Δ * L / 2)) ∧
    (C₂ : ℝ) ≤ Nk ^ M ∧
    (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧
    (∀ w o, ((lst₂ w o).card : ℝ) ≤ Nk ^ ε) ∧
    (∀ w b, MeasurableSet {o | b ∈ lst₂ w o}) ∧
    (∀ b, chart Nk M D (Nk ^ ε) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True) ∧
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume)
      {p | p ∈ F₂ b ∧ b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)}

def temperedLaw (Nk : ℝ) (M D W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ Nk ^ M ∧ (∀ w, 0 ≤ ω w) ∧ (∑ w, ω w) = 1 ∧
    ∀ w, MeasureTheory.IsProbabilityMeasure (ν w) ∧ 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M ∧
      ∃ n : ℕ, (n : ℝ) ≤ Nk ^ M ∧ ∃ (c : Fin n → ℝ) (copy : Fin n → ℕ) (S : Fin n → Set (Fin 6 → ℝ)),
        (∀ a, 0 ≤ c a ∧ c a ≤ Nk ^ M ∧ (copy a : ℝ) ≤ Nk ^ M ∧ fmt 6 (Nk ^ M) D (S a) ∧
          (∀ z ∈ S a, ∀ e, |z e| ≤ Nk ^ M)) ∧
        ν w = ∑ a, ENNReal.ofReal (c a) • MeasureTheory.Measure.map (fun z => (copy a, z)) (MeasureTheory.volume.restrict (S a))

def GreedyCoverage : Prop :=
  ∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain → discovery d₁ κ₁ S η ρ m s gain δ₀ →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mg Dg : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst,  path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      width (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mg Dg ε ∨ greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε

def AnalyticalConversion : Prop :=
  localGraph → algebraicJets → stableSheets → algebraicRemez →
    ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    ∃ α ρ : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 < ρ ∧ d₁ + ρ < 1 ∧
    ∀ S η : ℝ, 0 < S → 0 < η →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp Mg Dg : ℕ, ∃ Mi Di : ℕ, ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
    ∃ ε σ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ ζ ∧ 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst,  path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst → greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε →
      preImprovementAt (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain) m r T nw Mi Di ζ

def OriginalEncoding : Prop :=
  ∀ L : ℝ, 0 < L → ∀ Mν Dν M D : ℕ, ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
    ∀ (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
      (B : Fin W → ℝ) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    temperedLaw Nk Mν Dν W ω ν B →
    ∀ (ε r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
      (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
      (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ)
      (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
      (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    0 < ε → ε ≤ τ / 4 → ε ≤ 1 / 8 → (C₂ : ℝ) ≤ Nk ^ M →
    (∀ w o, ((lst₂ w o).card : ℝ) ≤ Nk ^ ε) →
    (∀ w b, MeasurableSet {o | b ∈ lst₂ w o}) →
    (∀ b, chart Nk M D (Nk ^ ε) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True) →
    ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume)
      {p | p ∈ F₂ b ∧ b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)} →
    ∃ (F' : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
      (∀ b, F' b ⊆ F₂ b) ∧ (∀ w o, ((lst' w o).card : ℝ) ≤ Nk ^ τ) ∧
      (∀ b, chart Nk M' D' (Nk ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F' b)
        (∀ p ∈ F' b, b ∈ lst' (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p))) ∧
      ENNReal.ofReal (Nk ^ (-τ)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume) (F' b)


theorem algebraicJets_available : algebraicJets := by
  intro D hD
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hcompare⟩ :=
    Submission.k4_algebraic_real_jet_comparison D
  refine ⟨K, hK, V, hV, c, hc, B, hB, ?_⟩
  intro f P hP hPD hf hroot hreal
  let Z : MvPolynomial (Fin 4) ℂ := MvPolynomial.X (3 : Fin 4)
  have hZ : Z ≠ 0 := by simp [Z]
  have hZD : Z.totalDegree ≤ D := by simpa [Z] using hD
  have hZroot : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (0 : ℂ)) Z = 0 := by
    intro z _
    simp [Z, Fin.snoc]
  obtain ⟨_, _, hupper, hlower⟩ := hcompare f (fun _ => 0) P Z hP hZ hPD hZD
    hf (differentiableOn_const (0 : ℂ)) hroot hZroot (fun x hx => ⟨hreal x hx, rfl⟩)
  constructor
  · intro A hA hbase v hv m _hm
    have hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
        ‖f (WithLp.toLp 2 (fun j => (x j : ℂ))) - 0‖ ≤ A := by
      simpa only [sub_zero] using hbase
    simpa only [sub_zero, zero_add] using
      hupper A hA hb v hv m 0 (by norm_num)
  · intro x hx
    simpa only [sub_zero, zero_add] using hlower 0 x (by norm_num) hx



/-- The improvement at one sample with the width exit (and the global depth margin) at `Δw`,
adapted from accepted o170's `ImprovementAt`. -/
def ImprovementAt2 (Nk L : ℝ) (W : ℕ)
    (ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (κ₁ Δ Δw : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (Mi Di : ℕ) (τ : ℝ) : Prop :=
  ∃ (r₂ : ℝ) (T₂ C₂ : ℕ) (γ₂ : Fin C₂ → Fin (W)) (j₂ : Fin C₂ → Fin (2 ^ T₂)) (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2)) (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ))) (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst₂ : Fin (W) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)), r₂ + Δw * L ≤ L ∧ ((Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ Nk ^ (κ₁ * Δ * L / 2)) ∨ ∃ i, i < m ∧ ((r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * Δ * L / 2)) ∨ (r₂ = r i ∧ T₂ = T i ∧ ∀ b, |Matrix.det (Q₂ b)| * (4 : ℝ) ^ T₂ ≤ Nk ^ (-(nw i + Δw * L))))) ∧ (C₂ : ℝ) ≤ Nk ^ Mi ∧ (∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b')) ∧ (∀ γ₁ o, ((lst₂ γ₁ o).card : ℝ) ≤ Nk ^ τ) ∧ (∀ b, chart (Nk) Mi Di (Nk ^ τ) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b)) (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) (∀ p ∈ F₂ b, b ∈ lst₂ (γ₂ b) (obs (B (γ₂ b)) (δ (Nk) L) p))) ∧ ENNReal.ofReal (Nk ^ (-τ)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) * ((ν (γ₂ b)).prod MeasureTheory.volume) (F₂ b)



/-- Extract exactly the original-law bounds needed for list encoding. -/
theorem prob_temperedLaw
    {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (h : prob N K L d S η W ω ν E P B f g G) :
    ∃ M D : ℕ, ∀ k, temperedLaw (N k) M D (W k) (ω k) (ν k) (B k) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hdata⟩
  rcases hdata.1 with ⟨M, D, hall⟩
  refine ⟨M, D, ?_⟩
  intro k
  rcases hall k with ⟨hW, hω, hsum, hworlds, _⟩
  refine ⟨hW, hω, hsum, ?_⟩
  intro w
  rcases hworlds w with ⟨hν, hB, hBup, hBinv, _, _, hprior, _⟩
  exact ⟨hν, hB, hBup, hBinv, hprior⟩

/-- Only the allowed upper bound on kappa depends on the path exponent. -/
theorem path_mono_exponent
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ σ' : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
    {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}
    (hN : 1 ≤ Nk) (hσ : σ ≤ σ')
    (h : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst) :
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ' r T nw κ C lev par γ j c u Q R A F lst := by
  exact Submission.Obl.k4_quadratic_finite_greedy_cover.path_slack_mono
    Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst
    σ' hN hσ h

/-- Enlarge count and format bounds and the requested list/mass slack. -/
theorem improvementAt2_mono
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {κ₁ Δ Δw : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {M D M' D' : ℕ} {ε τ : ℝ}
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D') (hε : ε ≤ τ)
    (hB : ∀ w, 0 ≤ B w)
    (h : ImprovementAt2 Nk L W ω ν E B κ₁ Δ Δw m r T nw M D ε) :
    ImprovementAt2 Nk L W ω ν E B κ₁ Δ Δw m r T nw M' D' τ := by
  rcases h with ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hroom, htime, hcount, hdisj, hlist, hchart, hmass⟩
  have hslack := Real.rpow_le_rpow_of_exponent_le hN hε
  refine ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hroom, htime, hcount.trans (pow_le_pow_right₀ hN hM), hdisj,
    fun w o => (hlist w o).trans hslack, ?_, ?_⟩
  · intro b
    exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono hN hM hD
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _) hslack (hB _) (hchart b) id
  · exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hε))).trans hmass

/-- The width certificate at `gainW` is the width exit at `Δw = gainW`. -/
theorem width_improvementAt2
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (κ₁ Δ gainW : ℝ) (m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ)
    (Mi Di : ℕ) (τ : ℝ)
    (hL : 0 ≤ L) (hgW : 0 ≤ gainW)
    (hw : width Nk L W ω ν E B m r T nw gainW Mi Di τ) :
    ImprovementAt2 Nk L W ω ν E B κ₁ Δ gainW m r T nw Mi Di τ := by
  rcases hw with ⟨i, hi, hroom, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    hcount, hdisj, hlist, hchart, hmass⟩
  refine ⟨r i, T i, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
    ?_, ?_, hcount, hdisj, hlist, ?_, hmass⟩
  · have hg : 0 ≤ gainW * L := mul_nonneg hgW hL
    linarith
  · exact Or.inr ⟨i, hi, Or.inr ⟨rfl, rfl, fun b => (hchart b).2⟩⟩
  · exact fun b => (hchart b).1

/-- o117' from o173's frozen statement and the accepted children. -/
theorem conversion2_of_analytical (hanalytic : AnalyticalConversion) :
    Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair.O117' := by
  have hencoding : OriginalEncoding := Submission.k4_original_observation_atlas_encoding
  have hstable : stableSheets := Submission.k4_stable_quadratic_hidden_sheets
  have hremez : algebraicRemez := Submission.k4_algebraic_sheet_remez
  have hjets : algebraicJets := algebraicJets_available
  intro hmatching d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  have hlocal : localGraph := Submission.k4_local_algebraic_graph_matching hmatching
  obtain ⟨α, ρ, hα, hαup, hρ, hdρ, hconvert⟩ :=
    hanalytic hlocal hjets hstable hremez d₁ κ₁ hd₁ hd₁1 hκ₁ hκ₁1
  refine ⟨α, ρ, hα, hαup, hρ, hdρ, ?_⟩
  intro S η hS hη m s gain gainW δ₀ hgrid hgain hgainup hgW hgWα hδ₀ hδ₀up hdiscovery
  intro N K L d W ω ν E P B f g G hprob hf Mp Dp
  obtain ⟨Mg, Dg, hcover⟩ :=
    Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair170.greedy_coverage2
      d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ m s gain gainW δ₀ hgrid hgain hgainup hgW
      hδ₀ hδ₀up hdiscovery N K L d W ω ν E P B f g G hprob hf Mp Dp
  obtain ⟨Mi, Di, hpre⟩ := hconvert S η hS hη m s gain δ₀ hgrid hgain
    hgainup hδ₀ hδ₀up N K L d W ω ν E P B f g G hprob hf Mp Dp Mg Dg
  obtain ⟨Mν, Dν, hlaw⟩ := prob_temperedLaw hprob
  have hL : 0 < L := hprob.2.2.2.1
  have hB := (Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G hprob).2.2.2.2.2.2.1
  obtain ⟨Me, De, hMi, hDi, hencode⟩ := hencoding L hL Mν Dν Mi Di
  refine ⟨max Mg Me, max Dg De, ?_⟩
  intro τ hτ
  let ζ : ℝ := min (τ / 4) (1 / 8)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζτ : ζ ≤ τ / 4 := min_le_left _ _
  have hζsmall : ζ ≤ 1 / 8 := min_le_right _ _
  have hζone : ζ ≤ 1 := hζsmall.trans (by norm_num)
  obtain ⟨ε, σc, hε, hεone, hεζ, hσc, kc, hpreAt⟩ := hpre ζ hζ hζone
  obtain ⟨σg, hσg, kg, hcoverAt⟩ := hcover ε hε hεone
  obtain ⟨N₀, hN₀, hencodeAt⟩ := hencode τ hτ
  obtain ⟨ke, hke⟩ := Filter.eventually_atTop.mp (hprob.2.1.eventually (Filter.eventually_ge_atTop N₀))
  refine ⟨min σg σc, lt_min hσg hσc, max (max kg kc) ke, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp
  have hNk : 1 ≤ N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hprob.1 k)
  have hkg : kg ≤ k := (le_max_left kg kc).trans ((le_max_left (max kg kc) ke).trans hk)
  have hkc : kc ≤ k := (le_max_right kg kc).trans ((le_max_left (max kg kc) ke).trans hk)
  have hke' : ke ≤ k := (le_max_right (max kg kc) ke).trans hk
  have hpG := path_mono_exponent hNk (min_le_left σg σc) hp
  have hpC := path_mono_exponent hNk (min_le_right σg σc) hp
  change ImprovementAt2 (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain) gainW
    m r T nw (max Mg Me) (max Dg De) τ
  rcases hcoverAt k hkg r T nw κ C lev par γ j c u Q R A F lst hpG with hw | hcov
  · have hi := width_improvementAt2 (N k) L (W k) (ω k) (ν k) (E k) (B k)
      κ₁ (α * gain) gainW m r T nw Mg Dg ε hL.le hgW.le hw
    exact improvementAt2_mono hNk (le_max_left Mg Me) (le_max_left Dg De)
      (hεζ.trans (hζτ.trans (by linarith))) (fun w => (hB k w).le) hi
  · have hpout := hpreAt k hkc r T nw κ C lev par γ j c u Q R A F lst hpC hcov
    rcases hpout with ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F₂, lst₂,
      hroom, htime, hcount, hdisj, hlist, hlistmeas, hcharts, hmass⟩
    obtain ⟨F', lst', hsub, hlist', hcharts', hmass'⟩ :=
      hencodeAt (N k) (hke k hke') (W k) (ω k) (ν k) (B k) (E k) (hlaw k)
        ζ r₂ T₂ C₂ γ₂ j₂ c₂ u₂ Q₂ R₂ A₂ F₂ lst₂ hζ hζτ hζsmall hcount
        hlist hlistmeas hcharts hmass
    have hi : ImprovementAt2 (N k) L (W k) (ω k) (ν k) (E k) (B k) κ₁ (α * gain) gainW
        m r T nw Me De τ := by
      refine ⟨r₂, T₂, C₂, γ₂, j₂, c₂, u₂, Q₂, R₂, A₂, F', lst',
        ?_, ?_, hcount.trans (pow_le_pow_right₀ hNk hMi), hdisj,
        hlist', hcharts', hmass'⟩
      · have : gainW * L ≤ α * gain * L := mul_le_mul_of_nonneg_right hgWα hL.le
        linarith
      · rcases htime with hfirst | ⟨i, hi, hr, ht⟩
        · exact Or.inl hfirst
        · exact Or.inr ⟨i, hi, Or.inl ⟨hr, ht⟩⟩
    exact improvementAt2_mono hNk (le_max_right Mg Me) (le_max_right Dg De) le_rfl
      (fun w => (hB k w).le) hi

/-- o106's exact frozen statement from the proposed o116' (`frozen116`) and o173's frozen
statement; every other ingredient is accepted. -/
theorem o106_of_repair
    (h116 : Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair.frozen116)
    (h173 : AnalyticalConversion) :
    Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair.O106 :=
  Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair.glue h116
    (conversion2_of_analytical h173)

end
end Submission.Obl.k4_isotropic_path_improvement.Repair.O106Repair117
