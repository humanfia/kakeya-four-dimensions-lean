import Submission.Obl.k4_cap_class_terminal_charts.Diagonal

namespace Submission.Obl.k4_cap_class_terminal_charts

open MeasureTheory Set
open scoped BigOperators

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The full graph point corresponding to an indexed trajectory and time. -/
def graphPoint (l : Trajectory) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

/-- The observed planar part of a graph trajectory. -/
def planarPoint (l : Trajectory) (t : ℝ) : Plane :=
  WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4]

/-- Closed blocks are used for whole-block fits, as in the frozen conclusion. -/
def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- All the finite geometric and assignment data of a terminal system. -/
structure ChartSystem (W T : ℕ) where
  count : ℕ
  world : Fin count → Fin W
  block : Fin count → Fin (2 ^ T)
  center : Fin count → Plane
  speed : Fin count → Plane
  frame : Fin count → Matrix (Fin 2) (Fin 2) ℝ
  test : Fin count → MvPolynomial (Fin 4) ℝ
  assignment : Fin count → Set Trajectory
  event : Fin count → Set Incidence

/-- The exact quantifier-free polynomial format used by the frozen statement. -/
def PolynomialFormat {n : ℕ} (N : ℝ) (M D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧
    ∃ p : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ i, (p i).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool,
        ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true

/-- A finite system satisfies every geometric, format, mass, and disjointness
condition required at one sample. The selected masses remain unnormalized. -/
def ChartSystem.Valid {W T : ℕ} (s : ChartSystem W T)
    (N κ fL δ : ℝ) (M D : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ) : Prop :=
  (s.count : ℝ) ≤ N ^ M ∧
  (∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
    Disjoint (s.assignment b) (s.assignment b')) ∧
  (∀ b,
    Matrix.det (s.frame b) ≠ 0 ∧
    ‖s.center b‖ + ‖s.speed b‖ ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2,
      (|s.frame b e e'| + |(s.frame b)⁻¹ e e'|)) ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame b e e'|) ≤ κ / (2 : ℝ) ^ T ∧
    (s.test b).totalDegree ≤ 2 ∧
    (∀ e, |(s.test b).coeff e| ≤ N ^ M) ∧
    MeasurableSet (s.assignment b) ∧ MeasurableSet (s.event b) ∧
    (∀ i,
      PolynomialFormat N M D {x | (i, x) ∈ s.assignment b} ∧
      PolynomialFormat N M D {x : Fin 7 → ℝ |
        ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ s.event b}) ∧
    (∀ l ∈ s.assignment b,
      (l.1 : ℝ) ≤ N ^ M ∧ (∀ e, |l.2 e| ≤ N ^ M) ∧
      ∀ t ∈ timeBlock T (s.block b),
        ‖Matrix.toEuclideanLin ((s.frame b)⁻¹)
          (planarPoint l t - s.center b - t • s.speed b)‖ ≤ κ ∧
        |MvPolynomial.eval (graphPoint l t) (s.test b)| ≤ κ * δ ∧
        |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4) (s.test b))| ≤
          κ * B (s.world b) ∧
        |MvPolynomial.eval (graphPoint l t)
          (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (s.test b)))| ≤
          κ * B (s.world b) ^ 2 / δ) ∧
    (∀ p ∈ s.event b,
      p ∈ E (s.world b) ∧ p.1 ∈ s.assignment b ∧ p.2 ∈ timeBlock T (s.block b) ∧
      B (s.world b) / κ ≤
        |MvPolynomial.eval (graphPoint p.1 p.2)
          (MvPolynomial.pderiv (3 : Fin 4) (s.test b))|) ∧
    ENNReal.ofReal (N ^ (-fL) * |Matrix.det (s.frame b)| / ((2 : ℝ) ^ T * κ)) ≤
      ((ν (s.world b)).prod volume) (s.event b)) ∧
  ENNReal.ofReal (κ⁻¹) ≤
    ∑ b, ENNReal.ofReal (ω (s.world b)) * ((ν (s.world b)).prod volume) (s.event b)

/-- A finite system with a prescribed upper bound on the time exponent. -/
def HasCharts (W : ℕ) (N κ fL δ h : ℝ) (M D : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ) : Prop :=
  ∃ T : ℕ, (2 : ℝ) ^ T ≤ N ^ h ∧ ∃ s : ChartSystem W T,
    s.Valid N κ fL δ M D ω ν E B

/-- A fixed-format, fixed-tolerance existence estimate at arbitrarily late samples yields the exact
subsequence and subpower slack required by the terminal assertion. -/
theorem charts_of_fixed_tolerances (N K δ : ℕ → ℝ) (fL h : ℝ) (M D : ℕ)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (B : (k : ℕ) → Fin (W k) → ℝ) (hN : ∀ k, 1 ≤ N k)
    (hfinite : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧
        HasCharts (W k) (N k) κ fL (δ k) h M D (ω k) (ν k) (E k) (B k)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ κ : ℕ → ℝ,
      Subpower (N ∘ ψ) κ ∧ (∀ k, K (ψ k) ≤ κ k) ∧
      ∃ T : ℕ → ℕ, ∃ s : (k : ℕ) → ChartSystem (W (ψ k)) (T k),
        ∀ k, (2 : ℝ) ^ T k ≤ N (ψ k) ^ h ∧
          (s k).Valid (N (ψ k)) (κ k) fL (δ (ψ k)) M D
            (ω (ψ k)) (ν (ψ k)) (E (ψ k)) (B (ψ k)) := by
  obtain ⟨ψ, hψ, κ, hκ, hKκ, hc⟩ := subpower_diagonal hN
    (fun k κ => HasCharts (W k) (N k) κ fL (δ k) h M D (ω k) (ν k) (E k) (B k)) hfinite
  choose T hT s hs using hc
  exact ⟨ψ, hψ, κ, hκ, hKκ, T, s, fun k => ⟨hT k, hs k⟩⟩

end Submission.Obl.k4_cap_class_terminal_charts
