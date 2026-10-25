import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal

abbrev Incidence := (ℕ × (Fin 6 → ℝ)) × ℝ
abbrev Label := Fin 6 → ℤ
abbrev ObsSpace := (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)

noncomputable def refMeasure : Measure ObsSpace :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod Measure.count

noncomputable def width (n r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log n / Real.log 2⌋ : ℤ))

noncomputable def observation (n r u : ℝ) (p : Incidence) : ObsSpace :=
  (((WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3,
      p.1.2 1 + p.2 * p.1.2 4] : EuclideanSpace ℝ (Fin 3)),
    ⌊(p.1.2 2 + p.2 * p.1.2 5) / width n r⌋),
    fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / width n u⌋)

noncomputable def commonLabel (n : ℝ) (H : ℕ) (R U : ℝ) (p : Incidence) : Label :=
  ![⌊n ^ H * p.2⌋, ⌊n ^ H * (p.1.2 0 + p.2 * p.1.2 3)⌋,
    ⌊n ^ H * (p.1.2 1 + p.2 * p.1.2 4)⌋,
    ⌊(p.1.2 2 + p.2 * p.1.2 5) / width n R⌋,
    ⌊p.1.2 3 / width n U⌋, ⌊p.1.2 4 / width n U⌋]

noncomputable def incidenceMeasure (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (E : Set Incidence) : Measure Incidence := (ν.prod volume).restrict E

noncomputable def clamp (B : ℝ) (q : ℚ) : ℝ := max 0 (min B (q : ℝ))

def Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

-- Adapted from this LOT tree, o075, session x0254,
-- Submission/Obl/k4_joint_homogenization/Interface.lean (branch x0254).
def TemperedProblem (N : ℝ) (M D : ℕ) (K : ℝ) (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) : Prop :=
  MeasureTheory.IsProbabilityMeasure ν ∧ (∃ m : ℕ, (m : ℝ) ≤ N ^ M ∧ ∃ (c : Fin m → ℝ)
    (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N ^ M ∧
    (i j : ℝ) ≤ N ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ,
    (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔
    b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧
    (∀ x ∈ A j, ∀ b, |x b| ≤ N ^ M)) ∧ ν = ∑ j, (ENNReal.ofReal (c j)) •
    MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧
  MeasurableSet E ∧ E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
  (∀ p ∈ E, (p.1.1 : ℝ) ≤ N ^ M ∧ ∀ e, |p.1.2 e| ≤ N ^ M) ∧
  (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ,
    (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀,
    x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ E}) ↔
    b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧
  (∀ᵐ l ∂ν, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1,
      ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ +
      ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K ∧
    |![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 3| ≤ K) ∧
  ENNReal.ofReal (K⁻¹) ≤ ((ν.prod MeasureTheory.volume).restrict E) Set.univ

def AbsoluteContinuity (N : ℕ → ℝ)
    (ν : ℕ → Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set Incidence) (R U : ℝ) : Prop :=
  ∀ k (S : Set Incidence), MeasurableSet S → S ⊆ E k →
    ∀ r u : ℝ, 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U →
      ∃ G : ObsSpace → ℝ≥0∞, Measurable G ∧
        (incidenceMeasure (ν k) S).map (observation (N k) r u) = refMeasure.withDensity G

def Approximation (N : ℕ → ℝ) (μ : ℕ → Measure Incidence)
    (R U : ℝ) (C H : ℕ) (g : ℕ → ℝ → ℝ → Label → ℝ) : Prop :=
  (∀ k r u, 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U →
    ∀ z, 0 ≤ g k r u z ∧ g k r u z ≤ N k ^ C) ∧
  (∀ k r u, 0 ≤ r → r ≤ R → 0 ≤ u → u ≤ U →
    ∀ G : ObsSpace → ℝ≥0∞, Measurable G →
      (μ k).map (observation (N k) r u) = refMeasure.withDensity G →
      μ k {p | G (observation (N k) r u p) <
          (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g k r u (commonLabel (N k) H R U p)) ∨
        2 * ENNReal.ofReal (g k r u (commonLabel (N k) H R U p)) <
          G (observation (N k) r u p) ∨
        ENNReal.ofReal (g k r u (commonLabel (N k) H R U p)) <
          ENNReal.ofReal (N k ^ (-(C : ℝ)))} ≤ ENNReal.ofReal (N k ^ (-1 : ℝ)))

def GridTypical (N : ℕ → ℝ) (μ : ℕ → Measure Incidence)
    (R U : ℝ) (a : ℕ → ℚ → ℚ → ℝ) : Prop :=
  ∀ (q s : ℚ) (τ : ℝ), 0 < τ → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k in atTop, ∀ G : ObsSpace → ℝ≥0∞, Measurable G →
      (μ k).map (observation (N k) (clamp R q) (clamp U s)) = refMeasure.withDensity G →
      μ k {p | G (observation (N k) (clamp R q) (clamp U s) p) <
          ENNReal.ofReal (N k ^ (-a k q s - τ)) ∨
        ENNReal.ofReal (N k ^ (-a k q s + τ)) <
          G (observation (N k) (clamp R q) (clamp U s) p)} ≤
        ENNReal.ofReal (N k ^ (-c))

lemma measurable_observation (n r u : ℝ) : Measurable (observation n r u) :=
  k4_profile_density_bounds.measurable_observe n r u

lemma measurable_commonLabel (n : ℝ) (H : ℕ) (R U : ℝ) :
    Measurable (commonLabel n H R U) := by
  unfold commonLabel
  fun_prop

lemma clamp_mem {B : ℝ} (hB : 0 ≤ B) (q : ℚ) : clamp B q ∈ Icc (0 : ℝ) B := by
  exact ⟨le_max_left _ _, max_le hB (min_le_left _ _)⟩

end Submission.Obl.k4_tempered_grid_selection
