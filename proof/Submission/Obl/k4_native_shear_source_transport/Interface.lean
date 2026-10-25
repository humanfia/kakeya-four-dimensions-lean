-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/Interface.lean (session x0254's own proofs), renamed into this namespace.
import Mathlib

/-!
# Interface for `k4_joint_homogenization`

Shared definitions for the two halves of the proof of o075:

* the *native* half (session x0254): the trajectory/time law pushed to the joint
  observation has an explicit density for every measurable selection, and its finest
  density can be flattened on a fixed polynomial base mesh with a power-small `L¹`
  error (paper Lemma `a01:flattening`);
* the *selection* half: density types on the flattened law, typicality at tested depths,
  profile compactness and squeezing, and the polynomial format of cell-table selections.

`TemperedProblem N M D K ν E` is, verbatim, the per-index hypothesis of the frozen
statement (same nesting of `∧`), so `hfmt k` can be passed directly.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory
open scoped ENNReal

/-- Observation space: base point `(t, y(t))`, hidden bin, two velocity bins. -/
abbrev ObsSpace := (EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)

/-- The reference measure `volume ⊗ count ⊗ count` of the frozen statement. -/
noncomputable def refMeasure : Measure ObsSpace :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).prod Measure.count

/-- The joint observation with hidden width `a` and velocity width `b`, written exactly as
in the frozen statement (with `a = 2 ^ (-⌊r log N / log 2⌋)`, `b = 2 ^ (-⌊u log N / log 2⌋)`). -/
noncomputable def obsMap (a b : ℝ) (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : ObsSpace :=
  (((WithLp.toLp 2 ![p.2, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
      p.1.2 2 + p.2 * p.1.2 5] 1, ![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4,
      p.1.2 2 + p.2 * p.1.2 5] 2] : EuclideanSpace ℝ (Fin 3)),
    ⌊![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5] 3 /
      a⌋), fun j : Fin 2 => ⌊(WithLp.toLp 2 ![p.1.2 3, p.1.2 4]) j / b⌋)

/-- The per-index tempered hypothesis of the frozen statement, verbatim. -/
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

/-- `L¹(refMeasure)` distance of two `ℝ≥0∞`-valued densities. -/
noncomputable def densityDist (G g : ObsSpace → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y, ((G y - g y) + (g y - G y)) ∂refMeasure

/-- **Native densities** (x0254). For a tempered prior, every measurable selection has a
joint observation law with a density with respect to `volume ⊗ count ⊗ count`, at all
positive widths. -/
def NativeDensityStatement : Prop :=
  ∀ (N : ℝ) (M D : ℕ) (K : ℝ) (ν : Measure (ℕ × (Fin 6 → ℝ)))
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), TemperedProblem N M D K ν E →
    ∀ E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ), MeasurableSet E' → ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ G : ObsSpace → ℝ≥0∞, Measurable G ∧
        Measure.map (obsMap a b) ((ν.prod volume).restrict E') = refMeasure.withDensity G

/-- **Joint base flattening** (x0254, paper Lemma `a01:flattening`). For fixed format
exponents `M, D`, fixed depth bounds `R, U` and a target error exponent `T`, there are fixed
exponents `C₁, D₁` such that at every resolution `N ≥ 2` the finest joint observation law
(hidden width `2^-n ≥ N^-R`, velocity width `2^-m ≥ N^-U`) is `N^-T`-close in `L¹` to a
density `g` which is constant on the base cells of a mesh of width `ρ ≥ N^-D₁`, bounded by
`N^C₁`, and supported in the box of half-width `N^C₁`. -/
def FlatteningStatement : Prop :=
  ∀ (M D : ℕ) (R U T : ℝ), 0 ≤ R → 0 ≤ U → 0 < T → ∃ C₁ D₁ : ℕ,
    ∀ (N K : ℝ) (ν : Measure (ℕ × (Fin 6 → ℝ))) (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
      2 ≤ N → TemperedProblem N M D K ν E → ∀ n m : ℕ, (2 : ℝ) ^ n ≤ N ^ R →
      (2 : ℝ) ^ m ≤ N ^ U →
      ∃ (ρ : ℝ) (g : ObsSpace → ℝ≥0∞), 0 < ρ ∧ ρ⁻¹ ≤ N ^ D₁ ∧ Measurable g ∧
        (∀ y, g y ≤ ENNReal.ofReal (N ^ C₁)) ∧
        (∀ y, g y ≠ 0 → (∀ i, |y.1.1 i| ≤ N ^ C₁) ∧ |(y.1.2 : ℝ)| ≤ N ^ C₁ ∧
          ∀ i, |(y.2 i : ℝ)| ≤ N ^ C₁) ∧
        (∀ (b b' : EuclideanSpace ℝ (Fin 3)) (j : ℤ) (v : Fin 2 → ℤ),
          (∀ i, ⌊b i / ρ⌋ = ⌊b' i / ρ⌋) → g ((b, j), v) = g ((b', j), v)) ∧
        ∀ G : ObsSpace → ℝ≥0∞, Measurable G →
          Measure.map (obsMap ((2 : ℝ) ^ (-(n : ℤ))) ((2 : ℝ) ^ (-(m : ℤ))))
              ((ν.prod volume).restrict E) = refMeasure.withDensity G →
            densityDist G g ≤ ENNReal.ofReal (N ^ (-T))

end Submission.Obl.k4_native_shear_source_transport
