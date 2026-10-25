import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Types

/-!
# The flattening interface consumed by the type selection

`ScalarApproximation p C H g` is the scalar, per-world analog of the version-2
`Approximation` of o084: a table `g`, read at a common integer label (a polynomial
base mesh in `(t, y)` and a fine hidden bin), approximates every version of every
depth-`r` observation density within a factor two, except on mass `N⁻¹`; the table
is polynomially bounded and values below `N^(-C)` are counted as exceptional.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal

/-- The common integer label of an incidence: base mesh cell of width `n^(-H)` in
`(t, y)` and the hidden bin of the same width. -/
def scalarLabel (n : ℝ) (H : ℕ) (z : Incidence) : Fin 3 → ℤ :=
  ![⌊n ^ H * z.2⌋, ⌊n ^ H * y z.1 z.2⌋, ⌊n ^ H * x z.1 z.2⌋]

theorem measurable_y : Measurable (fun z : Incidence => y z.1 z.2) := by
  unfold y
  fun_prop

theorem measurable_x : Measurable (fun z : Incidence => x z.1 z.2) := by
  unfold x
  fun_prop

theorem measurable_scalarLabel (n : ℝ) (H : ℕ) : Measurable (scalarLabel n H) := by
  have h0 : Measurable (fun z : Incidence => ⌊n ^ H * z.2⌋) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_snd)
  have h1 : Measurable (fun z : Incidence => ⌊n ^ H * y z.1 z.2⌋) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_y)
  have h2 : Measurable (fun z : Incidence => ⌊n ^ H * x z.1 z.2⌋) :=
    Int.measurable_floor.comp (measurable_const.mul measurable_x)
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem measurable_observe (n r : ℝ) : Measurable (observe n r) := by
  unfold observe
  refine Measurable.prodMk ?_ ?_
  · apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_snd
    · exact measurable_y
  · exact Int.measurable_floor.comp (measurable_x.div_const _)

/-- Per-world table approximation of all depth densities (the flattening output). -/
def ScalarApproximation (p : Problem) (C H : ℕ)
    (g : (k : ℕ) → Fin (p.1 k) → ℝ → (Fin 3 → ℤ) → ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ (a : Fin (p.1 k)) (r : ℝ), 0 ≤ r → r ≤ length p →
    (∀ z, 0 ≤ g k a r z ∧ g k a r z ≤ resolution p k ^ (C : ℝ)) ∧
    ∀ G : Observation → ℝ≥0∞, Measurable G →
      (law p k a).map (observe (resolution p k) r) = reference.withDensity G →
      law p k a {z | G (observe (resolution p k) r z) <
            (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g k a r (scalarLabel (resolution p k) H z)) ∨
          2 * ENNReal.ofReal (g k a r (scalarLabel (resolution p k) H z)) <
            G (observe (resolution p k) r z) ∨
          ENNReal.ofReal (g k a r (scalarLabel (resolution p k) H z)) <
            ENNReal.ofReal (resolution p k ^ (-(C : ℝ)))} ≤
        ENNReal.ofReal (resolution p k ^ (-1 : ℝ))

/-- The statement of scalar joint base flattening (paper Lemma 2.3) used here. -/
def ScalarFlatteningStatement : Prop :=
  ∀ p : Problem, RawScalar p → ∃ (C H : ℕ) (g : (k : ℕ) → Fin (p.1 k) → ℝ → (Fin 3 → ℤ) → ℝ),
    ScalarApproximation p C H g

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
