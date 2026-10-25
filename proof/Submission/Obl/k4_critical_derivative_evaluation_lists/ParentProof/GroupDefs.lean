/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupDefs.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.AffineEntries
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-! Pointwise good incidences, initial-position/velocity groups and full-time
hidden coefficients for the horizontal coefficient count (paper Lemma
`a06:horizontal-coefficient-count`). Everything here is stated for the
original frozen data at one sample `k`. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_coefficient_clustering

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- The hidden coordinate `w = b₂ + t b₅` along a trajectory. -/
def hidden (k : ℕ) (p : α × ℝ) : ℝ := cfg.b k p.1 2 + p.2 * cfg.b k p.1 5

/-- Full-time hidden coefficients `(b₂, b₅, 0)`, as a scalar-clustering coefficient. -/
def hiddenCoeff (k : ℕ) (l : α) : Coeff :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![cfg.b k l 2, cfg.b k l 5, 0]

/-- Incidences on which every frozen almost-everywhere fact used by the
coefficient count holds pointwise, at true depth `s`. -/
def goodSet (k : ℕ) (s : ℝ) : Set (α × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ |cfg.b k p.1 0| ≤ cfg.K k ∧ |cfg.b k p.1 1| ≤ cfg.K k ∧
    |cfg.b k p.1 3| ≤ cfg.K k ∧ |cfg.b k p.1 4| ≤ cfg.K k ∧ |cfg.b k p.1 2| ≤ cfg.K k ∧
    |cfg.b k p.1 5| ≤ 2 * cfg.K k ∧
    |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) ∧
    ∃ i, p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i)}

/-- The group of a trajectory: its initial position `(b₀, b₁)` at mesh `a`
and its velocity `b₃` at mesh `δ`. -/
def groupCode (k : ℕ) (a δ : ℝ) (l : α) : ℤ × ℤ × ℤ :=
  (⌊cfg.b k l 0 / a⌋, ⌊cfg.b k l 1 / a⌋, ⌊cfg.b k l 3 / δ⌋)

/-- The reference weight `π(v-bin) a²` of a group. -/
def groupWeight (k : ℕ) (a δ : ℝ) (g : ℤ × ℤ × ℤ) : ℝ :=
  a ^ 2 * (cfg.π k).real {w : ℝ | ⌊w / δ⌋ = g.2.2}

theorem hiddenCoeff_apply_zero (k : ℕ) (l : α) : cfg.hiddenCoeff k l 0 = cfg.b k l 2 := rfl

theorem hiddenCoeff_apply_one (k : ℕ) (l : α) : cfg.hiddenCoeff k l 1 = cfg.b k l 5 := rfl

theorem hiddenCoeff_apply_two (k : ℕ) (l : α) : cfg.hiddenCoeff k l 2 = 0 := rfl

theorem quadratic_hiddenCoeff (k : ℕ) (p : α × ℝ) :
    quadratic (cfg.hiddenCoeff k p.1) p.2 = cfg.hidden k p := by
  simp [quadratic, hidden, hiddenCoeff_apply_zero, hiddenCoeff_apply_one,
    hiddenCoeff_apply_two]

theorem measurable_hidden (k : ℕ) (hb : Measurable (cfg.b k)) : Measurable (cfg.hidden k) := by
  have hc (i : Fin 6) : Measurable (fun p : α × ℝ => cfg.b k p.1 i) :=
    (measurable_pi_apply i).comp (hb.comp measurable_fst)
  exact (hc 2).add (measurable_snd.mul (hc 5))

theorem measurable_hiddenCoeff (k : ℕ) (hb : Measurable (cfg.b k)) : Measurable (cfg.hiddenCoeff k) := by
  have hc (i : Fin 6) : Measurable (fun l : α => cfg.b k l i) := (measurable_pi_apply i).comp hb
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.measurable.comp
  apply measurable_pi_lambda
  intro j
  fin_cases j
  · exact hc 2
  · exact hc 5
  · exact measurable_const

theorem measurable_groupCode (k : ℕ) (hb : Measurable (cfg.b k)) (a δ : ℝ) :
    Measurable (cfg.groupCode k a δ) := by
  have hc (i : Fin 6) : Measurable (fun l : α => cfg.b k l i) := (measurable_pi_apply i).comp hb
  exact (Int.measurable_floor.comp ((hc 0).div_const a)).prodMk
    ((Int.measurable_floor.comp ((hc 1).div_const a)).prodMk
      (Int.measurable_floor.comp ((hc 3).div_const δ)))

theorem measurableSet_goodSet (k' : ℕ) (hb : Measurable (cfg.b k')) (s : ℝ)
    (hA : ∀ i, MeasurableSet (cfg.B k' s i)) :
    MeasurableSet (cfg.goodSet k' s) := by
  have hc (i : Fin 6) : Measurable (fun p : α × ℝ => cfg.b k' p.1 i) :=
    (measurable_pi_apply i).comp (hb.comp measurable_fst)
  have hcov : MeasurableSet {p : α × ℝ |
      ∃ i, p.1 ∈ cfg.B k' s i ∧ p.2 ∈ I (cfg.T k' s) (cfg.j k' s i)} := by
    have : {p : α × ℝ | ∃ i, p.1 ∈ cfg.B k' s i ∧ p.2 ∈ I (cfg.T k' s) (cfg.j k' s i)} =
        ⋃ i, (cfg.B k' s i ×ˢ I (cfg.T k' s) (cfg.j k' s i)) := by
      ext p; simp [Set.mem_prod]
    rw [this]
    exact MeasurableSet.iUnion fun i => (hA i).prod measurableSet_Icc
  refine (measurable_snd measurableSet_Icc).inter ?_
  refine (measurableSet_le (hc 0).abs measurable_const).inter ?_
  refine (measurableSet_le (hc 1).abs measurable_const).inter ?_
  refine (measurableSet_le (hc 3).abs measurable_const).inter ?_
  refine (measurableSet_le (hc 4).abs measurable_const).inter ?_
  refine (measurableSet_le (hc 2).abs measurable_const).inter ?_
  refine (measurableSet_le (hc 5).abs measurable_const).inter ?_
  exact (measurableSet_le ((hc 4).add (hc 0)).abs measurable_const).inter hcov

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
