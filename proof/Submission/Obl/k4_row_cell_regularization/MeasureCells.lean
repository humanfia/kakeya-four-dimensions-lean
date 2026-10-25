import Submission.Lib.K4IncidenceWitnesses

/-!
# Incidence cells: the measure-theoretic setup of the graph construction

The frozen incidence hypotheses are bundled in `IncHyp`, with the loss `L` (`= N ^ η`) and
the mesh `h` (`= N ^ (-a)`) as parameters.  An incidence `p = (l, t)` has a position
`z = (t, b l + t v l)`, a four-dimensional point cell `incCell` (position cell and row bin) and
a velocity bin `incBin`.  `goodSet` holds the incidences in the time support satisfying the
row conditions (it has full mass), and `longSet` those whose trajectory spends a long time in
`goodSet`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_row_cell_regularization

-- Adapted from this LOT tree, o072, session x0247, MeasureCells.lean,
-- commit b33e4e7 (and d5ac49b). Long-time estimates use the accepted library API.
abbrev Point := Fin 4 → ℤ

def pointProjection (v : ℝ) (p : Point) : ℝ × ℝ :=
  ((p 1 : ℝ) - v * (p 0 : ℝ), (p 2 : ℝ) + v * (p 3 : ℝ))

noncomputable def roundedProjection (v : ℝ) (p : Point) : ℤ × ℤ :=
  (⌊(pointProjection v p).1⌋, ⌊(pointProjection v p).2⌋)

/-- Trajectory position `z = (t, b + t v)` of an incidence. -/
def trajPos {α : Type*} (b v : α → ℝ) (p : α × ℝ) : Fin 2 → ℝ :=
  ![p.2, b p.1 + p.2 * v p.1]

/-- The frozen incidence hypotheses, with the loss `L` (`= N ^ η`) and the mesh `h`. -/
structure IncHyp {α : Type} [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
    (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (π : Measure ℝ) (E : ℝ)
    (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) (h L S : ℝ) : Prop where
  meas_b : Measurable b
  meas_v : Measurable v
  meas_H : Measurable H
  meas_T : Measurable T
  prob_ν : IsProbabilityMeasure ν
  prob_π : IsProbabilityMeasure π
  h_pos : 0 < h
  h_lt_one : h < 1
  one_le_L : 1 ≤ L
  h_le_E : h ≤ E
  E_le_one : E ≤ 1
  traj_bound : ∀ l, |b l| + |v l| ≤ L
  domination : μ ≤ ENNReal.ofReal L • (ν.prod volume)
  time_support : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  mass_lower : ENNReal.ofReal (1 / L) ≤ μ univ
  palette_cap : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
    π (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (L * r ^ S)
  joint_cap : ∀ (q₀ : Fin 2 → ℤ) (j : ℤ),
    μ {p | (fun i => ⌊trajPos b v p i / h⌋) = q₀ ∧ ⌊v p.1 / h⌋ = j} ≤
      ENNReal.ofReal (L * h ^ 2) * π (Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h))
  bins_card : ∀ q₀, ((F q₀).card : ℝ) ≤ L
  row : ∀ᵐ p ∂μ, (∀ j, |T p j| ≤ L) ∧
    (fun j => ⌊T p j / E⌋) ∈ F (fun i => ⌊trajPos b v p i / h⌋) ∧
    |T p 0 + v p.1 * T p 1 - H p.1| ≤ L * E

variable {α : Type} [MeasurableSpace α]

/-- Position cell `q` of an incidence. -/
noncomputable def posCell (h : ℝ) (b v : α → ℝ) (p : α × ℝ) : Fin 2 → ℤ :=
  fun i => ⌊trajPos b v p i / h⌋

/-- The four-dimensional point cell of an incidence: its position cell and its row bin. -/
noncomputable def incCell (h E : ℝ) (b v : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    Point :=
  ![⌊p.2 / h⌋, ⌊(b p.1 + p.2 * v p.1) / h⌋, ⌊T p 0 / E⌋, ⌊T p 1 / E⌋]

/-- Velocity bin of an incidence. -/
noncomputable def incBin (h : ℝ) (v : α → ℝ) (p : α × ℝ) : ℤ := ⌊v p.1 / h⌋

/-- Good incidences: time in `[0,1]` and the three row conditions. -/
def goodSet (h E L : ℝ) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ)
    (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)) : Set (α × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ ((∀ j, |T p j| ≤ L) ∧
    (fun j => ⌊T p j / E⌋) ∈ F (posCell h b v p) ∧
    |T p 0 + v p.1 * T p 1 - H p.1| ≤ L * E)}

/-- Incidences whose trajectory spends time at least `r` in `G`. -/
def longSet (G : Set (α × ℝ)) (r : ℝ) : Set (α × ℝ) :=
  Submission.Lib.K4IncidenceWitnesses.longTimeIncidences G r

theorem incCell_zero (h E : ℝ) (b v : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    incCell h E b v T p 0 = ⌊p.2 / h⌋ := rfl

theorem incCell_one (h E : ℝ) (b v : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    incCell h E b v T p 1 = ⌊(b p.1 + p.2 * v p.1) / h⌋ := rfl

theorem incCell_two (h E : ℝ) (b v : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    incCell h E b v T p 2 = ⌊T p 0 / E⌋ := rfl

theorem incCell_three (h E : ℝ) (b v : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (p : α × ℝ) :
    incCell h E b v T p 3 = ⌊T p 1 / E⌋ := rfl

theorem posCell_eq (h : ℝ) (b v : α → ℝ) (p : α × ℝ) :
    posCell h b v p = ![⌊p.2 / h⌋, ⌊(b p.1 + p.2 * v p.1) / h⌋] := by
  funext i
  fin_cases i <;> rfl

theorem posCell_eq_of_incCell {h E : ℝ} {b v : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
    {p : α × ℝ} {c : Point} (hc : incCell h E b v T p = c) :
    posCell h b v p = ![c 0, c 1] := by
  rw [posCell_eq, ← hc]
  rfl

section Measurability

theorem measurable_trajPos_apply {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v)
    (i : Fin 2) : Measurable fun p : α × ℝ => trajPos b v p i := by
  fin_cases i
  · exact measurable_snd
  · exact (hb.comp measurable_fst).add (measurable_snd.mul (hv.comp measurable_fst))

theorem measurable_posCell {h : ℝ} {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) :
    Measurable (posCell h b v) :=
  Measurable.of_eval fun i => ((measurable_trajPos_apply hb hv i).div_const h).floor

theorem measurable_incCell {h E : ℝ} {b v : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
    (hb : Measurable b) (hv : Measurable v) (hT : Measurable T) :
    Measurable (incCell h E b v T) := by
  apply Measurable.of_eval
  intro i
  have hT0 : Measurable fun p : α × ℝ => T p 0 := (measurable_pi_apply 0).comp hT
  have hT1 : Measurable fun p : α × ℝ => T p 1 := (measurable_pi_apply 1).comp hT
  fin_cases i
  · exact (measurable_snd.div_const h).floor
  · exact (((hb.comp measurable_fst).add
      (measurable_snd.mul (hv.comp measurable_fst))).div_const h).floor
  · exact (hT0.div_const E).floor
  · exact (hT1.div_const E).floor

theorem measurable_incBin {h : ℝ} {v : α → ℝ} (hv : Measurable v) :
    Measurable (incBin h v) :=
  ((hv.comp measurable_fst).div_const h).floor

theorem measurableSet_incCell_eq {h E : ℝ} {b v : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
    (hb : Measurable b) (hv : Measurable v) (hT : Measurable T) (c : Point) :
    MeasurableSet {p | incCell h E b v T p = c} :=
  measurable_incCell hb hv hT (measurableSet_singleton c)

theorem measurableSet_incBin_eq {h : ℝ} {v : α → ℝ} (hv : Measurable v) (d : ℤ) :
    MeasurableSet {p | incBin h v p = d} :=
  measurable_incBin hv (measurableSet_singleton d)

theorem measurableSet_goodSet {h E L : ℝ} {b v H : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)}
    (hb : Measurable b) (hv : Measurable v) (hH : Measurable H) (hT : Measurable T) :
    MeasurableSet (goodSet h E L b v H T F) := by
  have hT0 : Measurable fun p : α × ℝ => T p 0 := (measurable_pi_apply 0).comp hT
  have hT1 : Measurable fun p : α × ℝ => T p 1 := (measurable_pi_apply 1).comp hT
  have h1 : MeasurableSet {p : α × ℝ | p.2 ∈ Icc (0 : ℝ) 1} :=
    measurable_snd measurableSet_Icc
  have h2 : MeasurableSet {p : α × ℝ | ∀ j, |T p j| ≤ L} := by
    have : {p : α × ℝ | ∀ j, |T p j| ≤ L} = ⋂ j, {p | |T p j| ≤ L} := by
      ext p; simp
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((measurable_pi_apply j).comp hT).abs measurable_const
  have h3 : MeasurableSet {p : α × ℝ | (fun j => ⌊T p j / E⌋) ∈ F (posCell h b v p)} := by
    have hm : Measurable fun p : α × ℝ =>
        ((fun j => ⌊T p j / E⌋ : Fin 2 → ℤ), posCell h b v p) := by
      refine Measurable.prodMk ?_ (measurable_posCell hb hv)
      exact Measurable.of_eval fun j => (((measurable_pi_apply j).comp hT).div_const E).floor
    exact hm (Set.to_countable {x : (Fin 2 → ℤ) × (Fin 2 → ℤ) | x.1 ∈ F x.2}).measurableSet
  have h4 : MeasurableSet {p : α × ℝ | |T p 0 + v p.1 * T p 1 - H p.1| ≤ L * E} :=
    measurableSet_le ((hT0.add ((hv.comp measurable_fst).mul hT1)).sub
      (hH.comp measurable_fst)).abs measurable_const
  exact h1.inter (h2.inter (h3.inter h4))

theorem measurableSet_longSet {G : Set (α × ℝ)} (hG : MeasurableSet G) (r : ℝ) :
    MeasurableSet (longSet G r) :=
  hG.inter (measurableSet_le measurable_const
    ((measurable_measure_prodMk_left hG).comp measurable_fst))

end Measurability

section MassFacts

variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ} {T : α × ℝ → Fin 2 → ℝ}
  {π : Measure ℝ} {E : ℝ} {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

theorem IncHyp.measurableSet_goodSet (hyp : IncHyp ν μ b v H T π E F h L S) :
    MeasurableSet (goodSet h E L b v H T F) :=
  Submission.Obl.k4_row_cell_regularization.measurableSet_goodSet
    hyp.meas_b hyp.meas_v hyp.meas_H hyp.meas_T

theorem IncHyp.measure_univ_le (hyp : IncHyp ν μ b v H T π E F h L S) :
    μ univ ≤ ENNReal.ofReal L := by
  have := hyp.prob_ν
  have hs : MeasurableSet ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Icc
  calc μ univ = μ (univ ×ˢ Icc (0 : ℝ) 1) := by
        rw [← measure_add_measure_compl hs, hyp.time_support, add_zero]
    _ ≤ (ENNReal.ofReal L • ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := hyp.domination _
    _ = ENNReal.ofReal L * (ν univ * volume (Icc (0 : ℝ) 1)) := by
        rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    _ = ENNReal.ofReal L := by simp

theorem IncHyp.measure_ne_top (hyp : IncHyp ν μ b v H T π E F h L S) (s : Set (α × ℝ)) :
    μ s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono (subset_univ s)).trans
    hyp.measure_univ_le)

theorem IncHyp.measure_goodSet_compl (hyp : IncHyp ν μ b v H T π E F h L S) :
    μ (goodSet h E L b v H T F)ᶜ = 0 := by
  have hrow := hyp.row
  rw [ae_iff] at hrow
  apply measure_mono_null _ (measure_union_null hyp.time_support hrow)
  intro p hp
  by_cases ht : p.2 ∈ Icc (0 : ℝ) 1
  · right
    intro hrowp
    exact hp ⟨ht, hrowp⟩
  · left
    simp only [mem_compl_iff, mem_prod, mem_univ, true_and]
    exact ht

theorem IncHyp.measure_goodSet (hyp : IncHyp ν μ b v H T π E F h L S) :
    μ (goodSet h E L b v H T F) = μ univ := by
  rw [← measure_add_measure_compl hyp.measurableSet_goodSet, hyp.measure_goodSet_compl,
    add_zero]

/-- The long-time incidences keep half of the original mass. -/
theorem IncHyp.measure_longSet (hyp : IncHyp ν μ b v H T π E F h L S) :
    ENNReal.ofReal (1 / (2 * L)) ≤
      μ (longSet (goodSet h E L b v H T F) (1 / (2 * L ^ 2))) := by
  have := hyp.prob_ν
  have hL : 0 < L := lt_of_lt_of_le one_pos hyp.one_le_L
  have hm : ENNReal.ofReal (1 / L) ≤ μ (goodSet h E L b v H T F) := by
    rw [hyp.measure_goodSet]
    exact hyp.mass_lower
  have hlong := Submission.Lib.K4IncidenceWitnesses.longTimeIncidences_mass ν μ
    hL (one_div_pos.mpr hL) hyp.domination hyp.measurableSet_goodSet hm
  have e₁ : 1 / L / 2 = 1 / (2 * L) := by ring
  have e₂ : 1 / L / (2 * L) = 1 / (2 * L ^ 2) := by field_simp
  rw [e₁, e₂] at hlong
  exact hlong

end MassFacts

end Submission.Obl.k4_row_cell_regularization
