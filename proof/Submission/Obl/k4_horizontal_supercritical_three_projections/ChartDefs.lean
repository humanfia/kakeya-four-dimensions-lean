/- From this LOT obligation o226, session x0787, as shared in x0810 commit 07dee0c9; unchanged chart definitions. -/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Charts
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Grid

/-!
# Parameter charts for the supercritical scalar projection

A chart fixes the fine direction bin `⌊b₃/χ⌋ = β` and the `D`-bins of the
two intercepts `⌊b₀/D⌋ = P`, `⌊b₁/D⌋ = Q`, on bounded horizontal trajectories.
Inside a chart the scalar parameter is `R(t) = r - 2tp` for the normalized
intercepts `p = (b₀ - PD)/D`, `r = (b₁ - QD)/D` (paper, Proposition 9.7).
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Parent

noncomputable section

/-- The frozen dyadic time block `I T j`. -/
def blockTime (T : ℕ) (j : ℕ) : Set ℝ :=
  Icc ((j : ℝ) / (2 : ℝ) ^ T) (((j : ℝ) + 1) / (2 : ℝ) ^ T)

/-- A chart: bounded horizontal trajectories with fixed parameter bins. -/
def chartSet {α : Type*} (b : α → Fin 6 → ℝ) (K ζ D χ : ℝ) (P Q β : ℤ) : Set α :=
  {l | |b l 0| ≤ K ∧ |b l 3| ≤ K ∧ |b l 4 + b l 0| ≤ ζ ∧
    ⌊b l 0 / D⌋ = P ∧ ⌊b l 1 / D⌋ = Q ∧ ⌊b l 3 / χ⌋ = β}

/-- The scalar cell of an incidence at time `t` in the chart `(P, Q)`. -/
def chartCell (D σ : ℝ) (P Q : ℤ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  ![⌊t / σ⌋, ⌊scalarParameter t ((b 0 - P * D) / D) ((b 1 - Q * D) / D) / σ⌋]

theorem measurableSet_chartSet {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (K ζ D χ : ℝ) (P Q β : ℤ) :
    MeasurableSet (chartSet b K ζ D χ P Q β) := by
  have h0 : Measurable fun l => b l 0 := (measurable_pi_apply 0).comp hb
  have h1 : Measurable fun l => b l 1 := (measurable_pi_apply 1).comp hb
  have h3 : Measurable fun l => b l 3 := (measurable_pi_apply 3).comp hb
  have h4 : Measurable fun l => b l 4 := (measurable_pi_apply 4).comp hb
  refine MeasurableSet.inter (measurableSet_le h0.abs measurable_const) ?_
  refine MeasurableSet.inter (measurableSet_le h3.abs measurable_const) ?_
  refine MeasurableSet.inter (measurableSet_le (h4.add h0).abs measurable_const) ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact (Int.measurable_floor.comp (h0.div_const D)) (measurableSet_singleton P)
  · exact (Int.measurable_floor.comp (h1.div_const D)) (measurableSet_singleton Q)
  · exact (Int.measurable_floor.comp (h3.div_const χ)) (measurableSet_singleton β)

/-- Position of a number inside its floor cell. -/
theorem floor_cell_mem {x δ : ℝ} (hδ : 0 < δ) :
    (⌊x / δ⌋ : ℝ) * δ ≤ x ∧ x < ((⌊x / δ⌋ : ℝ) + 1) * δ := by
  have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (x / δ))
  have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x / δ))
  exact ⟨h₀, h₁⟩

theorem abs_sub_floor_mul_le {x δ : ℝ} (hδ : 0 < δ) :
    |x - (⌊x / δ⌋ : ℝ) * δ| ≤ δ := by
  obtain ⟨h₀, h₁⟩ := floor_cell_mem (x := x) hδ
  rw [abs_le]
  constructor <;> nlinarith

/-- The elementary consequences of chart membership. -/
theorem chartSet_bounds {α : Type*} {b : α → Fin 6 → ℝ} {K ζ D χ : ℝ}
    {P Q β : ℤ} (hD : 0 < D) (hχ : 0 < χ) {l : α}
    (hl : l ∈ chartSet b K ζ D χ P Q β) :
    0 ≤ (b l 0 - P * D) / D ∧ (b l 0 - P * D) / D < 1 ∧
      0 ≤ (b l 1 - Q * D) / D ∧ (b l 1 - Q * D) / D < 1 ∧
      |b l 0 - P * D| ≤ D ∧ |b l 3 - β * χ| ≤ χ ∧
      |(P : ℝ) * D| ≤ K + D ∧ |(β : ℝ) * χ| ≤ K + χ ∧
      |b l 0| ≤ K ∧ |b l 3| ≤ K ∧ |b l 4 + b l 0| ≤ ζ := by
  obtain ⟨hb0, hb3, he, hP, hQ, hβ⟩ := hl
  obtain ⟨hP₀, hP₁⟩ := floor_cell_mem (x := b l 0) hD
  obtain ⟨hQ₀, hQ₁⟩ := floor_cell_mem (x := b l 1) hD
  rw [hP] at hP₀ hP₁
  rw [hQ] at hQ₀ hQ₁
  have hβ' := abs_sub_floor_mul_le (x := b l 3) hχ
  rw [hβ] at hβ'
  have hP' : |b l 0 - P * D| ≤ D := by
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨?_, ?_, ?_, ?_, hP', hβ', ?_, ?_, hb0, hb3, he⟩
  · exact div_nonneg (by linarith) hD.le
  · rw [div_lt_one hD]; linarith
  · exact div_nonneg (by linarith) hD.le
  · rw [div_lt_one hD]; linarith
  · calc |(P : ℝ) * D| = |b l 0 - (b l 0 - P * D)| := by ring_nf
      _ ≤ |b l 0| + |b l 0 - P * D| := abs_sub _ _
      _ ≤ K + D := add_le_add hb0 hP'
  · calc |(β : ℝ) * χ| = |b l 3 - (b l 3 - β * χ)| := by ring_nf
      _ ≤ |b l 3| + |b l 3 - β * χ| := abs_sub _ _
      _ ≤ K + χ := add_le_add hb3 hβ'

/-- The scalar parameter of a chart trajectory lies in `[-2, 1)`. -/
theorem chart_scalarParameter_mem {α : Type*} {b : α → Fin 6 → ℝ} {K ζ D χ : ℝ}
    {P Q β : ℤ} (hD : 0 < D) (hχ : 0 < χ) {l : α}
    (hl : l ∈ chartSet b K ζ D χ P Q β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    -2 ≤ scalarParameter t ((b l 0 - P * D) / D) ((b l 1 - Q * D) / D) ∧
      scalarParameter t ((b l 0 - P * D) / D) ((b l 1 - Q * D) / D) ≤ 1 := by
  obtain ⟨hp₀, hp₁, hr₀, hr₁, -⟩ := chartSet_bounds hD hχ hl
  unfold scalarParameter
  constructor <;> nlinarith [ht.1, ht.2]

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
