/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/Charts.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Geometry
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FunProp

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open Set MeasureTheory

noncomputable section

def chartCode (D χ : ℝ) (b : Fin 6 → ℝ) : Fin 3 → ℤ :=
  ![⌊b 0 / D⌋, ⌊b 1 / D⌋, ⌊b 3 / χ⌋]

theorem measurable_chartCode {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (D χ : ℝ) :
    Measurable (fun l => chartCode D χ (b l)) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> exact Int.measurable_floor.comp (by fun_prop)

private theorem floor_center_bound {a δ : ℝ} (hδ : 0 < δ) :
    |a - (⌊a / δ⌋ : ℝ) * δ| ≤ δ := by
  have h₀ := (le_div_iff₀ hδ).mp (Int.floor_le (a / δ))
  have h₁ := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (a / δ))
  rw [abs_le]
  constructor <;> nlinarith only [h₀, h₁, hδ]

theorem chartCode_center_bounds {D χ : ℝ} (hD : 0 < D) (hχ : 0 < χ)
    {b : Fin 6 → ℝ} {q : Fin 3 → ℤ} (hq : chartCode D χ b = q) :
    |b 0 - (q 0 : ℝ) * D| ≤ D ∧ |b 1 - (q 1 : ℝ) * D| ≤ D ∧
      |b 3 - (q 2 : ℝ) * χ| ≤ χ := by
  have h₀ : ⌊b 0 / D⌋ = q 0 := congrFun hq 0
  have h₁ : ⌊b 1 / D⌋ = q 1 := congrFun hq 1
  have h₂ : ⌊b 3 / χ⌋ = q 2 := congrFun hq 2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [h₀] using floor_center_bound (a := b 0) hD
  · simpa only [h₁] using floor_center_bound (a := b 1) hD
  · simpa only [h₂] using floor_center_bound (a := b 3) hχ

def projectedCoefficients (pc qc D : ℝ) (b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![(b 1 - qc) / D, -2 * ((b 0 - pc) / D), b 2, b 5, 0]

theorem measurable_projectedCoefficients {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (pc qc D : ℝ) :
    Measurable (fun l => projectedCoefficients pc qc D (b l)) := by
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> dsimp [projectedCoefficients] <;> fun_prop

theorem projectedCoefficients_bound {pc qc D K : ℝ} (hD : 0 < D) (hK : 1 ≤ K)
    {b : Fin 6 → ℝ} (hp : |b 0 - pc| ≤ D) (hq : |b 1 - qc| ≤ D)
    (h₂ : |b 2| ≤ K) (h₅ : |b 5| ≤ K) (i : Fin 5) :
    |projectedCoefficients pc qc D b i| ≤ 2 * K := by
  have hp' : |(b 0 - pc) / D| ≤ 1 := by
    rw [abs_div, abs_of_pos hD]
    exact (div_le_one hD).mpr hp
  have hq' : |(b 1 - qc) / D| ≤ 1 := by
    rw [abs_div, abs_of_pos hD]
    exact (div_le_one hD).mpr hq
  fin_cases i
  · change |(b 1 - qc) / D| ≤ 2 * K
    linarith only [hq', hK]
  · change |-2 * ((b 0 - pc) / D)| ≤ 2 * K
    rw [abs_mul]
    rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
    linarith only [hp', hK]
  · change |b 2| ≤ 2 * K
    linarith only [h₂, hK]
  · change |b 5| ≤ 2 * K
    linarith only [h₅, hK]
  · change |(0 : ℝ)| ≤ 2 * K
    rw [abs_zero]
    linarith only [hK]

/-- Clamping outside the prior chart makes the global coefficient bound in
the frozen scalar input available on the unchanged trajectory type. -/
def chartCoefficients {α : Type*} (A : Set α) (b : α → Fin 6 → ℝ)
    (pc qc D : ℝ) : α → Fin 5 → ℝ :=
  A.indicator (fun l => projectedCoefficients pc qc D (b l))

theorem measurable_chartCoefficients {α : Type*} [MeasurableSpace α]
    {A : Set α} (hA : MeasurableSet A) {b : α → Fin 6 → ℝ}
    (hb : Measurable b) (pc qc D : ℝ) : Measurable (chartCoefficients A b pc qc D) :=
  (measurable_projectedCoefficients hb pc qc D).indicator hA

theorem chartCoefficients_bound {α : Type*} {A : Set α} {b : α → Fin 6 → ℝ}
    {pc qc D K : ℝ} (hD : 0 < D) (hK : 1 ≤ K)
    (hA : ∀ l ∈ A, |b l 0 - pc| ≤ D ∧ |b l 1 - qc| ≤ D ∧
      |b l 2| ≤ K ∧ |b l 5| ≤ K) (l : α) (i : Fin 5) :
    |chartCoefficients A b pc qc D l i| ≤ 2 * K := by
  by_cases hl : l ∈ A
  · obtain ⟨hp, hq, h₂, h₅⟩ := hA l hl
    simpa only [chartCoefficients, indicator_of_mem hl] using
      projectedCoefficients_bound hD hK hp hq h₂ h₅ i
  · simp only [chartCoefficients, indicator_of_notMem hl, Pi.zero_apply, abs_zero]
    linarith only [hK]

theorem projectedCoefficients_y (pc qc D : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    projectedCoefficients pc qc D b 0 + t * projectedCoefficients pc qc D b 1 =
      scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) := by
  simp only [projectedCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold scalarParameter
  ring

theorem projectedCoefficients_x (pc qc D : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    projectedCoefficients pc qc D b 2 + t * projectedCoefficients pc qc D b 3 +
      t ^ 2 * projectedCoefficients pc qc D b 4 = b 2 + t * b 5 := by
  simp [projectedCoefficients]

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
