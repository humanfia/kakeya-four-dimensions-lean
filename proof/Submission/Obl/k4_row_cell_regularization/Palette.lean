import Submission.Obl.k4_row_cell_regularization.OriginalMass
import Submission.Obl.k4_oss_weighted_level_transfer.Discretize

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Submission.Obl.k4_row_cell_regularization

/-- The actual half-open velocity cells. -/
def velocityCell (h : ℝ) (d : ℤ) : Set ℝ :=
  Ico ((d : ℝ) * h) (((d : ℝ) + 1) * h)

theorem velocityCell_eq_floor {h : ℝ} (hh : 0 < h) (d : ℤ) :
    velocityCell h d = {x : ℝ | ⌊x / h⌋ = d} := by
  convert Submission.Obl.k4_oss_weighted_level_transfer.Ico_eq_cell hh d using 1 <;>
    simp only [velocityCell, Submission.Obl.k4_oss_collision_cauchy_schwarz.cell]
  congr 1 <;> ring

theorem velocityCell_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (fun d d' : ℤ => Disjoint (velocityCell h d) (velocityCell h d')) := by
  intro d d' hdd
  rw [velocityCell_eq_floor hh, velocityCell_eq_floor hh]
  exact Set.disjoint_left.mpr fun x hx hy => hdd (hx.symm.trans hy)

theorem binWeight_nonneg (π : Measure ℝ) (h : ℝ) (d : ℤ) :
    0 ≤ binWeight π h d := ENNReal.toReal_nonneg

theorem sum_binWeight_eq {h : ℝ} (hh : 0 < h) (π : Measure ℝ) [IsFiniteMeasure π]
    (D : Finset ℤ) :
    (∑ d ∈ D, binWeight π h d) = π.real (⋃ d ∈ D, velocityCell h d) := by
  exact (measureReal_biUnion_finset
    (fun d _ d' _ hdd => velocityCell_disjoint hh hdd)
    (fun _ _ => measurableSet_Ico)).symm

theorem sum_binWeight_le_one {h : ℝ} (hh : 0 < h) (π : Measure ℝ)
    [IsProbabilityMeasure π] (D : Finset ℤ) :
    (∑ d ∈ D, binWeight π h d) ≤ 1 := by
  rw [sum_binWeight_eq hh π D]
  exact measureReal_le_one

variable {α : Type} [MeasurableSpace α]
variable {ν : Measure α} {μ : Measure (α × ℝ)} {b v H : α → ℝ}
    {T : α × ℝ → Fin 2 → ℝ} {π : Measure ℝ} {E : ℝ}
    {F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)} {h L S : ℝ}

/-- The weight of velocity cells with left corners in an interval satisfies the original cap. -/
theorem IncHyp.binWeight_cap (hyp : IncHyp ν μ b v H T π E F h L S)
    (D : Finset ℤ) (x r : ℝ) (hr : h ≤ r) (hr1 : r ≤ 1) :
    (∑ d ∈ D.filter (fun d => binVel h d ∈ Icc x (x + r)), binWeight π h d) ≤ L * r ^ S := by
  have := hyp.prob_π
  rw [sum_binWeight_eq hyp.h_pos]
  have hs : (⋃ d ∈ D.filter (fun d => binVel h d ∈ Icc x (x + r)), velocityCell h d) ⊆
      Icc ((x + r) - r) ((x + r) + r) := by
    intro y hy
    obtain ⟨d, hd, hy⟩ := mem_iUnion₂.mp hy
    have hd' := (Finset.mem_filter.mp hd).2
    change x ≤ (d : ℝ) * h ∧ (d : ℝ) * h ≤ x + r at hd'
    change (d : ℝ) * h ≤ y ∧ y < ((d : ℝ) + 1) * h at hy
    constructor <;> linarith
  have hm := (measure_mono hs).trans (hyp.palette_cap (x + r) r hr hr1)
  have hr0 : 0 < r := hyp.h_pos.trans_le hr
  have hL : 0 < L := lt_of_lt_of_le one_pos hyp.one_le_L
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ L * r ^ S), Measure.real] using hreal

/-- Every velocity-bin representative has the same bounded support as the original velocities,
up to one mesh step. -/
theorem incBins_velocity_bound {h L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {d : ℤ} (hd : d ∈ incBins h L) : |binVel h d| ≤ L + 1 := by
  obtain ⟨hd0, hd1⟩ := Finset.mem_Icc.mp hd
  have hd0' : (⌊-L / h⌋ : ℝ) ≤ d := Int.cast_le.mpr hd0
  have hd1' : (d : ℝ) ≤ ⌊L / h⌋ := Int.cast_le.mpr hd1
  have hf0 := Int.lt_floor_add_one (-L / h)
  have hf1 := Int.floor_le (L / h)
  have he0 : h * (-L / h) = -L := by field_simp
  have he1 : h * (L / h) = L := by field_simp
  have hlo := mul_le_mul_of_nonneg_left (show -L / h ≤ (d : ℝ) + 1 by linarith) hh.le
  have hhi := mul_le_mul_of_nonneg_left (hd1'.trans hf1) hh.le
  rw [he0] at hlo
  rw [he1] at hhi
  rw [binVel, abs_le]
  constructor <;> nlinarith

end Submission.Obl.k4_row_cell_regularization
