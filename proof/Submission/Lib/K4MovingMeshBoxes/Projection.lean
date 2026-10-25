/-
Adapted from: here:o222 (x0774), ProjectedCellCap.lean, commit 4d22216c.
-/
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! The scalar mesh cap inside a fine major-coordinate group. -/

namespace Submission.Lib.K4MovingMeshBoxes

open MeasureTheory Set

noncomputable section

private theorem mesh_floor_error {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |x - a * (⌊x / a⌋ : ℝ)| ≤ a := by
  have hlo := (le_div_iff₀ ha).mp (Int.floor_le (x / a))
  have hhi := (div_lt_iff₀ ha).mp (Int.lt_floor_add_one (x / a))
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith


def basePoint (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

def projectedCell (sigma g y₀ y₁ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 2 → ℤ :=
  ![⌊t / sigma⌋, ⌊((b 1 + t * b 4 - y₀ - t * y₁) / g) / sigma⌋]

def majorGroup (chi z₀ z₁ : ℝ) : Set (Fin 6 → ℝ) :=
  {b | |b 0 - z₀| ≤ chi ∧ |b 3 - z₁| ≤ chi}

theorem projectedCell_mem_movingBox
    {sigma g chi y₀ y₁ z₀ z₁ t : ℝ} (hs : 0 < sigma) (hg : 0 < g)
    (hc : 0 ≤ chi) (b : Fin 6 → ℝ) (q : Fin 2 → ℤ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hgroup : b ∈ majorGroup chi z₀ z₁)
    (hcell : projectedCell sigma g y₀ y₁ b t = q) :
    basePoint b t ∈ movingBox ((q 0 : ℝ) * sigma) sigma
      ![z₀, y₀ + (q 1 : ℝ) * g * sigma] ![z₁, y₁] ![2 * chi, g * sigma] := by
  have htime : ⌊t / sigma⌋ = q 0 := by
    simpa [projectedCell] using congrFun hcell 0
  have hspace : ⌊((b 1 + t * b 4 - y₀ - t * y₁) / g) / sigma⌋ = q 1 := by
    simpa [projectedCell] using congrFun hcell 1
  have ht' := mesh_floor_error hs t
  rw [htime, mul_comm sigma] at ht'
  refine ⟨ht', ?_⟩
  intro i
  fin_cases i
  · change |b 0 + t * b 3 - (z₀ + t * z₁)| ≤ 2 * chi
    have ht1 : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    calc
      _ = |(b 0 - z₀) + t * (b 3 - z₁)| := by ring_nf
      _ ≤ |b 0 - z₀| + |t| * |b 3 - z₁| := by
        simpa only [abs_mul] using abs_add_le (b 0 - z₀) (t * (b 3 - z₁))
      _ ≤ chi + 1 * chi := add_le_add hgroup.1
        (mul_le_mul ht1 hgroup.2 (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  · change |b 1 + t * b 4 - (y₀ + (q 1 : ℝ) * g * sigma + t * y₁)| ≤ g * sigma
    have h := mesh_floor_error hs
      ((b 1 + t * b 4 - y₀ - t * y₁) / g)
    rw [hspace] at h
    have heq : b 1 + t * b 4 - (y₀ + (q 1 : ℝ) * g * sigma + t * y₁) =
        g * ((b 1 + t * b 4 - y₀ - t * y₁) / g - sigma * (q 1 : ℝ)) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos hg]
    exact mul_le_mul_of_nonneg_left h hg.le

/-- Integrating the three-dimensional cap over one major group gives the
scalar factor `sigma² * chi * g`. The extra condition can include the
terminal hidden bin and the fixed original velocity bin. -/
theorem projected_cell_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (condition : α × ℝ → Prop)
    {delta sigma g chi L C y₀ y₁ z₀ z₁ : ℝ}
    (hd : 0 < delta) (hs : 0 < sigma) (hg : 0 < g) (hc : 0 ≤ chi)
    (hdr : delta ≤ sigma) (hdz : delta ≤ 2 * chi) (hdy : delta ≤ g * sigma)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hz₁ : |z₁| ≤ L) (hy₁ : |y₁| ≤ L)
    (hmz : L * delta ≤ 2 * chi) (hmy : L * delta ≤ g * sigma)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (basePoint (b p.1) p.2) = q ∧ condition p} ≤
        ENNReal.ofReal (C * delta ^ 3))
    (q : Fin 2 → ℤ) :
    μ {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ b p.1 ∈ majorGroup chi z₀ z₁ ∧
      projectedCell sigma g y₀ y₁ (b p.1) p.2 = q ∧ condition p} ≤
      ENNReal.ofReal (1200 * C * sigma ^ 2 * chi * g) := by
  let center : Fin 2 → ℝ := ![z₀, y₀ + (q 1 : ℝ) * g * sigma]
  let velocity : Fin 2 → ℝ := ![z₁, y₁]
  let width : Fin 2 → ℝ := ![2 * chi, g * sigma]
  have hv (i : Fin 2) : |velocity i| ≤ L := by fin_cases i <;> assumption
  have hdw (i : Fin 2) : delta ≤ width i := by fin_cases i <;> assumption
  have hmove (i : Fin 2) : L * delta ≤ width i := by fin_cases i <;> assumption
  have hsub : {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ b p.1 ∈ majorGroup chi z₀ z₁ ∧
      projectedCell sigma g y₀ y₁ (b p.1) p.2 = q ∧ condition p} ⊆
      {p | basePoint (b p.1) p.2 ∈
        movingBox ((q 0 : ℝ) * sigma) sigma center velocity width ∧ condition p} := by
    intro p hp
    exact ⟨projectedCell_mem_movingBox hs hg hc _ q hp.1 hp.2.1 hp.2.2.1, hp.2.2.2⟩
  apply (measure_mono hsub).trans
  convert measure_movingBox_of_cell_cap μ (fun p => basePoint (b p.1) p.2) condition
    hd hdr hL hC ((q 0 : ℝ) * sigma) center velocity width hv hdw hmove hcap using 1
  congr 1
  dsimp [width]
  ring

end

end Submission.Lib.K4MovingMeshBoxes
