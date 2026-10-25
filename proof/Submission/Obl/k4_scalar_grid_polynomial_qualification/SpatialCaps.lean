import Submission.Lib.K4CommonLocalChoice
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_initial_true_horizon

noncomputable section

def cubeIndices {n : ℕ} (q r : ℝ) (a : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc ⌊a j / q⌋ ⌊(a j + r) / q⌋

theorem cell_mem_cubeIndices {n : ℕ} {q r : ℝ} (hq : 0 < q)
    (a x : Fin n → ℝ) (hx : ∀ j, x j ∈ Ico (a j) (a j + r)) :
    cell q x ∈ cubeIndices q r a := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right (hx j).1 hq.le),
      Int.floor_mono (div_le_div_of_nonneg_right (hx j).2.le hq.le)⟩

theorem card_cubeIndices {n : ℕ} {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (a : Fin n → ℝ) :
    ((cubeIndices q r a).card : ENNReal) ≤ ENNReal.ofReal ((r / q + 2) ^ n) := by
  have hcard (j : Fin n) : ((Finset.Icc ⌊a j / q⌋ ⌊(a j + r) / q⌋).card : ℝ) ≤ r / q + 2 := by
    have h := card_Icc_floor_le (div_le_div_of_nonneg_right (by linarith : a j ≤ a j + r) hq.le)
    convert h using 1; ring
  have hcard' (j : Fin n) :
      ((Finset.Icc ⌊a j / q⌋ ⌊(a j + r) / q⌋).card : ENNReal) ≤
        ENNReal.ofReal (r / q + 2) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcard j)
  simp only [cubeIndices, Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : Fin n, ENNReal.ofReal (r / q + 2) :=
      Finset.prod_le_prod (fun j _ => hcard' j)
    _ = ENNReal.ofReal ((r / q + 2) ^ n) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (ENNReal.ofReal_pow (by positivity : 0 ≤ r / q + 2) n).symm

/-- Caps on the frozen floor cells extend to translated spatial cubes.
This keeps the original measure, and applies with a velocity-bin condition
already included in `E`. -/
theorem cube_cap_of_cell_caps {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (E : Set Ω) (x : Ω → Fin n → ℝ)
    {q r : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (C : ENNReal)
    (hcap : ∀ z, μ {p | p ∈ E ∧ cell q (x p) = z} ≤ C)
    (a : Fin n → ℝ) :
    μ {p | p ∈ E ∧ ∀ j, x p j ∈ Ico (a j) (a j + r)} ≤
      ENNReal.ofReal ((r / q + 2) ^ n) * C := by
  classical
  let L := cubeIndices q r a
  have hcover : {p | p ∈ E ∧ ∀ j, x p j ∈ Ico (a j) (a j + r)} ⊆
      ⋃ z ∈ L, {p | p ∈ E ∧ cell q (x p) = z} := by
    intro p hp
    exact mem_iUnion₂.mpr ⟨cell q (x p), cell_mem_cubeIndices hq a (x p) hp.2, hp.1, rfl⟩
  calc
    _ ≤ μ (⋃ z ∈ L, {p | p ∈ E ∧ cell q (x p) = z}) := measure_mono hcover
    _ ≤ ∑ z ∈ L, μ {p | p ∈ E ∧ cell q (x p) = z} := measure_biUnion_finset_le L _
    _ ≤ ∑ _z ∈ L, C := Finset.sum_le_sum (fun z _ => hcap z)
    _ = (L.card : ENNReal) * C := by simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((r / q + 2) ^ n) * C :=
      mul_le_mul_left (card_cubeIndices hq hr a) C

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
