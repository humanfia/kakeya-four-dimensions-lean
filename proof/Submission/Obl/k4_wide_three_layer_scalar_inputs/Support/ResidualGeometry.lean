import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input
import Submission.Obl.k4_critical_conditional_row_preparation.JointGrid
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ShearedCells

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Finset
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- The sharp coefficient estimate at the normalized base resolutions. -/
theorem residual_quad_variation {pc : Fin 6 → ℝ} {H Kz σ t t' y y' : ℝ}
    (hH : 0 ≤ H) (hKz : 0 ≤ Kz) (hσ : 0 ≤ σ) (hpc : ∀ e, |pc e| ≤ H)
    (ht : |t| ≤ 1) (ht' : |t'| ≤ 1) (hy : |y| ≤ Kz) (hy' : |y'| ≤ Kz)
    (hdt : |t - t'| ≤ σ) (hdy : |y - y'| ≤ σ) :
    |quadZ pc t y - quadZ pc t' y'| ≤ H * (5 + 3 * Kz) * σ := by
  have htadd : |t + t'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hyadd : |y + y'| ≤ 2 * Kz := (abs_add_le _ _).trans (by linarith)
  have hA : |pc 1 + pc 3 * (t + t') + pc 4 * y| ≤ H * (3 + Kz) := by
    calc
      _ ≤ |pc 1| + |pc 3| * |t + t'| + |pc 4| * |y| := by
        simpa only [abs_mul] using abs_add_three (pc 1) (pc 3 * (t + t')) (pc 4 * y)
      _ ≤ H + H * 2 + H * Kz := by gcongr; exact hpc 1; exact hpc 3; exact hpc 4
      _ = _ := by ring
  have hB : |pc 2 + pc 4 * t' + pc 5 * (y + y')| ≤ H * (2 + 2 * Kz) := by
    calc
      _ ≤ |pc 2| + |pc 4| * |t'| + |pc 5| * |y + y'| := by
        simpa only [abs_mul] using abs_add_three (pc 2) (pc 4 * t') (pc 5 * (y + y'))
      _ ≤ H + H * 1 + H * (2 * Kz) := by gcongr; exact hpc 2; exact hpc 4; exact hpc 5
      _ = _ := by ring
  have hid : quadZ pc t y - quadZ pc t' y' =
      (pc 1 + pc 3 * (t + t') + pc 4 * y) * (t - t') +
      (pc 2 + pc 4 * t' + pc 5 * (y + y')) * (y - y') := by
    unfold quadZ
    ring
  rw [hid]
  calc
    _ ≤ |pc 1 + pc 3 * (t + t') + pc 4 * y| * |t - t'| +
        |pc 2 + pc 4 * t' + pc 5 * (y + y')| * |y - y'| := by
      simpa only [abs_mul] using abs_add_le
        ((pc 1 + pc 3 * (t + t') + pc 4 * y) * (t - t'))
        ((pc 2 + pc 4 * t' + pc 5 * (y + y')) * (y - y'))
    _ ≤ H * (3 + Kz) * σ + H * (2 + 2 * Kz) * σ := by gcongr
    _ = _ := by ring

/-- The finite normalized base grid. -/
def residualBaseCells (σ Kz : ℝ) : Finset (Fin 2 → ℤ) := by
  classical
  exact ((Icc (0 : ℤ) ⌊1 / σ⌋) ×ˢ floorBand σ 0 Kz).image (fun q => ![q.1, q.2])

theorem mem_residualBaseCells {σ Kz t y : ℝ} (hσ : 0 < σ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ Kz) :
    (![⌊t / σ⌋, ⌊y / σ⌋] : Fin 2 → ℤ) ∈ residualBaseCells σ Kz := by
  classical
  apply mem_image.mpr
  refine ⟨(⌊t / σ⌋, ⌊y / σ⌋), mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact mem_Icc.mpr ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 hσ.le),
      Int.floor_mono (div_le_div_of_nonneg_right ht.2 hσ.le)⟩
  · exact mem_floorBand hσ (by simpa using hy)

theorem residualBaseCells_card {σ Kz : ℝ} (hσ : 0 < σ) (hKz : 0 ≤ Kz) :
    ((residualBaseCells σ Kz).card : ℝ) ≤ (1 / σ + 2) * (2 * Kz / σ + 2) := by
  classical
  have ht : (((Icc (0 : ℤ) ⌊1 / σ⌋).card : ℕ) : ℝ) ≤ 1 / σ + 2 := by
    simpa using Submission.Obl.k4_scalar_initial_true_horizon.card_Icc_floor_le
      (show (0 : ℝ) ≤ 1 / σ by positivity)
  calc
    _ ≤ (((Icc (0 : ℤ) ⌊1 / σ⌋) ×ˢ floorBand σ 0 Kz).card : ℝ) := by
      exact_mod_cast (card_image_le (s := (Icc (0 : ℤ) ⌊1 / σ⌋) ×ˢ floorBand σ 0 Kz))
    _ = ((Icc (0 : ℤ) ⌊1 / σ⌋).card : ℝ) * ((floorBand σ 0 Kz).card : ℝ) := by
      rw [card_product, Nat.cast_mul]
    _ ≤ _ := mul_le_mul ht (floorBand_card hσ hKz) (by positivity) (by positivity)

open scoped Classical in
/-- Choose a representative inside the original bounded rectangle whenever a base
cell meets it. This avoids evaluating a quadratic beyond its original coordinate bounds. -/
def residualBaseRepresentative (σ Kz : ℝ) (z : Fin 2 → ℤ) : ℝ × ℝ :=
  if h : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ |p.2| ≤ Kz ∧
      (![⌊p.1 / σ⌋, ⌊p.2 / σ⌋] : Fin 2 → ℤ) = z then Classical.choose h else (0, 0)

theorem residualBaseRepresentative_spec {σ Kz t y : ℝ} {z : Fin 2 → ℤ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ Kz)
    (hz : (![⌊t / σ⌋, ⌊y / σ⌋] : Fin 2 → ℤ) = z) :
    (residualBaseRepresentative σ Kz z).1 ∈ Set.Icc (0 : ℝ) 1 ∧
      |(residualBaseRepresentative σ Kz z).2| ≤ Kz ∧
      (![⌊(residualBaseRepresentative σ Kz z).1 / σ⌋,
        ⌊(residualBaseRepresentative σ Kz z).2 / σ⌋] : Fin 2 → ℤ) = z := by
  have hex : ∃ p : ℝ × ℝ, p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ |p.2| ≤ Kz ∧
      (![⌊p.1 / σ⌋, ⌊p.2 / σ⌋] : Fin 2 → ℤ) = z := ⟨(t, y), ht, hy, hz⟩
  simp only [residualBaseRepresentative, dite_eq_left hex]
  exact Classical.choose_spec hex

def residualBaseValue (pc : Fin 6 → ℝ) (σ Kz : ℝ) (z : Fin 2 → ℤ) : ℝ :=
  quadZ pc (residualBaseRepresentative σ Kz z).1 (residualBaseRepresentative σ Kz z).2

theorem residualBaseValue_close {pc : Fin 6 → ℝ} {σ Kz H t y : ℝ} {z : Fin 2 → ℤ}
    (hσ : 0 < σ) (hKz : 0 ≤ Kz) (hH : 0 ≤ H) (hpc : ∀ e, |pc e| ≤ H)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ Kz)
    (hz : (![⌊t / σ⌋, ⌊y / σ⌋] : Fin 2 → ℤ) = z) :
    |quadZ pc t y - residualBaseValue pc σ Kz z| ≤ H * (5 + 3 * Kz) * σ := by
  obtain ⟨ht', hy', hz'⟩ := residualBaseRepresentative_spec ht hy hz
  have h0 : ⌊t / σ⌋ = ⌊(residualBaseRepresentative σ Kz z).1 / σ⌋ := by
    have h := congrFun (hz.trans hz'.symm) 0
    simpa using h
  have h1 : ⌊y / σ⌋ = ⌊(residualBaseRepresentative σ Kz z).2 / σ⌋ := by
    have h := congrFun (hz.trans hz'.symm) 1
    simpa using h
  apply residual_quad_variation hH hKz hσ.le hpc
    (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
    (abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩) hy hy'
  · exact Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq hσ h0
  · exact Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq hσ h1

/-- The possible residual bins for one predicted base value and one original offset bin. -/
def residualBinOptions (τv H value : ℝ) (o : ℤ) : Finset ℤ :=
  floorBand τv (value + ((o : ℝ) + 1 / 2) * τv) ((H + 3 / 2) * τv)

theorem residualBinOptions_card {τv H value : ℝ} (hτv : 0 < τv) (hH : 1 ≤ H) (o : ℤ) :
    ((residualBinOptions τv H value o).card : ℝ) ≤ 7 * H := by
  calc
    _ ≤ 2 * ((H + 3 / 2) * τv) / τv + 2 := floorBand_card hτv (by positivity)
    _ = 2 * H + 5 := by field_simp; ring
    _ ≤ _ := by linarith

theorem mem_residualBinOptions {τv H value Q D X : ℝ} {o : ℤ}
    (hτv : 0 < τv) (hfit : |X - Q - D| ≤ H * τv)
    (hbase : |Q - value| ≤ τv) (ho : ⌊D / τv⌋ = o) :
    ⌊X / τv⌋ ∈ residualBinOptions τv H value o := by
  have hD := Submission.Obl.k4_contact_affine_residual_candidate_transfer.abs_sub_center_of_floor
    hτv ho
  apply mem_floorBand hτv
  have hid : X - (value + ((o : ℝ) + 1 / 2) * τv) =
      (X - Q - D) + (Q - value) + (D - ((o : ℝ) + 1 / 2) * τv) := by ring
  rw [hid]
  calc
    _ ≤ |X - Q - D| + |Q - value| + |D - ((o : ℝ) + 1 / 2) * τv| := abs_add_three _ _ _
    _ ≤ H * τv + τv + τv / 2 := by
      apply add_le_add (add_le_add hfit hbase)
      simpa only [mul_comm τv] using hD
    _ = _ := by ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
