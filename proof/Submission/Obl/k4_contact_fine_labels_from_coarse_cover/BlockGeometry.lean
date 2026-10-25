-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/BlockGeometry.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBounds
import Submission.Obl.k4_horizon_chart_assembly.ParameterScales

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set

variable {α : Type*} [MeasurableSpace α] (p : Model α)

noncomputable def blockStart (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : ℝ :=
  (p.j k s i : ℝ) * p.q k s

theorem I_eq_block (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    p.I k s i = Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s) := by
  simp only [I, timeBlock, blockStart, q_eq_inv, div_eq_mul_inv, add_mul, one_mul]

theorem block_geometry (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) :
    p.blockStart k s i ∈ Icc (0 : ℝ) 1 ∧ p.q k s ≤ 1 := by
  have hgeo := Submission.Obl.k4_horizon_chart_assembly.dyadic_block_geometry
    (p.T k s) (p.j k s i)
  have hstart : p.blockStart k s i ∈ Icc (0 : ℝ) 1 := by
    simpa only [blockStart, q_eq_inv] using hgeo.1
  have hsub : Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s) ⊆ Icc (0 : ℝ) 1 := by
    simpa only [blockStart, q_eq_inv] using hgeo.2.1
  have hend := hsub (show p.blockStart k s i + p.q k s ∈
    Icc (p.blockStart k s i) (p.blockStart k s i + p.q k s) from
      ⟨le_add_of_nonneg_right (p.q_pos k s).le, le_rfl⟩)
  exact ⟨hstart, by linarith [hstart.1, hend.2]⟩

/-- Excluding the original dyadic endpoints puts every retained label
incidence in its exact half-open time block. -/
theorem time_mem_Ico_of_away {k : ℕ} {s : ℝ} {i : Fin (p.n k s)} {t : ℝ}
    (ht : t ∈ p.I k s i)
    (haway : ∀ a : ℤ, t ≠ (a : ℝ) / (2 : ℝ) ^ p.T k s) :
    t ∈ Ico (p.blockStart k s i) (p.blockStart k s i + p.q k s) := by
  rw [I_eq_block] at ht
  have hend : p.blockStart k s i + p.q k s =
      ((p.j k s i : ℝ) + 1) / (2 : ℝ) ^ p.T k s := by
    simp only [blockStart, q_eq_inv, div_eq_mul_inv, add_mul, one_mul]
  have hne : t ≠ p.blockStart k s i + p.q k s := by
    rw [hend]
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      haway (((p.j k s i : ℕ) : ℤ) + 1)
  exact ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
