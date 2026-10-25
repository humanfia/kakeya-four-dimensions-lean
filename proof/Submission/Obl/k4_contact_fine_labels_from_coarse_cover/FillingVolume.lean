-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/FillingVolume.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Equal-rate transverse width converts the full original true-label
reference into its natural four-dimensional box scale. -/
theorem label_reference_q_four (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i)
    (hqg : p.q k s ≤ p.K k * p.g k s) :
    ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 4 / p.K k ^ 2) ≤
      ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i) := by
  have hK := Valid.K_pos p hp k
  have hq := p.q_pos k s
  have ha := Valid.a_pos p hp k s
  have hwidth : p.q k s / p.K k ≤ p.g k s := (div_le_iff₀ hK).mpr (by nlinarith)
  have hreal : p.a k s ^ p.d * p.q k s ^ 4 / p.K k ^ 2 ≤
      p.q k s * (p.a k s ^ p.d * p.q k s ^ 2 * p.g k s / p.K k) := by
    calc
      _ = p.q k s * (p.a k s ^ p.d * p.q k s ^ 2 *
          (p.q k s / p.K k) / p.K k) := by field_simp <;> ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ENNReal.ofReal (p.q k s *
        (p.a k s ^ p.d * p.q k s ^ 2 * p.g k s / p.K k)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (p.q k s) *
        ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 2 * p.g k s / p.K k) :=
      ENNReal.ofReal_mul hq.le
    _ ≤ _ := mul_le_mul le_rfl hi.1 bot_le bot_le

/-- The recovered fine density cancels the original hidden-width factor.
No restricted assignment prior enters the resulting volume floor. -/
theorem filling_volume_of_original_reference (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i)
    (hqg : p.q k s ≤ p.K k * p.g k s) {τ : ℝ} (hτ : 0 ≤ τ)
    (m V : ENNReal)
    (hlow : ENNReal.ofReal τ * (ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) ≤ m)
    (hhigh : m ≤ ENNReal.ofReal (27 * (320 * p.K k ^ 4 * p.a k s ^ p.d)) * V) :
    ENNReal.ofReal ((τ / (8640 * p.K k ^ 6)) * p.q k s ^ 4) ≤ V := by
  have hK := Valid.K_pos p hp k
  have ha := Valid.a_pos p hp k s
  have har : 0 < p.a k s ^ p.d := Real.rpow_pos_of_pos ha _
  have hD : 0 < 27 * (320 * p.K k ^ 4 * p.a k s ^ p.d) := by positivity
  have hmass : ENNReal.ofReal τ *
      ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 4 / p.K k ^ 2) ≤ m :=
    (mul_le_mul le_rfl (label_reference_q_four p hp hi hqg) bot_le bot_le).trans hlow
  have heq : ENNReal.ofReal (27 * (320 * p.K k ^ 4 * p.a k s ^ p.d)) *
      ENNReal.ofReal ((τ / (8640 * p.K k ^ 6)) * p.q k s ^ 4) =
      ENNReal.ofReal τ * ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 4 / p.K k ^ 2) := by
    rw [← ENNReal.ofReal_mul hD.le, ← ENNReal.ofReal_mul hτ]
    congr 1
    field_simp
    <;> ring
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hD).ne' ENNReal.ofReal_ne_top).mp
  rw [heq]
  exact hmass.trans hhigh

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
