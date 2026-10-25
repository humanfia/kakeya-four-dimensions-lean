-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelScales.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem q_bounds_of_resolution (hp : p.Valid) {k : ℕ} {s : ℝ}
    (hlo : p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s)
    (hhi : (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s)) :
    (p.K k)⁻¹ * p.N k ^ (-p.κ * s) ≤ p.q k s ∧
      p.q k s ≤ p.K k * p.N k ^ (-p.κ * s) := by
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have hscale : 0 < p.N k ^ (p.κ * s) := Real.rpow_pos_of_pos hN _
  rw [p.q_eq_inv]
  constructor
  · have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ p.T k s) hhi
    simpa only [one_div, mul_inv_rev, Real.rpow_neg hN.le,
      show -p.κ * s = -(p.κ * s) by ring, mul_comm] using h
  · have h := one_div_le_one_div_of_le (div_pos hscale hK) hlo
    rw [one_div_div] at h
    simpa only [one_div, Real.rpow_neg hN.le, div_eq_mul_inv,
      show -p.κ * s = -(p.κ * s) by ring, one_mul] using h

theorem equal_rate_width_bounds (hp : p.Valid) {k : ℕ} {s : ℝ}
    (hlo : p.N k ^ (p.κ * s) / p.K k ≤ (2 : ℝ) ^ p.T k s)
    (hhi : (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s)) :
    p.g k s ≤ p.K k * p.q k s ∧ p.q k s ≤ p.K k * p.g k s := by
  obtain ⟨hlo', hhi'⟩ := q_bounds_of_resolution p hp hlo hhi
  have hg : p.g k s = p.N k ^ (-p.κ * s) := by rw [g, hp.equal_rate]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo' (Valid.K_pos p hp k).le
    simpa only [← mul_assoc, mul_inv_cancel₀ (Valid.K_pos p hp k).ne', one_mul, ← hg] using h
  · simpa only [← hg] using hhi'

theorem a_rpow_eq (hp : p.Valid) (k : ℕ) (s : ℝ) :
    p.a k s ^ p.d = p.N k ^ (-p.d * s) := by
  rw [a, ← Real.rpow_mul (Valid.N_pos p hp k).le]
  congr 1
  ring

/-- The original incidence reference has a fixed-power floor in a shallow
depth, with only the original subpower budget as its prefactor. -/
theorem label_reference_floor (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i)
    (hhi : (2 : ℝ) ^ p.T k s ≤ p.K k * p.N k ^ (p.κ * s)) :
    ENNReal.ofReal ((p.K k)⁻¹ ^ (4 : ℕ) * p.N k ^ (-(p.d + 4 * p.κ) * s)) ≤
      ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i) := by
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have hq : 0 < p.q k s := p.q_pos k s
  have hg : p.g k s = p.N k ^ (-p.κ * s) := by rw [g, hp.equal_rate]
  have hlow : (p.K k)⁻¹ * p.g k s ≤ p.q k s := by
    rw [hg, p.q_eq_inv]
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ p.T k s) hhi
    simpa only [one_div, mul_inv_rev, Real.rpow_neg hN.le,
      show -p.κ * s = -(p.κ * s) by ring, mul_comm] using h
  have ha : 0 ≤ p.a k s ^ p.d := Real.rpow_nonneg (Valid.a_pos p hp k s).le _
  have hgpos : 0 < p.g k s := Valid.g_pos p hp k s
  have hpower : p.a k s ^ p.d * p.g k s ^ (4 : ℕ) =
      p.N k ^ (-(p.d + 4 * p.κ) * s) := by
    rw [a_rpow_eq p hp, hg, ← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ENNReal.ofReal ((p.K k)⁻¹ ^ (4 : ℕ) * (p.a k s ^ p.d * p.g k s ^ (4 : ℕ))) := by
      rw [hpower]
    _ = ENNReal.ofReal (p.a k s ^ p.d * ((p.K k)⁻¹ * p.g k s) ^ 3 *
        p.g k s / p.K k) := by
      congr 1
      rw [div_eq_mul_inv]
      ring
    _ ≤ ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 3 * p.g k s / p.K k) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ = ENNReal.ofReal (p.q k s) *
        ENNReal.ofReal (p.a k s ^ p.d * p.q k s ^ 2 * p.g k s / p.K k) := by
      rw [← ENNReal.ofReal_mul hq.le]
      congr 1
      ring
    _ ≤ _ := mul_le_mul le_rfl hi.1 bot_le bot_le

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
