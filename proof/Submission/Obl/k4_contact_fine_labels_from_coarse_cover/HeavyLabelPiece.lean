-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HeavyLabelPiece.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HeavyPiece
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Every original true label has a heavy intersection with one member of
an original coarse palette. There is no need to discard any true label. -/
theorem exists_heavy_label_piece (hp : p.Valid) {k : ℕ} {s : ℝ}
    {i : Fin (p.n k s)} (hi : p.Label k s i) {M : ℕ} {H : ℝ}
    (hH : 0 < H) (hM : (M : ℝ) ≤ H) (D : Fin M → Set (α × ℝ))
    (hD : ∀ᵐ u ∂p.μ k, ∃ a, u ∈ D a)
    (G : Set (α × ℝ)) (hG : ∀ᵐ u ∂p.μ k, u ∈ G) :
    ∃ a : Fin M, ENNReal.ofReal (1 / (2 * p.K k * H)) *
        (ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)) ≤
      p.μ k (((p.B k s i ×ˢ p.I k s i) ∩ G) ∩ D a) := by
  have : IsProbabilityMeasure (p.ν k) := (hp.basic k).2.1
  have hK := Valid.K_pos p hp k
  have hq := p.q_pos k s
  let w : ENNReal := ENNReal.ofReal (p.q k s) * p.ν k (p.A k s i)
  have hw0 : w ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne'
    (label_assignment_pos p hp hi).ne'
  have hwtop : w ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hscalar : (M : ℝ) * (1 / (2 * p.K k * H)) ≤ 1 / (2 * p.K k) := by
    calc
      _ = (M : ℝ) / (2 * p.K k * H) := by ring
      _ ≤ H / (2 * p.K k * H) := div_le_div_of_nonneg_right hM (by positivity)
      _ = _ := by field_simp
  have hcard : (M : ENNReal) * (ENNReal.ofReal (1 / (2 * p.K k * H)) * w) ≤
      ENNReal.ofReal (1 / (2 * p.K k)) * w := by
    rw [← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg M)]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal hscalar) le_rfl bot_le bot_le
  have hcoeff : ENNReal.ofReal (1 / (2 * p.K k)) < ENNReal.ofReal ((p.K k)⁻¹) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hK)).mpr
    simpa only [one_div] using div_lt_div_of_pos_left zero_lt_one hK
      (show p.K k < 2 * p.K k by linarith)
  have hlt : ENNReal.ofReal (1 / (2 * p.K k)) * w < ENNReal.ofReal ((p.K k)⁻¹) * w :=
    ENNReal.mul_lt_mul_left hw0 hwtop hcoeff
  have hfloor : ENNReal.ofReal ((p.K k)⁻¹) * w ≤ p.μ k (p.B k s i ×ˢ p.I k s i) := by
    have heq : ENNReal.ofReal ((p.K k)⁻¹) * w =
        ENNReal.ofReal (p.q k s / p.K k) * p.ν k (p.A k s i) := by
      dsimp [w]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hK).le]
      congr 1
      ring
    rw [heq]
    exact hi.2.2.1
  apply exists_heavy_cover_piece (p.μ k) ((p.B k s i ×ˢ p.I k s i) ∩ G) D
    (ENNReal.ofReal (1 / (2 * p.K k * H)) * w)
    (hD.mono (fun _ hu _ => hu))
  simp only [Fintype.card_fin]
  rw [measure_inter_conull (ae_iff.mp hG)]
  exact (hcard.trans_lt hlt).trans_le hfloor

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
