-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelWitnesses.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.MeshVelocity

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open MeasureTheory Set Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Three actual velocities in every true label, outside any prescribed
original null exception, at an arbitrarily small fixed power separation. -/
def LabelVelocities (k : ℕ) (s v : ℝ) : Prop :=
  ∀ (i : Fin (p.n k s)) (G : Set (α × ℝ)), (∀ᵐ u ∂p.μ k, u ∈ G) →
    ∃ u₀ ∈ (p.B k s i ×ˢ p.I k s i) ∩ G,
      ∃ u₁ ∈ (p.B k s i ×ˢ p.I k s i) ∩ G,
        ∃ u₂ ∈ (p.B k s i ×ˢ p.I k s i) ∩ G,
          p.N k ^ (-v) < |p.b k u₀.1 3 - p.b k u₁.1 3| ∧
          p.N k ^ (-v) < |p.b k u₀.1 3 - p.b k u₂.1 3| ∧
          p.N k ^ (-v) < |p.b k u₁.1 3 - p.b k u₂.1 3|

theorem eventually_label_velocities (hp : p.Valid) {s v : ℝ}
    (hs : 0 < s) (hsU : s ≤ p.U) (hv : 0 < v) :
    ∀ᶠ k in atTop, p.LabelVelocities k s v := by
  let R : ℝ := 2 + s⁻¹ + v⁻¹ + v
  have hsip : 0 < s⁻¹ := inv_pos.mpr hs
  have hvip : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hsinv : s⁻¹ ≤ R := by dsimp [R]; linarith
  have hvinv : v⁻¹ ≤ R := by dsimp [R]; linarith
  have hsR : R⁻¹ ≤ s := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hs) hsinv
  have hvR : R⁻¹ ≤ v := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hv) hvinv
  have hvR' : v ≤ R := by dsimp [R]; linarith
  have hRinv : R⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hR.le
  have hsmall : ∀ᶠ k in atTop, 10 * p.K k ^ 2 * (p.K k * p.N k ^ (-p.S * v)) < 1 := by
    have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (fun k => (by linarith [hp.N_ge k] : 1 ≤ p.N k)) hp.N_lim hp.K_ge hp.K_sub 3
      (show -p.S * v < 0 by nlinarith [hp.S_pos]) (show (0 : ℝ) ≤ 10 by norm_num)
    filter_upwards [h] with k hk
    simpa only [Real.rpow_zero, show 10 * p.K k ^ 3 * p.N k ^ (-p.S * v) =
      10 * p.K k ^ 2 * (p.K k * p.N k ^ (-p.S * v)) by ring] using hk
  filter_upwards [hp.labels R hR, hp.caps R hR, hsmall] with k hlabels hcaps hsmall
  obtain ⟨_, _, _, _, hOne, _, hpalette⟩ := hlabels s hsR hsU
  obtain ⟨hπ, _, _⟩ := hcaps 1 0 v hRinv hR.le (by norm_num) hRpos.le hvR hvR'
  intro i G hG
  have : IsProbabilityMeasure (p.ν k) := (hp.basic k).2.1
  apply three_velocity_witnesses_of_assignment (p.μ k) (p.ν k) (p.π k)
    (p.A k s i) (p.B k s i) (p.I k s i) G (fun l => p.b k l 3)
    (Valid.K_pos p hp k) (p.q_pos k s) (Real.rpow_pos_of_pos (Valid.N_pos p hp k) _)
    (mul_nonneg (Valid.K_pos p hp k).le (Real.rpow_nonneg (Valid.N_pos p hp k).le _))
    (label_assignment_pos p hp (hOne i)).ne' (hOne i).2.2.1 ?_ hπ hG hsmall
  intro a
  simpa only [mem_prod, and_assoc] using hpalette i v a hvR hvR'

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
