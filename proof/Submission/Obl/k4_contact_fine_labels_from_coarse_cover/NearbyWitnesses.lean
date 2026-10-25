-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/NearbyWitnesses.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelDiameter
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelWitnesses

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Three original full-time native trajectories near almost every original
base point. The quantitative perturbation is the diameter of a deep true label. -/
def NearbyVelocities (k : ℕ) (t v : ℝ) : Prop :=
  ∀ᵐ u ∂p.μ k, p.GoodPoint k u ∧ ∃ w : Fin 3 → α × ℝ,
    (∀ e, p.GoodPoint k (w e) ∧
      ‖p.base k (w e) - p.base k u‖ ≤ 6 * p.K k ^ 2 * p.q k t) ∧
    ∀ e e', e ≠ e' → p.N k ^ (-v) < |p.b k (w e).1 3 - p.b k (w e').1 3|

theorem eventually_nearby_velocities (hp : p.Valid) {t v : ℝ}
    (ht : 0 < t) (htU : t ≤ p.U) (hv : 0 < v) :
    ∀ᶠ k in atTop, p.NearbyVelocities k t v := by
  let R : ℝ := 2 + t⁻¹
  have htip : 0 < t⁻¹ := inv_pos.mpr ht
  have hR : 1 < R := by dsimp [R]; linarith
  have htR : R⁻¹ ≤ t := by
    have hle : t⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le htip hle
  filter_upwards [hp.labels R hR, eventually_label_velocities p hp ht htU hv]
    with k hlabels hvel
  obtain ⟨_, _, hAB, _, hOne, hcover, _⟩ := hlabels t htR htU
  filter_upwards [hcover, Valid.ae_good p hp k] with u hu hgood
  obtain ⟨i, hui, hut⟩ := hu
  obtain ⟨w₀, hw₀, w₁, hw₁, w₂, hw₂, h01, h02, h12⟩ :=
    hvel i (p.Good k) (Valid.ae_good p hp k)
  let w : Fin 3 → α × ℝ := ![w₀, w₁, w₂]
  have hmem : ∀ e, w e ∈ (p.B k t i ×ˢ p.I k t i) ∩ p.Good k := by
    intro e
    fin_cases e <;> simp only [w]
    · exact hw₀
    · exact hw₁
    · exact hw₂
  refine ⟨hgood, w, ?_, ?_⟩
  · intro e
    refine ⟨(hmem e).2, ?_⟩
    exact label_base_diameter p hp ht.le (hOne i) (hAB i).2.2 (hmem e).1 ⟨hui, hut⟩
  · intro e e' hne
    fin_cases e <;> fin_cases e'
    all_goals first
      | exact (hne rfl).elim
      | simpa [w, abs_sub_comm] using h01
      | simpa [w, abs_sub_comm] using h02
      | simpa [w, abs_sub_comm] using h12

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
