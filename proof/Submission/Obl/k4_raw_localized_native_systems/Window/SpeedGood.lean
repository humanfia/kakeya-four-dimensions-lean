import Submission.Obl.k4_raw_localized_native_systems.Window.RawBounds
import Submission.Obl.k4_profile_density_bounds.Support

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A common original-law event giving the pointwise speed bound used by
the inverse and full-mass packing estimates. -/
def speedGood (K : ℝ) : Set Point := {q | ‖v q.1‖ ≤ K}

theorem measurableSet_speedGood (K : ℝ) : MeasurableSet (speedGood K) := by
  exact measurableSet_le
    ((k4_profile_density_bounds.measurable_velocity.comp measurable_fst).norm)
    measurable_const

theorem ae_speedGood {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {K : ℝ} (hK : p.K k ≤ K) : ∀ᵐ q ∂selected p k γ, q ∈ speedGood K := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  rcases (hfmt k).2.2.2.1 γ with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hwhole, _⟩
  have hv : ∀ᵐ l ∂p.ν k γ, ‖v l‖ ≤ K := by
    filter_upwards [hwhole] with l hl
    have hy := (hl 0 (by simp)).1
    exact (le_add_of_nonneg_left (norm_nonneg (y l 0))).trans (hy.trans hK)
  exact k4_profile_density_bounds.ae_velocity_bound (p.ν k γ) hv (p.E k γ)

theorem speedGood_compl_null {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {K : ℝ} (hK : p.K k ≤ K) : selected p k γ (speedGood K)ᶜ = 0 := by
  exact ae_iff.mp (ae_speedGood hp k γ hK)

/-- Adding the pointwise speed event to a common analytical mask costs no mass. -/
theorem speedGood_inter_loss {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {K : ℝ} (hK : p.K k ≤ K) (Good : Set Point) :
    selected p k γ (Good ∩ speedGood K)ᶜ = selected p k γ Goodᶜ := by
  rw [compl_inter]
  apply le_antisymm
  · exact (measure_union_le _ _).trans (by rw [speedGood_compl_null hp k γ hK, add_zero])
  · exact measure_mono subset_union_left

end
end Submission.Obl.k4_raw_localized_native_systems.Window
