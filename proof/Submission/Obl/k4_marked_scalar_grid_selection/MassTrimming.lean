import Submission.Obl.k4_tempered_grid_selection.SelectionMass
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set Filter
open scoped ENNReal

/-- Removing at most half the mass floor preserves a half-sized floor. -/
theorem half_mass_floor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) {K : ℝ} (hK : 0 < K)
    (hlower : ENNReal.ofReal K⁻¹ ≤ μ S)
    (hcover : μ S ≤ μ T + ENNReal.ofReal (2 * K)⁻¹) :
    ENNReal.ofReal (2 * K)⁻¹ ≤ μ T := by
  have hh : ENNReal.ofReal ((2 * K)⁻¹) + ENNReal.ofReal ((2 * K)⁻¹) ≤
      μ T + ENNReal.ofReal ((2 * K)⁻¹) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have heq : (2 * K)⁻¹ + (2 * K)⁻¹ = K⁻¹ := by ring
    rw [heq]
    exact hlower.trans hcover
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hh

/-- A power-small discard can be made at every sufficiently large scale,
while the finitely many other scales retain their original atoms. -/
theorem dense_active_sets {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : k4_tempered_grid_selection.Subpower N K)
    (μ : (k : ℕ) → Measure (Ω k)) (S T : (k : ℕ) → Set (Ω k))
    (hTS : ∀ k, T k ⊆ S k)
    (hlower : ∀ k, ENNReal.ofReal (K k)⁻¹ ≤ μ k (S k))
    (d : ℝ) (hd : 0 < d)
    (hdiscard : ∀ᶠ k in atTop,
      μ k (S k) ≤ μ k (T k) + ENNReal.ofReal (N k ^ (-d))) :
    k4_tempered_grid_selection.Subpower N (fun k => 2 * K k) ∧
    ∃ A : (k : ℕ) → Set (Ω k), (∀ k, A k ⊆ S k) ∧
      (∀ᶠ k in atTop, A k = T k) ∧
      ∀ k, ENNReal.ofReal (2 * K k)⁻¹ ≤ μ k (A k) := by
  classical
  have hsmall : ∀ᶠ k in atTop, N k ^ (-d) < (2 * K k)⁻¹ := by
    have hs := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      (fun k => by linarith [hN k]) hNt hK.1 hK.2 1
      (show -d < 0 by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
    filter_upwards [hs] with k hk
    simp only [pow_one, Real.rpow_zero] at hk
    have hpos : 0 < 2 * K k := by linarith [hK.1 k]
    simpa only [mul_one] using (lt_inv_mul_iff₀ hpos).2 hk
  have hgood : ∀ᶠ k in atTop,
      ENNReal.ofReal (2 * K k)⁻¹ ≤ μ k (T k) := by
    filter_upwards [hdiscard, hsmall] with k hk hs
    apply half_mass_floor (μ k) (S k) (T k) (by linarith [hK.1 k]) (hlower k)
    exact hk.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hs.le))
  let A (k : ℕ) : Set (Ω k) :=
    if ENNReal.ofReal (2 * K k)⁻¹ ≤ μ k (T k) then T k else S k
  refine ⟨?_, A, ?_, ?_, ?_⟩
  · exact k4_tempered_grid_selection.subpower_mul (fun k => by linarith [hN k])
      ⟨(fun _ => by norm_num), k4_discrete_of_terminal_charts.subpower_const hNt 2⟩ hK
  · intro k
    dsimp [A]
    split_ifs
    · exact hTS k
    · exact Subset.rfl
  · filter_upwards [hgood] with k hk
    exact if_pos hk
  · intro k
    dsimp [A]
    split_ifs with hk
    · exact hk
    · apply le_trans _ (hlower k)
      apply ENNReal.ofReal_le_ofReal
      exact inv_le_inv₀ (by linarith [hK.1 k]) (by linarith [hK.1 k]) |>.mpr
        (by linarith [hK.1 k])

end Submission.Obl.k4_marked_scalar_grid_selection
