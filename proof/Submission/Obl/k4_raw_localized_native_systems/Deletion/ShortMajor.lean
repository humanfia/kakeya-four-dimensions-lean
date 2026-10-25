import Submission.Obl.k4_raw_localized_native_systems.Deletion.UniformVelocity
import Submission.Obl.k4_raw_localized_native_systems.Packing.FramePowers
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_raw_localized_native_systems.Deletion

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

theorem velocity_near_center_of_short_major {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r lam : ℝ} {e : Fin W.C} (hW : Window.WChart p k W M D κ r e)
    (hκ : 0 ≤ κ) (hmajor : ‖longCol (W.Q e)‖ ≤ lam)
    {l : Line} (hl : l ∈ W.A e) :
    ‖v l - W.u e‖ ≤ 4 * κ * (2 : ℝ) ^ W.T * lam := by
  have heq : v l - W.u e = Matrix.toEuclideanLin (W.Q e)
      (Matrix.toEuclideanLin (W.Q e)⁻¹ (v l - W.u e)) :=
    (Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (W.Q e) hW.det_ne _).symm
  rw [heq]
  apply (norm_toEuclideanLin_le_longCol _ _).trans
  calc
    _ ≤ 2 * lam * (2 * κ * (2 : ℝ) ^ W.T) :=
      mul_le_mul (by linarith) (hW.velocity_inverse hl) (norm_nonneg _) (by
        have hlam : 0 ≤ lam := (norm_nonneg _).trans hmajor
        positivity)
    _ = _ := by ring

theorem velocity_diameter_of_short_major {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r lam : ℝ} {e : Fin W.C} (hW : Window.WChart p k W M D κ r e)
    (hκ : 0 ≤ κ) (hmajor : ‖longCol (W.Q e)‖ ≤ lam)
    {l l' : Line} (hl : l ∈ W.A e) (hl' : l' ∈ W.A e) :
    dist (v l) (v l') ≤ 8 * κ * (2 : ℝ) ^ W.T * lam := by
  calc
    _ ≤ dist (v l) (W.u e) + dist (W.u e) (v l') := dist_triangle _ _ _
    _ = ‖v l - W.u e‖ + ‖v l' - W.u e‖ := by
      rw [dist_eq_norm, dist_comm (W.u e), dist_eq_norm]
    _ ≤ 4 * κ * (2 : ℝ) ^ W.T * lam + 4 * κ * (2 : ℝ) ^ W.T * lam :=
      add_le_add (velocity_near_center_of_short_major hW hκ hmajor hl)
        (velocity_near_center_of_short_major hW hκ hmajor hl')
    _ = _ := by ring

/-- At every arbitrarily small positive major cutoff, the complete original
world-union mass of the removed earlier labels is power-small. Formats,
numbers of labels, depths, floors and block counts have no cost here. -/
theorem uniform_short_major_labels {p : Data} (hp : Valid p) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ p.η * p.L) :
    ∃ τ c : ℝ, 0 < τ ∧ τ ≤ u / 100 ∧ 0 < c ∧ ∀ᶠ k in atTop,
      ∀ (M D : ℕ) (κ r : ℝ) (W : Atlas p k), 0 ≤ κ → κ ≤ p.N k ^ τ →
        (∀ e, Window.WChart p k W M D κ r e) →
        (∀ γ e, MeasurableSet {o | e ∈ W.lst γ o}) →
        (∀ γ o, ((W.lst γ o).card : ℝ) ≤ κ) →
        (∀ e z, z ∈ W.F e → e ∈ W.lst (W.γ e)
          (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z)) →
        (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
          {z | ∃ e, W.γ e = γ ∧ z ∈ W.F e ∧
            ‖longCol (W.Q e)‖ < (1 / (2 : ℝ) ^ W.T) * p.N k ^ (-u)}) ≤
          ENNReal.ofReal (p.N k ^ (-c)) := by
  obtain ⟨τ, c, hτ, hτu, hc, hbound⟩ := uniform_small_velocity_labels hp
    (by positivity : 0 < u / 2) (by linarith : u / 2 ≤ p.η * p.L)
  have hthreshold := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.scale_tendsto (show -u + τ < -(u / 2) by linarith only [hu, hτu]) 8
  refine ⟨τ, c, hτ, by linarith only [hu, hτu], hc, ?_⟩
  filter_upwards [hbound, hthreshold] with k hk hthreshold
  intro M D κ r W hκ hκN hW hlist hcard hknown
  let F : Fin (p.W k) → Fin W.C → Set Point := fun γ e =>
    {z | W.γ e = γ ∧ z ∈ W.F e ∧
      ‖longCol (W.Q e)‖ < (1 / (2 : ℝ) ^ W.T) * p.N k ^ (-u)}
  have hFknown (γ : Fin (p.W k)) (e : Fin W.C) (z : Point) (hz : z ∈ F γ e) :
      e ∈ W.lst γ (obs (p.B k γ) (δ (p.N k) p.L) z) := by
    simpa only [hz.1] using hknown e z hz.2.1
  have hdiam (γ : Fin (p.W k)) (e : Fin W.C) (z : Point) (hz : z ∈ F γ e)
      (z' : Point) (hz' : z' ∈ F γ e) : dist (v z.1) (v z'.1) ≤ δ (p.N k) (u / 2) := by
    have hgeom := velocity_diameter_of_short_major (hW e) hκ hz.2.2.le
      ((hW e).sel hz.2.1).2.1 ((hW e).sel hz'.2.1).2.1
    apply hgeom.trans
    have hN := hp.scale_pos k
    calc
      _ = 8 * κ * p.N k ^ (-u) := by field_simp
      _ ≤ 8 * p.N k ^ τ * p.N k ^ (-u) := by gcongr
      _ = 8 * p.N k ^ (-u + τ) := by rw [mul_assoc, ← Real.rpow_add hN]; congr 2; ring
      _ ≤ p.N k ^ (-(u / 2)) := hthreshold.le
      _ ≤ δ (p.N k) (u / 2) :=
        (Submission.Obl.k4_profile_density_bounds.width_bounds hN (u / 2)).1
  have h := hk W.C κ F W.lst hκN hlist hcard hFknown hdiam
  simpa only [F, Set.ofPred_exists] using h

end
end Submission.Obl.k4_raw_localized_native_systems.Deletion
