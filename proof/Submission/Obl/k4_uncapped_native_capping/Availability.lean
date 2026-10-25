/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/Availability.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.PacketPruning
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity
import Submission.Obl.k4_quadratic_finite_greedy_cover.PathFacts
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

theorem PacketData.Geometry.mono_loss
    {W : ℕ} {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss loss' h : ℝ}
    (hp : p.Geometry N K ω ν E P B M D loss h)
    (hN : 1 ≤ N) (hB : ∀ a, 0 ≤ B a) (hle : loss ≤ loss') :
    p.Geometry N K ω ν E P B M D loss' h := by
  have hpow : N ^ loss ≤ N ^ loss' := Real.rpow_le_rpow_of_exponent_le hN hle
  refine ⟨hp.ambient.trans hpow, hp.time.trans ?_, hp.count, hp.separated,
    fun w o => (hp.list_bound w o).trans hpow, hp.list_measurable, ?_,
    hp.coordinates, hp.budget_sum⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · intro a
    exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
      hN le_rfl le_rfl (Real.rpow_pos_of_pos (by linarith) _) hpow
      (hB _) (hp.charts a) id

/-- The exact problem and format precede every actual geometric loss.  Law
floors may still be removed by finite pruning. -/
def CappedPacketAvailable (ds kr S η s m U χ h t : ℝ) : Prop :=
  ∃ N K d W ω ν E P B f g G,
    prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧
      kr - t < H N K 1 W ω ν E B f ∧
    ∃ M D : ℕ, ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
      ∃ p : PacketData (W k),
        p.Geometry (N k) (K k) (ω k) (ν k) (E k) (P k) (B k) M D loss h ∧
        p.Analysis (N k) χ ds s m (S / 2) U (ω k) (ν k) (P k) (B k) ∧
        ENNReal.ofReal (N k ^ (-loss)) ≤ p.mass (ω k) (ν k)

def CappedAvailability (ds kr S η : ℝ) : Prop :=
  ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧
    ∀ χ h t : ℝ, 0 < χ → 0 < h → 0 < t →
      CappedPacketAvailable ds kr S η s m U χ h t

/-- Reserve actual geometric slack inside the same problem before deleting
light laws. This retains the fixed format and all outside quantifiers. -/
theorem CappedPacketAvailable.to_native
    {ds kr S η s m U χ h t : ℝ} (hχ : 0 < χ)
    (hp : CappedPacketAvailable ds kr S η s m U χ h t) :
    NativeSystemAvailable true ds kr S η s m U χ 1 h t := by
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd, hH, M, D, havail⟩ := hp
  obtain ⟨hN, hNt, _, _, _, _, hB, _⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic
      N K 1 d S η W ω ν E P B f g G hprob
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hprob, hd, hH,
    1, M, D, by norm_num, ?_⟩
  intro loss hloss
  let ρ : ℝ := min (loss / 2) (χ / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρloss : ρ < loss := (min_le_left _ _).trans_lt (by linarith)
  have hρχ : ρ < χ := (min_le_right _ _).trans_lt (by linarith)
  have hgap : ∀ᶠ k in atTop,
      ENNReal.ofReal (N k ^ (-loss)) + ENNReal.ofReal (N k ^ (-χ)) ≤
        ENNReal.ofReal (N k ^ (-ρ)) := by
    filter_upwards
      [Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (show -loss < -ρ by linarith) 2,
       Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
        (show -χ < -ρ by linarith) 2] with k hk₁ hk₂
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg (by linarith [hN k]) _)
      (Real.rpow_nonneg (by linarith [hN k]) _)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  apply ((havail ρ hρ).and_eventually hgap).mono
  rintro k ⟨⟨p, hg, ha, hmass⟩, hgapk⟩
  exact p.to_sample_of_mass_margin
    (hg.mono_loss (by linarith [hN k]) (fun a => (hB k a).le) hρloss.le)
    ha (hgapk.trans hmass)

theorem CappedAvailability.to_balanced
    {ds kr S η : ℝ} (hp : CappedAvailability ds kr S η) :
    BalancedAvailability ds kr S η := by
  obtain ⟨s, m, U, hs, hs₁, hsm, hU, hUm, hp⟩ := hp
  exact ⟨s, m, U, hs, hs₁, hsm, hU, hUm, fun χ h t hχ hh ht =>
    (hp χ h t hχ hh ht).to_native hχ⟩

end
end Submission.Obl.k4_uncapped_native_capping
