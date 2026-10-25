import Mathlib
import ChallengeDeps
import Submission.Obl.k4_lifted_plank_cap_saturation.Bins
import Submission.Obl.k4_lifted_plank_cap_saturation.Exponents
import Submission.Obl.k4_lifted_plank_cap_saturation.Plank
set_option linter.unusedVariables false

/-!
# `Submission.k4_lifted_plank_cap_saturation`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_lifted_plank_cap_saturation`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_lifted_plank_cap_saturation/`
belong to this obligation.

The heavy lifted plank lies over the coefficient ball of radius `5 v` about
`plankCenter b₀ w`, with dummy fibers of length at most `8 u` (`lifted_plank_mass_le`).
The coefficient cap at radius `max p (5 v)` and the chosen power losses
(`lifted_saturation_exponents`) leave more mass in that ball than its ordinary
coefficient `p`-bins can carry below the target, so one bin is heavy
(`exists_heavy_coefficient_bin`).
-/

open Submission.Obl.k4_lifted_plank_cap_saturation in
theorem Submission.k4_lifted_plank_cap_saturation : ∀ d c ε : ℝ, 0 ≤ d → d < 1 → 0 < c → 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (G : Set α), Measurable a → MeasurableSet G → ν Set.univ ≤ ENNReal.ofReal (N ^ κ) → (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r → ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ κ * r ^ d)) → ∀ (b₀ w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (u v : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → N ^ (-c - κ) ≤ u → u ≤ v → v ≤ N ^ κ → ENNReal.ofReal (N ^ (-c * (d - 1) - κ) * u * v) ≤ (ν.prod (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) {z : α × ℝ | z.1 ∈ G ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ - t • w) e₁| ≤ u ∧ |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ - t • w) e₂| ≤ v} → ∃ q : Fin 3 → ℤ, ENNReal.ofReal (N ^ (-c * d - ε)) ≤ ν {l | (∀ j : Fin 3, ⌊a l j / (N ^ (-c))⌋ = q j) ∧ l ∈ G} := by
  intro d c ε hd0 hd1 hc hε
  obtain ⟨κ, hκ, N₀, hN₀, hexp⟩ := lifted_saturation_exponents hd0 hd1 hc hε
  refine ⟨κ, hκ, N₀, hN₀, ?_⟩
  intro N hN α _ ν a G ha hG hν hcap b₀ w e₁ e₂ u v he₁ he₂ he hu huv hvN hheavy
  have hN0 : 0 < N := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hu
  have hM1 := hheavy.trans
    (lifted_plank_mass_le ν a G ha hG b₀ w e₁ e₂ he₁ he₂ he hu0 huv)
  have hM2 : ν {l | a l ∈ Metric.ball (plankCenter b₀ w) (5 * v) ∧ l ∈ G} ≤
      ENNReal.ofReal (N ^ κ * (max (N ^ (-c)) (5 * v)) ^ d) :=
    (MeasureTheory.measure_mono (show
      {l | a l ∈ Metric.ball (plankCenter b₀ w) (5 * v) ∧ l ∈ G} ⊆
        {l | a l ∈ Metric.ball (plankCenter b₀ w) (max (N ^ (-c)) (5 * v))} from
      fun l hl => Metric.ball_subset_ball (le_max_right _ _) hl.1)).trans
      (hcap _ _ (le_max_left _ _))
  exact exists_heavy_coefficient_bin ν a G (plankCenter b₀ w)
    (by linarith [hu0.trans_le huv]) (Real.rpow_pos_of_pos hN0 _)
    (Real.rpow_nonneg hN0.le _) (hexp N hN u v hu huv _ hM1 hM2)
