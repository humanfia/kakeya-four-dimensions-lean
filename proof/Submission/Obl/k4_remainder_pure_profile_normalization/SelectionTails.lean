import Submission.Obl.k4_remainder_pure_profile_normalization.HomogeneousSelection
import Submission.Obl.k4_remainder_pure_profile_normalization.DensitySelection
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit
import Submission.Obl.k4_native_grid_profile_extension.Profiles.DensityRefinement

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles

theorem HomogeneousSelection.upperAt_of_source {p : Data} (s : HomogeneousSelection p)
    {σ e : ℝ} (hσ : 0 ≤ σ) (hσL : σ ≤ p.L)
    (hsourceLaw : ∀ k b, Measurable (p.g k b σ) ∧
      (p.incidenceMeasure k b).map (obs (p.B k b) (δ (p.N k) σ)) =
        (volume.prod Measure.count).withDensity (p.g k b σ))
    (htail : p.UpperAt σ e) : s.selection.data.UpperAt σ e := by
  intro τ hτ
  apply ((htail τ hτ).comp s.selection.index s.selection.strictMono.tendsto_atTop).mono
  apply Eventually.of_forall
  intro k
  exact weighted_upper_tail_mono (volume.prod Measure.count)
    (p.incidenceMeasure (s.selection.index k)) (s.selection.data.incidenceMeasure k)
    (fun b => Measure.restrict_mono (s.event_subset k b) le_rfl)
    (fun b => obs (p.B (s.selection.index k) b) (δ (p.N (s.selection.index k)) σ))
    (fun _ => Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)
    (fun b => p.g (s.selection.index k) b σ) (fun b => s.selection.g k b σ)
    (fun b => (hsourceLaw _ b).1) (fun b => (s.pure_law k b σ hσ hσL).1)
    (fun b => (hsourceLaw _ b).2) (fun b => (s.pure_law k b σ hσ hσL).2)
    (fun b => ENNReal.ofReal (p.ω (s.selection.index k) b))
    (ENNReal.ofReal (p.N (s.selection.index k) ^ (-e + τ)))

theorem HomogeneousSelection.typicalAt_of_source {p : Data} (s : HomogeneousSelection p)
    (hN : ∀ k, 1 ≤ p.N k) (hNt : Tendsto p.N atTop atTop)
    (hmass : ∀ k, (∑ b, ENNReal.ofReal (p.ω k b) * p.incidenceMeasure k b univ) ≤ 1)
    {σ e : ℝ} (hσ : 0 ≤ σ) (hσL : σ ≤ p.L)
    (hsourceLaw : ∀ k b, Measurable (p.g k b σ) ∧
      (p.incidenceMeasure k b).map (obs (p.B k b) (δ (p.N k) σ)) =
        (volume.prod Measure.count).withDensity (p.g k b σ))
    (htail : p.TypicalAt σ e) : s.selection.data.TypicalAt σ e := by
  apply weighted_typical_of_domination s.selection.data.N
    (fun k => hN (s.selection.index k)) (hNt.comp s.selection.strictMono.tendsto_atTop)
    s.selection.data.W (volume.prod Measure.count)
    (fun k => p.incidenceMeasure (s.selection.index k)) s.selection.data.incidenceMeasure
    (fun k b => Measure.restrict_mono (s.event_subset k b) le_rfl)
    (fun k b => obs (p.B (s.selection.index k) b) (δ (p.N (s.selection.index k)) σ))
    (fun _ _ => Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)
    (fun k b => p.g (s.selection.index k) b σ) (fun k b => s.selection.g k b σ)
    (fun k b => (hsourceLaw _ b).1) (fun k b => (s.pure_law k b σ hσ hσL).1)
    (fun k b => (hsourceLaw _ b).2) (fun k b => (s.pure_law k b σ hσ hσL).2)
    (fun k b => ENNReal.ofReal (p.ω (s.selection.index k) b))
    (fun k => hmass (s.selection.index k)) e
  intro τ hτ
  exact (htail τ hτ).comp s.selection.index s.selection.strictMono.tendsto_atTop

/-- Coverage with a subpower slack rules out a power-small total selected law. -/
theorem Data.not_powerSmall_mass (p : Data) (hN : ∀ k, 1 ≤ p.N k)
    (ht : Tendsto p.N atTop atTop)
    (hK : (∀ k, 1 ≤ p.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, p.K k ≤ p.N k ^ ε)
    (hs : ∃ M D : ℕ, ∀ k, Normalization.SampleProblem (p.N k) (p.K k) M D
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)) :
    ¬ IsPowerSmall p.N (fun k => p.sampleMeasure k univ) := by
  obtain ⟨M, D, hs⟩ := hs
  apply not_isPowerSmall_of_inverse_subpower ht
  intro ε hε
  filter_upwards [hK.2 ε hε] with k hk
  have hlo : ENNReal.ofReal (p.K k)⁻¹ ≤ p.sampleMeasure k univ := by
    rw [p.sampleMeasure_univ k]
    simpa only [Data.incidenceMeasure, Measure.restrict_apply_univ] using (hs k).mass
  refine (ENNReal.ofReal_le_ofReal ?_).trans hlo
  rw [Real.rpow_neg (by linarith [hN k] : 0 ≤ p.N k)]
  exact inv_anti₀ (by linarith [hK.1 k]) hk

end Submission.Obl.k4_remainder_pure_profile_normalization
