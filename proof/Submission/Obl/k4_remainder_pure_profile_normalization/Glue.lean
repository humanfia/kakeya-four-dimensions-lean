import Submission.Obl.k4_remainder_pure_profile_normalization.SelectionTails
import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizedAsymptotics
import Submission.Obl.k4_remainder_pure_profile_normalization.ProfileComparison
import Submission.Obl.k4_remainder_pure_profile_normalization.Interface

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Pure homogenization, applied to the actual normalized chart worlds, supplies
the full pure remainder certificate with the original local endpoint cap. -/
theorem pureNormalization_of_homogenization (H : PureHomogenization) : PureNormalization := by
  classical
  intro p hp r h cap hr hrL hc hc1 hcap hk
  obtain ⟨t⟩ := hk.exists_ratio_samples hp hr
  let q := t.samples.rawData hp cap
  have hNq : ∀ k, 2 ≤ q.N k := fun k => hp.1 _
  have htq : Tendsto q.N atTop atTop := hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop
  have hLq : 0 < q.L := sub_pos.mpr hrL
  have hsampleq : ∃ M D : ℕ, ∀ k, Normalization.SampleProblem (q.N k) (q.K k) M D
      (q.W k) (q.ω k) (q.ν k) (q.E k) (q.P k) (q.B k) :=
    ⟨t.samples.formatM, t.samples.formatD, t.samples.rawData_samples hp cap⟩
  obtain ⟨u⟩ := H q hNq htq (t.samples.rawData_subpower hp cap) hLq hsampleq
  let q₂ := u.selection.data
  have hN₂ : ∀ k, 2 ≤ q₂.N k := fun k => hNq (u.selection.index k)
  have hN₁ : ∀ k, 1 ≤ q₂.N k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN₂ k)
  have ht₂ : Tendsto q₂.N atTop atTop := htq.comp u.selection.strictMono.tendsto_atTop
  have hmass := q₂.not_powerSmall_mass hN₁ ht₂ u.subpower u.samples
  have hrawMass (k : ℕ) : (∑ b, ENNReal.ofReal (q.ω k b) * q.incidenceMeasure k b univ) ≤ 1 :=
    (t.samples.rawData_samples hp cap k).weighted_mass_le_one
  have hg₂ (σ : ℝ) (hσ : 0 ≤ σ) (hσL : σ ≤ q.L) :
      ∀ k b, Measurable (q₂.g k b σ) := fun k b => (u.pure_law k b σ hσ hσL).1
  have hterminal₀ : q₂.TypicalAt (p.L - r) (p.f p.L - t.exponent) :=
    u.typicalAt_of_source (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hNq k)) htq hrawMass
      hLq.le le_rfl (fun k b => t.samples.rawData_pure_law hp cap hr k b (p.L - r) hLq.le le_rfl)
      (t.rawData_terminal_typical hp cap hr hrL.le)
  have hterminal : u.selection.f (p.L - r) = p.f p.L - t.exponent :=
    Submission.Obl.k4_scalar_grid_density_extension.typical_exponent_unique
      q₂.N hN₂ ht₂ q₂.sampleMeasure (q₂.sampledDensity (p.L - r)) hmass
      (q₂.hasTypicalDensity_of_typicalAt (hg₂ _ hLq.le le_rfl) (u.typical _ hLq.le le_rfl))
      (q₂.hasTypicalDensity_of_typicalAt (hg₂ _ hLq.le le_rfl) hterminal₀)
  have hintermediate (σ : ℝ) (hσ : 0 ≤ σ) (hσL : σ ≤ p.L - r) :
      p.f (r + σ) - t.exponent ≤ u.selection.f σ := by
    have hu : q₂.UpperAt σ (p.f (r + σ) - t.exponent) :=
      u.upperAt_of_source hσ hσL
        (fun k b => t.samples.rawData_pure_law hp cap hr k b σ hσ hσL)
        (t.rawData_upper_tail hp cap hr hσ hσL)
    exact typical_exponent_ge_of_upper q₂.N hN₂ ht₂ q₂.sampleMeasure (q₂.sampledDensity σ)
      hmass (q₂.hasTypicalDensity_of_typicalAt (hg₂ σ hσ hσL) (u.typical σ hσ hσL))
      (q₂.tagged_upper_of_upperAt (hg₂ σ hσ hσL) hu)
  have hcap₂ := cap_of_shifted_profile_comparison hterminal hintermediate hcap
  have hvalid : q₂.PureValid := pureValid_of_samples hN₂ ht₂ u.subpower hLq hc hc1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 u.samples
    ⟨u.pure_law, u.joint_law, u.increments,
      (fun σ τ hσ hσL hτ => u.typical σ hσ hσL τ hτ), hcap₂⟩
  let s := t.samples.sequence.reindex u.selection.index u.selection.strictMono
  refine ⟨t.samples.atlasM, t.samples.atlasD, s, ⟨{
    K := u.selection.K
    E := u.selection.E
    f := u.selection.f
    g := u.selection.g
    G := u.selection.G
    valid := hvalid
    event_subset := u.event_subset
    prior_positive := fun k b => t.samples.prior_pos hp (u.selection.index k) b
    normalizer_subpower := s.normalizer_subpower hp
    terminal_comparison := ?_ }⟩⟩
  intro ε hε
  filter_upwards [u.selection.strictMono.tendsto_atTop.eventually (t.ratios ε hε)] with k hk b
  exact terminal_floor_of_ratio
    (by change 0 < p.N (t.samples.sequence.index (u.selection.index k));
        linarith [hp.1 (t.samples.sequence.index (u.selection.index k))])
    (t.samples.prior_pos hp (u.selection.index k) b) hterminal (hk b).2

theorem statement_of_homogenization (H : PureHomogenization) : Statement :=
  statement_of_construction (pureNormalization_of_homogenization H)

end Submission.Obl.k4_remainder_pure_profile_normalization
