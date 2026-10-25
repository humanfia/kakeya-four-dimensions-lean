import Submission.Obl.k4_remainder_pure_profile_normalization.Glue
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Main

namespace Submission.Obl.k4_raw_critical_segment_forests.PureAssembly

open MeasureTheory Filter Set
open Submission.Obl.k4_remainder_pure_profile_normalization

noncomputable section

/-- Apply the accepted analytic estimates to supplied ratio samples, retaining
the given parent sequence and recording the resulting terminal profile. -/
theorem pure_remainder_from_samples {p : Data} (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hcap0 : 0 < cap) (hcap1 : cap < 1)
    (hcap : ∀ x : ℝ, r ≤ x → x ≤ p.L → p.f p.L - p.f x ≤ cap * (p.L - x)) :
    ∃ (ψ : ℕ → ℕ) (hψ : StrictMono ψ),
      ∃ v : PureRemainder (t.samples.sequence.reindex ψ hψ) cap,
        v.f (p.L - r) = p.f p.L - t.exponent := by
  let raw := t.samples.rawData hp cap
  have hN : ∀ k, 2 ≤ raw.N k := fun k => hp.1 _
  have hN1 : ∀ k, 1 ≤ raw.N k := fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)
  have hNt : Tendsto raw.N atTop atTop := hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop
  have hL : 0 < raw.L := sub_pos.mpr hrL
  obtain ⟨u⟩ := MultiHomog.pureHomogenization raw hN hNt
    (t.samples.rawData_subpower hp cap) hL
    ⟨t.samples.formatM, t.samples.formatD, t.samples.rawData_samples hp cap⟩
  let q := u.selection.data
  have hqN : ∀ k, 2 ≤ q.N k := fun k => hN (u.selection.index k)
  have hqN1 : ∀ k, 1 ≤ q.N k := fun k => hN1 (u.selection.index k)
  have hqt : Tendsto q.N atTop atTop := hNt.comp u.selection.strictMono.tendsto_atTop
  have hmass := q.not_powerSmall_mass hqN1 hqt u.subpower u.samples
  have hrawMass (k : ℕ) :
      (∑ b, ENNReal.ofReal (raw.ω k b) * raw.incidenceMeasure k b univ) ≤ 1 :=
    (t.samples.rawData_samples hp cap k).weighted_mass_le_one
  have hmeas (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ raw.L) :
      ∀ k b, Measurable (q.g k b x) := fun k b => (u.pure_law k b x hx hxL).1
  have hterminal := u.typicalAt_of_source hN1 hNt hrawMass hL.le le_rfl
    (fun k b => t.samples.rawData_pure_law hp cap hr k b (p.L - r) hL.le le_rfl)
    (t.rawData_terminal_typical hp cap hr hrL.le)
  have hvalue : u.selection.f (p.L - r) = p.f p.L - t.exponent :=
    k4_scalar_grid_density_extension.typical_exponent_unique
      q.N hqN hqt q.sampleMeasure (q.sampledDensity (p.L - r)) hmass
      (q.hasTypicalDensity_of_typicalAt (hmeas _ hL.le le_rfl) (u.typical _ hL.le le_rfl))
      (q.hasTypicalDensity_of_typicalAt (hmeas _ hL.le le_rfl) hterminal)
  have hcompare (x : ℝ) (hx : 0 ≤ x) (hxL : x ≤ p.L - r) :
      p.f (r + x) - t.exponent ≤ u.selection.f x := by
    have hupper := u.upperAt_of_source hx hxL
      (fun k b => t.samples.rawData_pure_law hp cap hr k b x hx hxL)
      (t.rawData_upper_tail hp cap hr hx hxL)
    exact typical_exponent_ge_of_upper q.N hqN hqt q.sampleMeasure (q.sampledDensity x)
      hmass (q.hasTypicalDensity_of_typicalAt (hmeas x hx hxL) (u.typical x hx hxL))
      (q.tagged_upper_of_upperAt (hmeas x hx hxL) hupper)
  have hqc := cap_of_shifted_profile_comparison hvalue hcompare hcap
  have hqvalid : q.PureValid := pureValid_of_samples hqN hqt u.subpower hL hcap0 hcap1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 u.samples
    ⟨u.pure_law, u.joint_law, u.increments, fun x τ hx hxL hτ => u.typical x hx hxL τ hτ, hqc⟩
  let s := t.samples.sequence.reindex u.selection.index u.selection.strictMono
  have hcal : ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, ∀ b,
      p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q b).det| ≤
        p.N (s.index k) ^ e *
          (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal *
          p.N (s.index k) ^ (-u.selection.f (p.L - r)) := by
    intro e he
    filter_upwards [u.selection.strictMono.tendsto_atTop.eventually (t.ratios e he)] with k hk b
    exact terminal_floor_of_ratio
      (by
        change 0 < p.N (t.samples.sequence.index (u.selection.index k))
        linarith [hp.1 (t.samples.sequence.index (u.selection.index k))])
      (t.samples.prior_pos hp (u.selection.index k) b) hvalue (hk b).2
  exact ⟨u.selection.index, u.selection.strictMono,
    ⟨u.selection.K, u.selection.E, u.selection.f, u.selection.g, u.selection.G,
      hqvalid, u.event_subset, fun k b => t.samples.prior_pos hp (u.selection.index k) b,
      s.normalizer_subpower hp, hcal⟩, hvalue⟩

end
end Submission.Obl.k4_raw_critical_segment_forests.PureAssembly
