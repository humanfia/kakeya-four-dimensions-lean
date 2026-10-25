/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/BalancedNormalization.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Glue
import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Main
import Submission.Obl.k4_remainder_angular_cap_transport.Assemble

/-! The exact endpoint calibration retained by the actual normalized worlds.
This strengthens the exported normalization certificate for the mass-to-area
cancellation in Section 10 without bounding an absolute density exponent. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace BalancedNormalization

open MeasureTheory Filter Set

open Submission.Obl.k4_remainder_pure_profile_normalization

/-- Homogenization of the actual normalized worlds preserves the terminal
exponent supplied by their original known-label density law. -/
theorem terminal_exponent
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data}
    (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (u : HomogeneousSelection (t.samples.rawData hp cap)) :
    u.selection.f (p.L - r) = p.f p.L - t.exponent := by
  let q := t.samples.rawData hp cap
  let q₂ := u.selection.data
  have hN (k : ℕ) : 2 ≤ q.N k := hp.1 _
  have ht : Tendsto q.N atTop atTop :=
    hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop
  have hL : 0 < q.L := sub_pos.mpr hrL
  have hN₂ (k : ℕ) : 2 ≤ q₂.N k := hN (u.selection.index k)
  have ht₂ : Tendsto q₂.N atTop atTop := ht.comp u.selection.strictMono.tendsto_atTop
  have hg₂ (k : ℕ) (b : Fin (q₂.W k)) :
      Measurable (q₂.g k b (p.L - r)) := (u.pure_law k b _ hL.le le_rfl).1
  have hmass := q₂.not_powerSmall_mass
    (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN₂ k)) ht₂ u.subpower u.samples
  have hsource : q₂.TypicalAt (p.L - r) (p.f p.L - t.exponent) :=
    u.typicalAt_of_source (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN k)) ht
      (fun k => (t.samples.rawData_samples hp cap k).weighted_mass_le_one)
      hL.le le_rfl
      (fun k b => t.samples.rawData_pure_law hp cap hr k b _ hL.le le_rfl)
      (t.rawData_terminal_typical hp cap hr hrL.le)
  exact Submission.Obl.k4_scalar_grid_density_extension.typical_exponent_unique
    q₂.N hN₂ ht₂ q₂.sampleMeasure (q₂.sampledDensity (p.L - r)) hmass
    (q₂.hasTypicalDensity_of_typicalAt hg₂ (u.typical _ hL.le le_rfl))
    (q₂.hasTypicalDensity_of_typicalAt hg₂ hsource)

/-- The intermediate exponent comparison uses the same unrestricted shift as
the exact endpoint equality. -/
theorem intermediate_exponent
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data}
    (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (_hrL : r < p.L)
    (u : HomogeneousSelection (t.samples.rawData hp cap))
    {s : ℝ} (hs : 0 ≤ s) (hsL : s ≤ p.L - r) :
    p.f (r + s) - t.exponent ≤ u.selection.f s := by
  let q₂ := u.selection.data
  have hN₂ (k : ℕ) : 2 ≤ q₂.N k := hp.1 _
  have ht₂ : Tendsto q₂.N atTop atTop :=
    (hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop).comp
      u.selection.strictMono.tendsto_atTop
  have hmass := q₂.not_powerSmall_mass
    (fun k => (by norm_num : (1 : ℝ) ≤ 2).trans (hN₂ k)) ht₂ u.subpower u.samples
  have hg₂ (k : ℕ) (b : Fin (q₂.W k)) : Measurable (q₂.g k b s) :=
    (u.pure_law k b s hs hsL).1
  have hupper : q₂.UpperAt s (p.f (r + s) - t.exponent) :=
    u.upperAt_of_source hs hsL
      (fun k b => t.samples.rawData_pure_law hp cap hr k b s hs hsL)
      (t.rawData_upper_tail hp cap hr hs hsL)
  exact typical_exponent_ge_of_upper q₂.N hN₂ ht₂ q₂.sampleMeasure
    (q₂.sampledDensity s) hmass
    (q₂.hasTypicalDensity_of_typicalAt hg₂ (u.typical s hs hsL))
    (q₂.tagged_upper_of_upperAt hg₂ hupper)

/-- The homogeneous data keeps all finite sample bounds and the original local
cap, while its terminal density remains exactly calibrated. -/
theorem pure_valid
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data}
    (hp : p.Valid) {r h cap : ℝ}
    (t : RatioSamples p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hc : 0 < cap) (hc₁ : cap < 1)
    (hcap : ∀ s, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s))
    (u : HomogeneousSelection (t.samples.rawData hp cap)) :
    u.selection.data.PureValid := by
  have hcap₂ := cap_of_shifted_profile_comparison
    (terminal_exponent hp t hr hrL u)
    (fun s hs hsL => intermediate_exponent hp t hr hrL u hs hsL) hcap
  exact pureValid_of_samples (fun k => hp.1 _)
    ((hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop).comp
      u.selection.strictMono.tendsto_atTop)
    u.subpower (sub_pos.mpr hrL) hc hc₁ hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
    u.samples ⟨u.pure_law, u.joint_law, u.increments,
      (fun s τ hs hsL hτ => u.typical s hs hsL τ hτ), hcap₂⟩

/-- Select and homogenize an actual known atlas, retaining its uniform spatial
Jacobian/full-prior calibration and the exact normalized endpoint exponent.
The full conditional trajectory priors and normalized world weights are those
of `rawData`; only incidence events and the sample index are selected. -/
theorem exists_calibrated_normalization
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data}
    (hp : p.Valid) {r h cap : ℝ}
    (hk : Known p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hc : 0 < cap) (hc₁ : cap < 1)
    (hcap : ∀ s, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s)) :
    ∃ t : RatioSamples p r h,
    ∃ u : HomogeneousSelection (t.samples.rawData hp cap),
      u.selection.data.PureValid ∧
      u.selection.f (p.L - r) = p.f p.L - t.exponent ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
        p.N (t.samples.sequence.index (u.selection.index k)) ^ (t.exponent - ε) ≤
          |((t.samples.sequence.atlas (u.selection.index k)).Q b).det| /
            (p.ν (t.samples.sequence.index (u.selection.index k))
              ((t.samples.sequence.atlas (u.selection.index k)).γ b)
              ((t.samples.sequence.atlas (u.selection.index k)).A b)).toReal ∧
        |((t.samples.sequence.atlas (u.selection.index k)).Q b).det| /
            (p.ν (t.samples.sequence.index (u.selection.index k))
              ((t.samples.sequence.atlas (u.selection.index k)).γ b)
              ((t.samples.sequence.atlas (u.selection.index k)).A b)).toReal ≤
          p.N (t.samples.sequence.index (u.selection.index k)) ^ (t.exponent + ε) := by
  obtain ⟨t⟩ := hk.exists_ratio_samples hp hr
  obtain ⟨u⟩ := MultiHomog.pureHomogenization (t.samples.rawData hp cap)
    (fun k => hp.1 _)
    (hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop)
    (t.samples.rawData_subpower hp cap) (sub_pos.mpr hrL)
    ⟨t.samples.formatM, t.samples.formatD, t.samples.rawData_samples hp cap⟩
  exact ⟨t, u, pure_valid hp t hr hrL hc hc₁ hcap u, terminal_exponent hp t hr hrL u,
    fun ε hε => u.selection.strictMono.tendsto_atTop.eventually (t.ratios ε hε)⟩

/-- A complete normalized cap-class problem together with the exact density
shift and the actual parent Jacobian/full-prior ratios. -/
structure CalibratedRemainder
    (p : Submission.Obl.k4_remainder_pure_profile_normalization.Data) (r h cap : ℝ) where
  M : ℕ
  D : ℕ
  sequence : KnownSequence p M D r h
  remainder : NormalizedRemainder sequence cap
  exponent : ℝ
  terminal : remainder.f (p.L - r) = p.f p.L - exponent
  ratios : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
    p.N (sequence.index k) ^ (exponent - ε) ≤
      |((sequence.atlas k).Q b).det| /
        (p.ν (sequence.index k) ((sequence.atlas k).γ b) ((sequence.atlas k).A b)).toReal ∧
    |((sequence.atlas k).Q b).det| /
        (p.ν (sequence.index k) ((sequence.atlas k).γ b) ((sequence.atlas k).A b)).toReal ≤
      p.N (sequence.index k) ^ (exponent + ε)

/-- The accepted angular transport completes the calibrated pure construction,
with the same priors, worlds, profiles and density shift. This includes depth
zero and needs no saturation of the original known atlas. -/
theorem exists_calibrated_remainder
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data} (hp : p.Valid)
    {r h cap : ℝ} (hk : Known p r h) (hr : 0 ≤ r) (hrL : r < p.L)
    (hc : 0 < cap) (hc₁ : cap < 1)
    (hcap : ∀ s, r ≤ s → s ≤ p.L → p.f p.L - p.f s ≤ cap * (p.L - s)) :
    Nonempty (CalibratedRemainder p r h cap) := by
  obtain ⟨t, u, hvalid, hterminal, hratio⟩ :=
    exists_calibrated_normalization hp hk hr hrL hc hc₁ hcap
  let s := t.samples.sequence.reindex u.selection.index u.selection.strictMono
  have hprior (k : ℕ) (b : Fin (s.atlas k).C) :
      0 < (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal :=
    t.samples.prior_pos hp (u.selection.index k) b
  have hZ := s.normalizer_subpower hp
  have hcompare : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
      p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q b).det| ≤
        p.N (s.index k) ^ ε *
          (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal *
            p.N (s.index k) ^ (-u.selection.f (p.L - r)) := by
    intro ε hε
    filter_upwards [hratio ε hε] with k hk b
    exact terminal_floor_of_ratio (by linarith [hp.1 (s.index k)])
      (hprior k b) hterminal (hk b).2
  have hang : (s.remainingData cap u.selection.K u.selection.E u.selection.f
      u.selection.g u.selection.G).AngularValid := by
    exact Submission.Obl.k4_remainder_angular_cap_transport.transport
      p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      ((p.valid_iff_pure_angular).mp hp) r h cap hr hrL
      t.samples.atlasM t.samples.atlasD s.index
      (fun k => (s.atlas k).κ) (fun k => (s.atlas k).T) (fun k => (s.atlas k).C)
      (fun k => (s.atlas k).γ) (fun k => (s.atlas k).j)
      (fun k => (s.atlas k).c) (fun k => (s.atlas k).u) (fun k => (s.atlas k).Q)
      (fun k => (s.atlas k).R) (fun k => (s.atlas k).A) (fun k => (s.atlas k).F)
      u.selection.K u.selection.E u.selection.f u.selection.g u.selection.G
      ⟨s.strictMono, s.slack_one, s.slack_ambient, s.slack_subpower, s.time_upper, s.valid⟩
      ⟨hvalid, u.event_subset, hprior, hZ, hcompare⟩
  refine ⟨⟨t.samples.atlasM, t.samples.atlasD, s, {
    K := u.selection.K
    E := u.selection.E
    f := u.selection.f
    g := u.selection.g
    G := u.selection.G
    valid := ?_
    event_subset := u.event_subset
    prior_positive := hprior
    normalizer_subpower := hZ
    terminal_comparison := hcompare }, t.exponent, hterminal, hratio⟩⟩
  exact (Data.valid_iff_pure_angular _).mpr ⟨hvalid, hang⟩

/-- In particular a depth-zero known atlas produces a calibrated problem in
the same cap class, even when that atlas was not saturated. -/
theorem exists_depth_zero_calibrated_remainder
    {p : Submission.Obl.k4_remainder_pure_profile_normalization.Data} (hp : p.Valid)
    {h : ℝ} (hk : Known p 0 h) : Nonempty (CalibratedRemainder p 0 h p.d) := by
  have hp₀ := hp
  rcases hp with ⟨_, _, _, hL, hd, hd₁, _, _, _, _, _, _, _, hcap, _⟩
  exact exists_calibrated_remainder hp₀ hk le_rfl hL hd hd₁ hcap

end BalancedNormalization
end Submission.Obl.k4_balanced_native_packet_transport.CPF
