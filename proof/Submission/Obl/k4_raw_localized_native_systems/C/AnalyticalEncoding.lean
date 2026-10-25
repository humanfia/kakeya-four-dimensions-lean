import Submission.Obl.k4_raw_localized_native_systems.C.KnownSystems
import Submission.Obl.k4_original_observation_atlas_encoding.Assembly

/-
Adapted from this LOT tree, o178, session x0596, `AnalyticalEncoding.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open Filter MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Lib.K4XInterface

noncomputable section

/-- Geometric chart events with an analytical observable list.  List success
is measured on the unchanged original priors, while the chart events have the
fixed Boolean format. -/
def AnalyticalKnownAt {p : Data} {k : ℕ} (a : Atlas p k)
    (M D : ℕ) (ε r : ℝ) : Prop :=
  (a.C : ℝ) ≤ p.N k ^ M ∧
  (∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' →
    Disjoint (a.A b) (a.A b')) ∧
  (∀ w o, ((a.lst w o).card : ℝ) ≤ p.N k ^ ε) ∧
  (∀ w b, MeasurableSet {o | b ∈ a.lst w o}) ∧
  (∀ b, gchart (p.N k) M D (p.N k ^ ε) a.T ((a.j b : ℕ) : ℝ) r
    (p.B k (a.γ b)) (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b)
    (a.A b) (a.F b) True) ∧
  ENNReal.ofReal (p.N k ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) *
    ((p.ν k (a.γ b)).prod volume)
      {z | z ∈ a.F b ∧ b ∈ a.lst (a.γ b) (gobs (p.B k (a.γ b)) (gδ (p.N k) p.L) z)}

def AnalyticalKnownSystem (p : Data) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ a : Atlas p k, (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧ AnalyticalKnownAt a M D ε r

/-- The original problem's fixed mixture format is exactly the hypothesis
needed by the accepted original-observation encoding theorem. -/
theorem valid_temperedLaw {p : Data} (hp : Valid p) :
    ∃ M D : ℕ, ∀ k,
      Submission.Obl.k4_original_observation_atlas_encoding.temperedLaw
        (p.N k) M D (p.W k) (p.ω k) (p.ν k) (p.B k) := by
  obtain ⟨M, D, hf⟩ := hp.2.2.2.2.2.2.2.2.1
  refine ⟨M, D, fun k => ?_⟩
  obtain ⟨hW, hω, hw, hworlds, hmass⟩ := hf k
  refine ⟨hW, hω, hw, fun w => ?_⟩
  have hh := hworlds w
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.2.2.1⟩

/-- Analytical list success suffices for an actual fixed-format known atlas.
The encoding theorem chooses the output format before its exponent tolerance;
the proof never substitutes a merely outer-diagonal loss for that order. -/
theorem AnalyticalKnownSystem.to_knownSystem {p : Data} (hp : Valid p)
    {r h : ℝ} (hs : AnalyticalKnownSystem p r h) : KnownSystem p r h := by
  obtain ⟨Mν, Dν, hlaw⟩ := valid_temperedLaw hp
  obtain ⟨M, D, hs⟩ := hs
  obtain ⟨M', D', hM, hD, hencode⟩ :=
    Submission.Obl.k4_original_observation_atlas_encoding.encoding
      p.L hp.length_pos Mν Dν M D
  refine ⟨M', D', fun τ hτ => ?_⟩
  let ε : ℝ := min (τ / 4) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hετ : ε ≤ τ / 4 := min_le_left _ _
  have hε1 : ε ≤ 1 / 8 := min_le_right _ _
  obtain ⟨N₀, hN₀, henc⟩ := hencode τ hτ
  have hlateN : ∀ᶠ k in atTop, N₀ ≤ p.N k :=
    hp.scale_tendsto.eventually (eventually_ge_atTop N₀)
  refine ((hs ε hε).and_eventually (hlateN.and (hp.slack_subpower τ hτ))).mono ?_
  rintro k ⟨⟨a, hT, hC, hdisj, hlst, hlstm, hcharts, hmass⟩, hNk, hK⟩
  obtain ⟨F', lst', hsub, hlst', hcharts', hmass'⟩ := henc (p.N k) hNk
    (p.W k) (p.ω k) (p.ν k) (p.B k) (p.E k) (hlaw k) ε r a.T a.C
    a.γ a.j a.c a.u a.Q a.R a.A a.F a.lst hε hετ hε1 hC hlst hlstm hcharts hmass
  let a' : Atlas p k := { a with F := F', lst := lst' }
  refine ⟨p.N k ^ τ, Real.one_le_rpow (hp.scale_ge_one k) hτ.le, hK,
    le_rfl, a', hT.trans ?_, ⟨?_, hdisj, hcharts', ?_⟩, hlst'⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)
  · exact hC.trans (pow_le_pow_right₀ (hp.scale_ge_one k) hM)
  · simpa only [Real.rpow_neg (hp.scale_pos k).le, a', priorMass] using hmass'

end
end Submission.Obl.k4_raw_localized_native_systems.C
