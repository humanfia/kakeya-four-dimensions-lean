/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/BalancedPacketSystems.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.CalibratedHorizon
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SmallDepthSaturation
import Submission.Obl.k4_balanced_native_packet_transport.CPF.NormalizedAssignments

/-! Genuine saturated packets inside the actual calibrated normalized family,
with balanced full assignment masses back in the original worlds. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace BalancedPacketSystems

open MeasureTheory Set Filter

abbrev SourceData := Submission.Obl.k4_remainder_pure_profile_normalization.Data
abbrev Certificate (p : SourceData) := BalancedNormalization.CalibratedRemainder p 0 0 p.d

noncomputable def normalizedData {p : SourceData} (q : Certificate p) : Data :=
  let P := q.remainder.data
  ⟨P.N, P.K, P.L, P.d, P.S, P.η, P.W, P.ω, P.ν, P.E, P.P, P.B, P.f, P.g, P.G⟩

theorem normalizedData_valid {p : SourceData} (q : Certificate p) :
    (normalizedData q).Valid := q.remainder.valid

theorem parent_det_ne_zero {p : SourceData} (q : Certificate p) (k : ℕ)
    (b : Fin (q.sequence.atlas k).C) : ((q.sequence.atlas k).Q b).det ≠ 0 := by
  obtain ⟨_, _, _, _, hchart, _⟩ := q.sequence.valid k
  exact (hchart b).1

def originalAssignment {p : SourceData} (q : Certificate p) (k : ℕ)
    (a : Atlas (normalizedData q) k) (c : Fin a.C) : Set Trajectory :=
  NormalizedAssignments.originalAssignment (q.sequence.atlas k) (a.γ c)
    (parent_det_ne_zero q k (a.γ c)) (a.A c)

def composedFrame {p : SourceData} (q : Certificate p) (k : ℕ)
    (a : Atlas (normalizedData q) k) (c : Fin a.C) : Frame :=
  (q.sequence.atlas k).Q (a.γ c) * a.Q c

noncomputable def originalMass {p : SourceData} (q : Certificate p) (k : ℕ)
    (a : Atlas (normalizedData q) k) (c : Fin a.C) : ℝ :=
  (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))
    (originalAssignment q k a c)).toReal

/-- The exact parent and child calibrations cancel uniformly on every chart.
Only an outer relative-profile error and an inner arbitrary loss remain. -/
theorem original_mass_band {p : SourceData} (hp : p.Valid) (hL : p.L = 1)
    (q : Certificate p) {k M D : ℕ} {r ε err d : ℝ}
    {a : Atlas (normalizedData q) k} (ha : a.SaturatedAt M D r)
    (hκ : 1 ≤ a.κ) (hκN : a.κ ≤ (normalizedData q).N k ^ ε)
    (hr : r ∈ Icc (0 : ℝ) 1)
    (hparent : ∀ b,
      p.N (q.sequence.index k) ^ (q.exponent - ε) ≤
        |((q.sequence.atlas k).Q b).det| /
          (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ b)
            ((q.sequence.atlas k).A b)).toReal ∧
      |((q.sequence.atlas k).Q b).det| /
          (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ b)
            ((q.sequence.atlas k).A b)).toReal ≤
        p.N (q.sequence.index k) ^ (q.exponent + ε))
    (hold : |p.f 1 - d| ≤ err)
    (hprofile : ∀ s ∈ Icc (0 : ℝ) 1,
      |q.remainder.f s - q.remainder.f 0 - d * s| ≤ err) :
    ∀ c, MeasurableSet (originalAssignment q k a c) ∧
      p.N (q.sequence.index k) ^ (-d * r - (3 * err + 2 * ε)) ≤
        originalMass q k a c / |(composedFrame q k a c).det| ∧
      originalMass q k a c / |(composedFrame q k a c).det| ≤
        p.N (q.sequence.index k) ^ (-d * r + (3 * err + 2 * ε)) := by
  have hrelative : |q.remainder.f 1 - q.remainder.f r - d * (1 - r)| ≤ 2 * err := by
    have h₁ := abs_le.mp (hprofile 1 (by norm_num))
    have hr' := abs_le.mp (hprofile r hr)
    rw [abs_le]
    constructor <;> nlinarith
  have hterminal : q.remainder.f 1 = p.f 1 - q.exponent := by
    simpa only [hL, sub_zero] using q.terminal
  obtain ⟨_, _, hsample⟩ := hp.sampleProblem
  obtain ⟨_, _, _, _, hcharts, _⟩ := q.sequence.valid k
  intro c
  obtain ⟨hR, _, _, _, _, _, hB, _, _, _, _, _⟩ := ha.1.2.2.1 c
  obtain ⟨_, _, _, _, _, _, hA, _, _, _, _, _⟩ := hcharts (a.γ c)
  letI : IsProbabilityMeasure
      (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))) :=
    (hsample (q.sequence.index k)).prob _
  have hchild := SmallDepthSaturation.prior_power_band (normalizedData_valid q) ha hκ hκN c
  refine ⟨NormalizedAssignments.measurableSet_originalAssignment _ _ _ hA _ hB, ?_⟩
  exact NormalizedAssignments.original_assignment_relative_band
    (q.sequence.atlas k) (a.γ c) (parent_det_ne_zero q k (a.γ c))
    (a.A c) hB (a.Q c) hR (by linarith [hp.1 (q.sequence.index k)])
    (q.remainder.prior_positive k (a.γ c)) (hparent (a.γ c))
    ⟨hchild.2.1, hchild.2.2⟩ hterminal hold hrelative

/-- The actual normalized problem supplies small saturated true packets whose
full ORIGINAL assignment masses obey the balanced density bounds. Formats are
fixed before every inner loss, independently of all density shifts. -/
theorem exists_balanced_systems (hi : InitialHorizon) {p : SourceData}
    (hp : p.Valid) (hL : p.L = 1) (q : Certificate p)
    {b d D err : ℝ} (hb : 0 < b) (hb₁ : 2 * b ≤ 1)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hold : |p.f 1 - d| ≤ err)
    (hprofile : ∀ s ∈ Icc (0 : ℝ) 1,
      |q.remainder.f s - q.remainder.f 0 - d * s| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
      ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
        ∃ a : Atlas (normalizedData q) k,
          1 ≤ a.κ ∧ (normalizedData q).K k ≤ a.κ ∧
          a.κ ≤ (normalizedData q).N k ^ ε ∧
          (2 : ℝ) ^ a.T ≤ (normalizedData q).N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
          ∀ c, MeasurableSet (originalAssignment q k a c) ∧
            p.N (q.sequence.index k) ^ (-d * r - (3 * err + 2 * ε)) ≤
              originalMass q k a c / |(composedFrame q k a c).det| ∧
            originalMass q k a c / |(composedFrame q k a c).det| ≤
              p.N (q.sequence.index k) ^ (-d * r + (3 * err + 2 * ε)) := by
  have hbL : 2 * b ≤ (normalizedData q).L := by
    change 2 * b ≤ p.L - 0
    simpa only [hL, sub_zero] using hb₁
  obtain ⟨r, hr, hsystems⟩ := SmallDepthSaturation.exists_small_saturated_systems hi
    (normalizedData_valid q) hb hbL hD hD₁ hdD
    (fun t ht => hprofile t ⟨ht.1, ht.2.trans hb₁⟩) hsmall
  refine ⟨r, hr, fun h hh => ?_⟩
  obtain ⟨M₁, D₁, hs⟩ := hsystems h hh
  refine ⟨M₁, D₁, fun ε hε => ?_⟩
  apply ((hs ε hε).and_eventually (q.ratios ε hε)).mono
  rintro k ⟨⟨a, hκ, hK, hκN, hT, ha, _⟩, hratios⟩
  exact ⟨a, hκ, hK, hκN, hT, ha,
    original_mass_band hp hL q ha hκ hκN ⟨(hb.trans_le hr.1).le, hr.2.trans hb₁⟩
      hratios hold hprofile⟩

end BalancedPacketSystems
end Submission.Obl.k4_balanced_native_packet_transport.CPF
