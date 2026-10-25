/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/RelativePacketBalance.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.OriginalPacketCoverage

/-! Balance relative to the original initial density. The factor N^(-f(0))
is retained, so neither problem needs an absolute density normalization. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace RelativePacketBalance

open MeasureTheory Set Filter
open BalancedPacketSystems

theorem relative_ratio_bounds {N mass J f₀ f₁ F₁ Fb d r err ε : ℝ}
    (hN : 1 ≤ N)
    (hraw : N ^ (-f₁ + F₁ - Fb - 2 * ε) ≤ mass / J ∧
      mass / J ≤ N ^ (-f₁ + F₁ - Fb + 2 * ε))
    (hold : |f₁ - f₀ - d| ≤ err)
    (hrelative : |F₁ - Fb - d * (1 - r)| ≤ 2 * err) :
    N ^ (-d * r - (3 * err + 2 * ε)) ≤ mass / (N ^ (-f₀) * J) ∧
      mass / (N ^ (-f₀) * J) ≤ N ^ (-d * r + (3 * err + 2 * ε)) := by
  have hN₀ : 0 < N := by linarith
  have hbase : 0 < N ^ (-f₀) := Real.rpow_pos_of_pos hN₀ _
  have heq : mass / (N ^ (-f₀) * J) = (mass / J) / N ^ (-f₀) := by ring
  have ho := abs_le.mp hold
  have hr := abs_le.mp hrelative
  rw [heq]
  constructor
  · apply (le_div_iff₀ hbase).mpr
    apply le_trans _ hraw.1
    rw [← Real.rpow_add hN₀]
    exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  · apply (div_le_iff₀ hbase).mpr
    apply hraw.2.trans
    rw [← Real.rpow_add hN₀]
    exact Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)

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
    (hold : |p.f 1 - p.f 0 - d| ≤ err)
    (hprofile : ∀ s ∈ Icc (0 : ℝ) 1,
      |q.remainder.f s - q.remainder.f 0 - d * s| ≤ err) :
    ∀ c, MeasurableSet (originalAssignment q k a c) ∧
      p.N (q.sequence.index k) ^ (-d * r - (3 * err + 2 * ε)) ≤
        originalMass q k a c /
          (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ∧
      originalMass q k a c /
          (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ≤
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
  obtain ⟨hQ, _, _, _, _, _, hA, _, _, _, _, _⟩ := hcharts (a.γ c)
  letI : IsProbabilityMeasure
      (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))) :=
    (hsample (q.sequence.index k)).prob _
  have hchild := SmallDepthSaturation.prior_power_band (normalizedData_valid q) ha hκ hκN c
  have hchild' := And.intro hchild.2.1 hchild.2.2
  change p.N (q.sequence.index k) ^ (-q.remainder.f r - ε) ≤
      (((normalizedData q).ν k (a.γ c)) (a.A c)).toReal / |(a.Q c).det| ∧
    (((normalizedData q).ν k (a.γ c)) (a.A c)).toReal / |(a.Q c).det| ≤
      p.N (q.sequence.index k) ^ (-q.remainder.f r + ε) at hchild'
  have hdet : |(composedFrame q k a c).det| / |((q.sequence.atlas k).Q (a.γ c)).det| =
      |(a.Q c).det| := by
    rw [composedFrame, Matrix.det_mul, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hQ)]
  have hmass := NormalizedAssignments.normalized_assignment_mass
    (q.sequence.atlas k) (a.γ c) (parent_det_ne_zero q k (a.γ c)) (a.A c) hB
  change (((normalizedData q).ν k (a.γ c)) (a.A c)).toReal =
    originalMass q k a c / _ at hmass
  have hraw := PacketCancellation.ratio_bounds
    (by linarith [hp.1 (q.sequence.index k)] : 0 < p.N (q.sequence.index k))
    (q.remainder.prior_positive k (a.γ c)) (abs_pos.mpr hQ)
    (abs_pos.mpr (by rw [composedFrame, Matrix.det_mul]; exact mul_ne_zero hQ hR))
    (hparent (a.γ c))
    (show p.N (q.sequence.index k) ^ (-q.remainder.f r - ε) ≤
        (originalMass q k a c /
          (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))
            ((q.sequence.atlas k).A (a.γ c))).toReal) /
          (|(composedFrame q k a c).det| / |((q.sequence.atlas k).Q (a.γ c)).det|) ∧
      (originalMass q k a c /
          (p.ν (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c))
            ((q.sequence.atlas k).A (a.γ c))).toReal) /
          (|(composedFrame q k a c).det| / |((q.sequence.atlas k).Q (a.γ c)).det|) ≤
        p.N (q.sequence.index k) ^ (-q.remainder.f r + ε) from by
      simpa only [hdet, ← hmass] using hchild')
    hterminal
  refine ⟨NormalizedAssignments.measurableSet_originalAssignment _ _ _ hA _ hB, ?_⟩
  exact relative_ratio_bounds (by linarith [hp.1 (q.sequence.index k)]) hraw hold hrelative

/-- Full original coverage and balance relative to N^(-f(0)). Only relative
profile estimates enter; the original initial density can be arbitrary. -/
theorem exists_balanced_covered_systems (hi : InitialHorizon) {p : SourceData}
    (hp : p.Valid) (hL : p.L = 1) (q : Certificate p)
    {b d D err : ℝ} (hb : 0 < b) (hb₁ : 2 * b ≤ 1)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : d < D)
    (hold : |p.f 1 - p.f 0 - d| ≤ err)
    (hprofile : ∀ s ∈ Icc (0 : ℝ) 1,
      |q.remainder.f s - q.remainder.f 0 - d * s| ≤ err)
    (hsmall : 2 * err ≤ (D - d) * b) :
    ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
      ∃ M₁ D₁ : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
        ∃ a : Atlas (normalizedData q) k,
          1 ≤ a.κ ∧ (normalizedData q).K k ≤ a.κ ∧
          a.κ ≤ (normalizedData q).N k ^ ε ∧
          (2 : ℝ) ^ a.T ≤ (normalizedData q).N k ^ h ∧ a.SaturatedAt M₁ D₁ r ∧
          ENNReal.ofReal (p.N (q.sequence.index k) ^ (-ε)) ≤
            OriginalPacketCoverage.originalCoveredMass q k a ∧
          ∀ c, MeasurableSet (originalAssignment q k a c) ∧
            MeasurableSet (OriginalPacketCoverage.originalEvent q k a c) ∧
            OriginalPacketCoverage.originalEvent q k a c ⊆
              p.E (q.sequence.index k) ((q.sequence.atlas k).γ (a.γ c)) ∧
            OriginalPacketCoverage.originalEvent q k a c ⊆
              originalAssignment q k a c ×ˢ (univ : Set ℝ) ∧
            p.N (q.sequence.index k) ^ (-d * r - (3 * err + ε)) ≤
              originalMass q k a c /
                (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ∧
            originalMass q k a c /
                (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ≤
              p.N (q.sequence.index k) ^ (-d * r + (3 * err + ε)) := by
  have hbL : 2 * b ≤ (normalizedData q).L := by
    change 2 * b ≤ p.L - 0
    simpa only [hL, sub_zero] using hb₁
  obtain ⟨r, hr, hs⟩ := SmallDepthSaturation.exists_small_saturated_systems hi
    (normalizedData_valid q) hb hbL hD hD₁ hdD
    (fun t ht => hprofile t ⟨ht.1, ht.2.trans hb₁⟩) hsmall
  refine ⟨r, hr, fun h hh => ?_⟩
  obtain ⟨M₁, D₁, hs⟩ := hs h hh
  refine ⟨M₁, D₁, fun ε hε => ?_⟩
  apply (((hs (ε / 2) (half_pos hε)).and_eventually
    (q.sequence.slack_subpower (ε / 2) (half_pos hε))).and_eventually
    (q.ratios (ε / 2) (half_pos hε))).mono
  rintro k ⟨⟨⟨a, hκ, hK, hκN, hT, ha, _⟩, hparent⟩, hratios⟩
  have hN : 1 ≤ (normalizedData q).N k := by
    change 1 ≤ p.N (q.sequence.index k)
    linarith [hp.1 (q.sequence.index k)]
  refine ⟨a, hκ, hK, hκN.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hT, ha,
    OriginalPacketCoverage.original_coverage_power_lower hp q ha.1 hκ hparent hκN,
    fun c => ?_⟩
  obtain ⟨hA, hlo, hhi⟩ := original_mass_band hp hL q ha hκ hκN
    ⟨(hb.trans_le hr.1).le, hr.2.trans hb₁⟩ hratios hold hprofile c
  refine ⟨hA, OriginalPacketCoverage.measurableSet_originalEvent q ha.1 c,
    OriginalPacketCoverage.originalEvent_subset_original q ha.1 c,
    OriginalPacketCoverage.originalEvent_subset_assignment q ha.1 c, ?_⟩
  simpa only [show 2 * (ε / 2) = ε by ring] using And.intro hlo hhi

end RelativePacketBalance
end Submission.Obl.k4_balanced_native_packet_transport.CPF
