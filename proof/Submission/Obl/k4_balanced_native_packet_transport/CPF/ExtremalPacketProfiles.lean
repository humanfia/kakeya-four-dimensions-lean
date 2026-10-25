/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/ExtremalPacketProfiles.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.RelativePacketBalance
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SplitInterfaces
import Submission.Obl.k4_local_remainder_horizon_transfer.Bridges

/-! Extremality supplies relative profile control for the actual complete
depth-zero calibrated normalization, because its genuine horizon is preserved. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace ExtremalPacketProfiles

open MeasureTheory Set Filter
open BalancedPacketSystems

theorem source_horizonExpanded_eq (p : SourceData) :
    HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f =
      CalibratedHorizon.horizon p :=
  Submission.Obl.k4_local_remainder_horizon_transfer.horizonExpanded_eq
    (CalibratedHorizon.toData p)

/-- The same outer tolerance works for every actual normalized remainder.
The profile is controlled only after subtracting its own value at zero. -/
theorem relative_profiles (hi : InitialHorizonExpanded)
    {ds kr S η err : ℝ} (es : ExtremalSetup ds kr S η) (herr : 0 < err) :
    ∃ a : ℝ, 0 < a ∧ ∀ p : SourceData, p.Valid → p.L = 1 →
      p.S = S → p.η = η → p.d < ds + a →
      kr - a < CalibratedHorizon.horizon p →
      (∀ r ∈ Icc (0 : ℝ) 1, |p.f r - p.f 0 - ds * r| ≤ err) ∧
      ∀ q : Certificate p, ∀ r ∈ Icc (0 : ℝ) 1,
        |q.remainder.f r - q.remainder.f 0 - ds * r| ≤ err := by
  obtain ⟨a, ha, hprofile⟩ := es.2.2.2.2.2.2 err herr
  refine ⟨a, ha, fun p hp hL hS hη hd hnear => ?_⟩
  subst S
  subst η
  constructor
  · have hpH : (kr - a) * p.L <
        HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f := by
      rw [source_horizonExpanded_eq, hL, mul_one]
      exact hnear
    have hclose := hprofile p.N p.K p.L p.d p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
      hp hd hpH
    intro r hr
    have h := hclose r hr.1 (by simpa only [hL] using hr.2)
    simpa only [hL, mul_one] using h
  intro q
  let z := q.remainder.data
  have hbound : CalibratedHorizon.horizon p ≤ CalibratedHorizon.horizon z := by
    simpa only [zero_add] using CalibratedHorizon.horizon_bound
      (Submission.Obl.k4_local_remainder_horizon_transfer.initialHorizon_iff.mp hi)
      hp q (by norm_num : (0 : ℝ) ≤ 0)
  have hzL : z.L = 1 := by
    change p.L - 0 = 1
    simpa only [sub_zero] using hL
  have hzH : (kr - a) * z.L <
      HorizonExpanded z.N z.K z.L z.W z.ω z.ν z.E z.B z.f := by
    rw [source_horizonExpanded_eq, hzL, mul_one]
    exact hnear.trans_le hbound
  have hclose := hprofile z.N z.K z.L z.d z.W z.ω z.ν z.E z.P z.B z.f z.g z.G
    q.remainder.valid hd hzH
  intro r hr
  have h := hclose r hr.1 (by simpa only [hzL] using hr.2)
  change |q.remainder.f r - q.remainder.f 0 - ds * r| ≤ err * z.L at h
  simpa only [hzL, mul_one] using h

/-- A depth-zero known atlas in a sufficiently close maximizing problem
produces actual balanced covered packets. Extremality supplies both relative
profile estimates, and the original initial density remains in the ratio. -/
theorem exists_packets_from_known_zero (hi : InitialHorizonExpanded)
    {ds kr S η b D err : ℝ} (es : ExtremalSetup ds kr S η)
    (hb : 0 < b) (hb₁ : 2 * b ≤ 1) (herr : 0 < err)
    (hD : 0 < D) (hD₁ : D < 1) (hdD : ds < D)
    (hsmall : 2 * err ≤ (D - ds) * b) :
    ∃ tolerance : ℝ, 0 < tolerance ∧ ∀ p : SourceData, p.Valid → p.L = 1 →
      p.S = S → p.η = η → p.d < ds + tolerance →
      kr - tolerance < CalibratedHorizon.horizon p →
      Submission.Obl.k4_remainder_pure_profile_normalization.Known p 0 0 →
      ∃ q : Certificate p, ∃ r ∈ Icc b (2 * b), ∀ h : ℝ, 2 * b < h →
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
              p.N (q.sequence.index k) ^ (-ds * r - (3 * err + ε)) ≤
                originalMass q k a c /
                  (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ∧
              originalMass q k a c /
                  (p.N (q.sequence.index k) ^ (-p.f 0) * |(composedFrame q k a c).det|) ≤
                p.N (q.sequence.index k) ^ (-ds * r + (3 * err + ε)) := by
  obtain ⟨tolerance, htol, hprofiles⟩ := relative_profiles hi es herr
  refine ⟨tolerance, htol, fun p hp hL hS hη hd hnear hk => ?_⟩
  obtain ⟨q⟩ := BalancedNormalization.exists_depth_zero_calibrated_remainder hp hk
  obtain ⟨hold, hnew⟩ := hprofiles p hp hL hS hη hd hnear
  refine ⟨q, ?_⟩
  exact RelativePacketBalance.exists_balanced_covered_systems (initialHorizon_iff.mp hi)
    hp hL q hb hb₁ hD hD₁ hdD
    (by simpa only [mul_one] using hold 1 (by norm_num)) (hnew q) hsmall

end ExtremalPacketProfiles
end Submission.Obl.k4_balanced_native_packet_transport.CPF
