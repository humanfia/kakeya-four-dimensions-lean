import Submission.Obl.k4_raw_localized_native_systems.C.RecoveredMass
import Submission.Obl.k4_raw_localized_native_systems.C.RecoveryNumerics
import Submission.Obl.k4_raw_localized_native_systems.C.AnalyticalEncoding

/-
Adapted from this LOT tree, o178, session x0596, `SampleRecovery.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- At one sufficiently late sample, recover all substantial packets and
assemble an analytical known atlas on the original priors.  Its format is
fixed independently of the requested output slack. -/
theorem ProjectedPackets.to_analytical
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c ε : ℝ}
    (hp : Valid p) (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (hrule : ScalarRecoveryRule (p.N k) η d s m S U c Mq Dq)
    (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (hloss : loss ≤ ε)
    (hlists : p.N k ^ loss * (Mq : ℝ) ≤ p.N k ^ ε)
    (hgap : 2 * p.N k ^ (-ε) + p.N k ^ (-η) ≤ p.N k ^ (-loss)) :
    ∃ a' : Atlas p k,
      (2 : ℝ) ^ a'.T ≤ p.N k ^ (h + ε) ∧
      AnalyticalKnownAt a' (2 * Mp + Mq + 10) (max Dp (2 * Dq)) ε (c / 2) := by
  classical
  obtain ⟨out, hsuccess⟩ := a.recover_candidates hp hrule
  let a' := recoveredAtlas a.atlas a.offset a.tangent out
  refine ⟨a', a.time.trans ?_, ?_, a.recovered_disjoint out, ?_,
    recoveredAtlas_list_measurable a.atlas a.offset a.tangent out a.list_measurable, ?_, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)
  · have hds : d * s ≤ 1 := mul_le_one₀ hd1.le hs.le hs1.le
    have hn : p.N k ^ (d * s + 1) ≤ p.N k ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using
        (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k)
          (show d * s + 1 ≤ (2 : ℝ) by linarith))
    calc
      (a'.C : ℝ) ≤ (a.atlas.C : ℝ) * p.N k ^ (d * s + 1) :=
        recoveredAtlas_count a.atlas a.offset a.tangent out
      _ ≤ p.N k ^ Mp * p.N k ^ (2 : ℕ) :=
        mul_le_mul a.known.1.1 hn (Real.rpow_nonneg (hp.scale_pos k).le _)
          (pow_nonneg (hp.scale_pos k).le _)
      _ = p.N k ^ (Mp + 2) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (hp.scale_ge_one k) (by omega)
  · intro w o
    have hb : ((a'.lst w o).card : ℝ) ≤ ((a.atlas.lst w o).card : ℝ) * (Mq : ℝ) := by
      exact_mod_cast recoveredAtlas_list_card a.atlas a.offset a.tangent out w o
    exact hb.trans ((mul_le_mul_of_nonneg_right (a.known.2 w o) (Nat.cast_nonneg Mq)).trans hlists)
  · intro z
    let bi := (candidateEquiv out).symm z
    exact a.recovered_chart hp (out bi.1) bi.1 bi.2 hc hε hloss
      (by omega) (le_max_left _ _) (le_max_right _ _)
      (recovery_format_bound (hp.scale_ge_two k) Mp Mq)
      (recovery_coefficient_bound (hp.scale_ge_two k) Mp Mq)
  · exact recovery_mass_lower (Real.rpow_pos_of_pos (hp.scale_pos k) _).le
      (Real.rpow_pos_of_pos (hp.scale_pos k) _).le hgap
      (a.recovered_mass hp out hsuccess)

end
end Submission.Obl.k4_raw_localized_native_systems.C
