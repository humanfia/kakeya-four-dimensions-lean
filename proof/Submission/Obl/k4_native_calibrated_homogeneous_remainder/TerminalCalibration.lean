import Submission.Obl.k4_native_calibrated_homogeneous_remainder.HomogeneousRemainder
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TerminalAsymptotics
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ExponentComparison

/-! Terminal-list refinement forces the calibration exponent; a cofinal
vanishing error then makes calibration exact in every retained world. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

theorem RawValid.family_mass_not_powerSmall {q : Data} (hq : RawValid q) :
    ¬ IsPowerSmall q.N (fun k => familyLaw q k univ) := by
  apply not_isPowerSmall_of_inverse_subpower hq.2.1
  intro ε hε
  have hq0 := hq
  obtain ⟨hN, -, hK, -, -, -, -, -, M, D, hfmt⟩ := hq
  filter_upwards [hK.2 ε hε] with k hk
  have hlow : q.N k ^ (-ε) ≤ (q.K k)⁻¹ := by
    rw [Real.rpow_neg (by linarith [hN k])]
    exact inv_anti₀ (by linarith [hK.1 k]) hk
  apply (ENNReal.ofReal_le_ofReal hlow).trans
  simpa only [familyLaw, worldLaw_univ, selected, priorMass] using (hfmt k).2.2.2.2

theorem HomogeneousRemainder.terminal_exponent_le {p q : Data} {r h w : ℝ}
    (a : HomogeneousRemainder p q r h w) (hp : Valid p) :
    q.f q.L + a.ratio_exponent ≤ p.f p.L := by
  let old : (k : ℕ) → Fin (q.W k) × Incidence → ENNReal :=
    fun k z => a.toRemainderGeometry.oldTerminalDensity k z.1 z.2
  let current : (k : ℕ) → Fin (q.W k) × Incidence → ENNReal :=
    fun k z => q.g k z.1 q.L (obs (q.B k z.1) (δ (q.N k) q.L) z.2)
  have hlo : ∀ k, ∀ᵐ z ∂familyLaw q k,
      ENNReal.ofReal (a.toRemainderGeometry.densityRatio k z.1) *
        a.toRemainderGeometry.restrictedTerminalDensity k z.1 z.2 ≤ current k z := by
    intro k
    apply ae_worldLaw
    intro b
    exact a.toRemainderGeometry.terminal_density_lower hp a.raw_valid
      (fun k b => a.homogeneous.2.1 k b q.L) k b
  have hcompare : ∀ ε : ℝ, 0 < ε → IsPowerSmall q.N (fun k => familyLaw q k
      {z | current k z < ENNReal.ofReal (q.N k ^ (a.ratio_exponent - ε)) * old k z}) := by
    intro ε hε
    apply IsPowerSmall.mono (a.toRawRemainder.terminal_refinement_isPowerSmall hp
      (ε / 2) (by positivity))
    filter_upwards [a.ratio_band (ε / 2) (by positivity)] with k hk
    apply measure_mono_ae
    filter_upwards [hlo k] with z hz hbad
    by_contra hn
    have hNk : 0 < q.N k := by linarith [a.raw_valid.1 k]
    have hcmp : ENNReal.ofReal (q.N k ^ (a.ratio_exponent - ε)) * old k z ≤ current k z := by
      calc
        _ = ENNReal.ofReal (q.N k ^ (a.ratio_exponent - ε / 2)) *
            (ENNReal.ofReal (q.N k ^ (-(ε / 2))) * old k z) := by
          rw [← mul_assoc, ofReal_rpow_mul_rpow hNk]
          congr 2
          ring
        _ ≤ ENNReal.ofReal (a.toRemainderGeometry.densityRatio k z.1) *
            a.toRemainderGeometry.restrictedTerminalDensity k z.1 z.2 :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (hk z.1).1) (not_lt.mp hn)
        _ ≤ _ := hz
    exact not_lt_of_ge hcmp hbad
  exact exponent_le_of_power_lower_comparison q.N a.raw_valid.1 a.raw_valid.2.1
    (familyLaw q) old current (p.f p.L) (q.f q.L) a.ratio_exponent
    a.raw_valid.family_mass_not_powerSmall (a.toRawRemainder.old_terminal_typical hp)
    (a.homogeneous.2.2.2.2 q.L a.raw_valid.2.2.2.1.le le_rfl) hcompare

theorem HomogeneousRemainder.eventual_terminal_calibration {p q : Data} {r h w : ℝ}
    (a : HomogeneousRemainder p q r h w) (hp : Valid p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
      p.N (a.φ k) ^ (-p.f p.L) * |Matrix.det ((a.parent k).Q (a.worlds k b))| ≤
        q.N k ^ ε * (a.toRemainderGeometry.assignmentMass k b).toReal * q.N k ^ (-q.f q.L) := by
  intro ε hε
  have hexp := a.terminal_exponent_le hp
  filter_upwards [a.ratio_band ε hε] with k hk b
  have hNk : 0 < q.N k := by linarith [a.raw_valid.1 k]
  have hN1 : 1 ≤ q.N k := by linarith [a.raw_valid.1 k]
  have hm := (a.toRemainderGeometry.assignmentMass_bounds hp k b).1
  have hpow : q.N k ^ (-p.f p.L) * a.toRemainderGeometry.densityRatio k b ≤
      q.N k ^ ε * q.N k ^ (-q.f q.L) := by
    calc
      _ ≤ q.N k ^ (-p.f p.L) * q.N k ^ (a.ratio_exponent + ε) :=
        mul_le_mul_of_nonneg_left (hk b).2 (Real.rpow_nonneg hNk.le _)
      _ = q.N k ^ (-p.f p.L + (a.ratio_exponent + ε)) := (Real.rpow_add hNk _ _).symm
      _ ≤ q.N k ^ (ε + -q.f q.L) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = _ := Real.rpow_add hNk _ _
  rw [← a.same_base k]
  calc
    _ = (q.N k ^ (-p.f p.L) * a.toRemainderGeometry.densityRatio k b) *
        (a.toRemainderGeometry.assignmentMass k b).toReal := by
      unfold RemainderGeometry.densityRatio
      field_simp [hm.ne']
    _ ≤ (q.N k ^ ε * q.N k ^ (-q.f q.L)) *
        (a.toRemainderGeometry.assignmentMass k b).toReal :=
      mul_le_mul_of_nonneg_right hpow hm.le
    _ = _ := by ring

structure CalibratedPureRemainder (p q : Data) (r h w : ℝ)
    extends RemainderGeometry p q r h w where
  homogeneous : PureHomogeneous q
  terminal_calibration : ∀ k b,
    p.N (φ k) ^ (-p.f p.L) * |Matrix.det ((parent k).Q (worlds k b))| ≤
      κ k * (p.ν (φ k) ((parent k).γ (worlds k b)) ((parent k).A (worlds k b))).toReal *
        q.N k ^ (-q.f q.L)

theorem HomogeneousRemainder.calibrate {p q : Data} {r h w : ℝ}
    (a : HomogeneousRemainder p q r h w) (hp : Valid p) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Nonempty (CalibratedPureRemainder p (q.reindex ψ) r h w) := by
  obtain ⟨ψ, error, hψ, he0, he1, het, hP⟩ := vanishing_error_subsequence
    (fun ε k => a.κ k ≤ q.N k ^ ε ∧ a.error k ≤ ε ∧ ∀ b,
      p.N (a.φ k) ^ (-p.f p.L) * |Matrix.det ((a.parent k).Q (a.worlds k b))| ≤
        q.N k ^ ε * (a.toRemainderGeometry.assignmentMass k b).toReal * q.N k ^ (-q.f q.L))
    (fun ε hε => by
      filter_upwards [(a.toRemainderGeometry.slack_subpower hp).2 ε hε,
        a.error_limit.eventually (gt_mem_nhds hε), a.eventual_terminal_calibration hp ε hε]
        with k hκ he hc
      exact ⟨hκ, he.le, hc⟩)
  let κ : ℕ → ℝ := fun k => q.N (ψ k) ^ error k
  let geom := (a.toRemainderGeometry.reindex hψ).enlarge hp κ error
    (fun k => (hP k).1) (fun k => (hP k).2.1) he0 he1 het (fun _ => le_rfl)
  refine ⟨ψ, hψ, ⟨{
    toRemainderGeometry := geom
    homogeneous := a.homogeneous.reindex hψ
    terminal_calibration := ?_ }⟩⟩
  intro k b
  exact (hP k).2.2 b

theorem RawRemainder.calibrated_pure_preparation {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (hp : Valid p) :
    ∃ q₀ : Data, Nonempty (CalibratedPureRemainder p q₀ r h w) := by
  obtain ⟨q₁, ⟨a₁⟩⟩ := a.pure_preparation hp
  obtain ⟨ψ, hψ, ha⟩ := a₁.calibrate hp
  exact ⟨q₁.reindex ψ, ha⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
