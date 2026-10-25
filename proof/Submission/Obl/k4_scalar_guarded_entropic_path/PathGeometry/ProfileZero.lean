/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ProfileZero.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.WorldMeasure
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.MarginalBounds
import Submission.Obl.k4_profile_density_bounds.Mass
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
The absolute pure profile at depth zero is nonpositive. The observation
of the original coefficient support has subpower reference volume, while
the original selected mixture has inverse-subpower mass.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

namespace ProfileZero

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_pure_multiworld_homogenization
open Submission.Obl.k4_native_grid_profile_extension.Profiles

def observationSupport (K : ℝ) : Set Observation :=
  box 2 (3 * K) ×ˢ
    (Submission.Obl.k4_native_base_flattening.cubeBins (3 * K) 1 : Set ℤ)

theorem measurable_observationSupport (K : ℝ) :
    MeasurableSet (observationSupport K) :=
  measurableSet_Icc.prod (Finset.measurableSet _)

theorem reference_observationSupport_le {K : ℝ} (hK : 1 ≤ K) :
    reference (observationSupport K) ≤ ENNReal.ofReal (396 * K ^ 3) := by
  have hK0 : 0 ≤ K := by linarith
  unfold observationSupport
  rw [Measure.prod_prod, volume_box 2 (by positivity), Measure.count_apply_finset]
  calc
    _ ≤ ENNReal.ofReal ((2 * (3 * K)) ^ 2) *
        ENNReal.ofReal (2 * (3 * K) / 1 + 5) := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal
        (Submission.Obl.k4_native_base_flattening.card_cubeBins_le
          (by positivity) (by norm_num))
    _ = ENNReal.ofReal ((2 * (3 * K)) ^ 2 * (2 * (3 * K) / 1 + 5)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h : 2 * (3 * K) / 1 + 5 ≤ 11 * K := by linarith
      calc
        _ ≤ (2 * (3 * K)) ^ 2 * (11 * K) := by gcongr
        _ = 396 * K ^ 3 := by ring

theorem mem_observationSupport {N K : ℝ} (hK : 1 ≤ K)
    {z : Incidence} (ht : z.2 ∈ Icc (0 : ℝ) 1)
    (hl : ∀ e, |z.1.2 e| ≤ K) :
    observe N 0 z ∈ observationSupport K := by
  have hK0 : 0 ≤ K := by linarith
  have ht0 : |z.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have ht2 : |z.2 ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) ht0
  have hy : |y z.1 z.2| ≤ 2 * K := by
    calc
      _ ≤ |z.1.2 0| + |z.2| * |z.1.2 1| := by
        simpa only [y, abs_mul] using abs_add_le (z.1.2 0) (z.2 * z.1.2 1)
      _ ≤ K + 1 * K := by gcongr <;> exact hl _
      _ = _ := by ring
  have hx : |x z.1 z.2| ≤ 3 * K := by
    change |z.1.2 2 + z.2 * z.1.2 3 + z.2 ^ 2 * z.1.2 4| ≤ 3 * K
    calc
      _ ≤ |z.1.2 2 + z.2 * z.1.2 3| + |z.2 ^ 2 * z.1.2 4| := abs_add_le _ _
      _ ≤ (|z.1.2 2| + |z.2 * z.1.2 3|) + |z.2 ^ 2 * z.1.2 4| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = |z.1.2 2| + |z.2| * |z.1.2 3| + |z.2 ^ 2| * |z.1.2 4| := by
        rw [abs_mul, abs_mul]
      _ ≤ K + 1 * K + 1 * K := by gcongr <;> exact hl _
      _ = _ := by ring
  change (![z.2, y z.1 z.2] : Fin 2 → ℝ) ∈ box 2 (3 * K) ∧
    ⌊x z.1 z.2 / N ^ (-(0 : ℝ))⌋ ∈
      (Submission.Obl.k4_native_base_flattening.cubeBins (3 * K) 1 : Set ℤ)
  constructor
  · constructor <;> intro i <;> fin_cases i
    · change -(3 * K) ≤ z.2
      linarith [ht.1]
    · change -(3 * K) ≤ y z.1 z.2
      linarith [(abs_le.mp hy).1]
    · change z.2 ≤ 3 * K
      linarith [ht.2]
    · change y z.1 z.2 ≤ 3 * K
      linarith [(abs_le.mp hy).2]
  · change ⌊x z.1 z.2 / N ^ (-(0 : ℝ))⌋ ∈
      Submission.Obl.k4_native_base_flattening.cubeBins (3 * K) 1
    simpa only [neg_zero, Real.rpow_zero] using
      Submission.Obl.k4_native_base_flattening.mem_cubeBins (by norm_num : (0 : ℝ) < 1) hx

theorem ae_observationSupport {p : Problem} (hp : RawScalar p)
    (k : ℕ) (a : Fin (p.1 k)) :
    ∀ᵐ z ∂law p k a, observe (resolution p k) 0 z ∈ observationSupport (loss p k) := by
  have ha := (hp.2 k).2.2.2.1 a
  let := ha.1
  have hm : MeasurableSet {z : Incidence | ∀ e, |z.1.2 e| ≤ loss p k} :=
    by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun e : Fin 5 =>
        measurableSet_le (show Measurable (fun z : Incidence => |z.1.2 e|) by fun_prop)
          measurable_const
  have hcoef : ∀ᵐ z ∂(prior p k a).prod (volume : Measure ℝ),
      ∀ e, |z.1.2 e| ≤ loss p k := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [ha.2.2.1] with l hl
    exact Eventually.of_forall fun _ => hl
  filter_upwards [ae_restrict_of_ae hcoef, ae_restrict_mem ha.2.2.2.1] with z hz hE
  exact mem_observationSupport (hp.1.2.2.1.1 k) (ha.2.2.2.2.1 hE).2 hz

/-- A pointwise bound on the zero-depth density pays only a polynomial in
original coefficient support, independently of the number of worlds. -/
theorem mass_le_zero_density {p : Problem} (hp : RawScalar p)
    (hd : HasDensities p) (k : ℕ) (b : ENNReal) :
    worldLaw p k univ ≤ b * ENNReal.ofReal (396 * loss p k ^ 3) +
      ∑ a, ENNReal.ofReal (weight p k a) * law p k a
        {z | b < density p k a 0 (observe (resolution p k) 0 z)} := by
  have hL : 0 ≤ length p := hp.1.2.2.2.2.2.1.le
  have hobs : Measurable (observe (resolution p k) 0) :=
    Submission.Obl.k4_scalar_grid_density_extension.measurable_obs_label _ _
  have hsum : (∑ a, ENNReal.ofReal (weight p k a)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hp.2 k).2.1 a),
      (hp.2 k).2.2.1, ENNReal.ofReal_one]
  rw [worldLaw_univ]
  calc
    _ ≤ ∑ a, ENNReal.ofReal (weight p k a) *
        (b * reference (observationSupport (loss p k)) + law p k a
          {z | b < density p k a 0 (observe (resolution p k) 0 z)}) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul' le_rfl
      exact Submission.Obl.k4_profile_density_bounds.mass_le_density_times_support
        (law p k a) reference hobs (hd k a 0 le_rfl hL).1
        (hd k a 0 le_rfl hL).2 (measurable_observationSupport _)
        (ae_observationSupport hp k a) b
    _ = b * reference (observationSupport (loss p k)) + _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := by
      gcongr
      exact reference_observationSupport_le (hp.1.2.2.1.1 k)

/-- The depth-zero profile of any raw scalar system with a pure profile
is nonpositive; no normalization of its absolute profile is assumed. -/
theorem profile_zero_le {p : Problem} (hp : RawScalar p) (hf : PureProfile p) :
    profile p 0 ≤ 0 := by
  by_contra! hfpos
  let τ : ℝ := profile p 0 / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let A : ℕ → ENNReal := fun k => ENNReal.ofReal
    (396 * resolution p k ^ (-(profile p 0 / 4)))
  have hA : IsPowerSmall (resolution p) A :=
    Submission.Obl.k4_scalar_grid_density_extension.isPowerSmall_of_le_const_mul
      (resolution p) hp.1.2.1 396 (profile p 0 / 4) (by positivity) _
      (Eventually.of_forall fun _ => le_rfl)
  let bad : ℕ → ENNReal := fun k => ∑ a, ENNReal.ofReal (weight p k a) * law p k a
    {z | density p k a 0 (observe (resolution p k) 0 z) <
        ENNReal.ofReal (resolution p k ^ (-profile p 0 - τ)) ∨
      ENNReal.ofReal (resolution p k ^ (-profile p 0 + τ)) <
        density p k a 0 (observe (resolution p k) 0 z)}
  have hbad : IsPowerSmall (resolution p) bad :=
    hf.2.2 0 τ le_rfl hp.1.2.2.2.2.2.1.le hτ
  have hpow := Submission.Obl.k4_profile_density_bounds.eventually_subpower_pow_le
    (fun k => (show (1 : ℝ) ≤ 2 by norm_num).trans (hp.1.1 k))
    hp.1.2.2.1.1 hp.1.2.2.1.2 3 (show 0 < profile p 0 / 4 by positivity)
  have hsmall : IsPowerSmall (resolution p) (fun k => worldLaw p k univ) := by
    apply (hA.add hp.1.2.1 hbad).mono
    filter_upwards [hpow] with k hk
    refine (mass_le_zero_density hp hf.1 k
      (ENNReal.ofReal (resolution p k ^ (-profile p 0 + τ)))).trans ?_
    apply add_le_add
    · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hp.1.1 k]) _)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ resolution p k ^ (-profile p 0 + τ) *
            (396 * resolution p k ^ (profile p 0 / 4)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (by norm_num))
            (Real.rpow_nonneg (by linarith [hp.1.1 k]) _)
        _ = _ := by
          rw [mul_left_comm, ← Real.rpow_add (by linarith [hp.1.1 k])]
          congr 2
          dsimp [τ]
          ring
    · apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul' le_rfl (measure_mono (fun _ hz => Or.inr hz))
  exact not_isPowerSmall_of_inverse_subpower hp.1.2.1
    (worldLaw_inverse_subpower hp) hsmall

end ProfileZero

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The sign estimate applies directly to the literal frozen exact data. -/
theorem exact_profile_zero_le {p : Code} (hp : Exact p) : f p 0 ≤ 0 := by
  apply ProfileZero.profile_zero_le (p := p)
  · exact ⟨hp.1, hp.2.1⟩
  · exact ⟨hp.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
