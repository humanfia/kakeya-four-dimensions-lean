-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.CorePowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Fixed powers of the core envelope below `K` (session x1088, for x1082's final sample).

* `pow_le_of_pow_le`, `const_mul_pow_le_rpow`: a smaller power of `X ≥ 1` (times a constant `c`)
  stays below `N^f` once `X^P ≤ N^e` and `c ≤ N^(f - e)`.
* `hcount_le`: samplePost's `hcount`, `(Kcore^10 (2 Kcore^(3R+18))) 9^3 ≤ N^f`, from
  `Kcore^P ≤ N^e`, `3R + 28 ≤ P` and `1458 ≤ N^(f - e)`.
* `hcount_native` / `eventually_hcount_native`: the same for the literal core envelope
  `Kcore = nativePreGeometryEnvelope κ source N tolerance` and `R = coreRadius`, from x1095's
  `FixedSourcePowers.native_envelope_power` (`Kcore^power ≤ N^(budget/256)`,
  `3 coreRadius + 28 ≤ power`), at any `f > budget/256` (e.g. `f = loss gain L/(Ep+1)` when
  `budget ≤ f`).
* `Kc_le_mk4Kg`, `le_K_of_brow`: the census constant is below the MK4 row constant
  (`8 Cband ≥ 1`, `c ≤ 1`), hence below `K` once `Brow = 28 Kg^6 ≤ K`; `one_le_cband` is
  `8 Cband ≥ 1` for root_slice_full's literal `Cband`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4Numerics

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- A smaller power of `X ≥ 1`. -/
theorem pow_le_of_pow_le {X B : ℝ} {n P : ℕ} (hX : 1 ≤ X) (hn : n ≤ P) (hP : X ^ P ≤ B) :
    X ^ n ≤ B :=
  (pow_le_pow_right₀ hX hn).trans hP

/-- **A constant times a smaller power below `N^f`.** -/
theorem const_mul_pow_le_rpow {X N c e f : ℝ} {n P : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hn : n ≤ P) (hP : X ^ P ≤ N ^ e) (hc0 : 0 ≤ c) (hc : c ≤ N ^ (f - e)) :
    c * X ^ n ≤ N ^ f := by
  have hNp : 0 < N := by linarith
  calc c * X ^ n ≤ N ^ (f - e) * N ^ e :=
        mul_le_mul hc (pow_le_of_pow_le hX hn hP) (by positivity) (by positivity)
    _ = N ^ f := by rw [← Real.rpow_add hNp]; ring_nf

/-- **samplePost's `hcount`** from a power bound of the core constant. -/
theorem hcount_le {Kcore N e f : ℝ} {R P : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ Kcore)
    (hP : 3 * R + 28 ≤ P) (hpow : Kcore ^ P ≤ N ^ e) (hc : 1458 ≤ N ^ (f - e)) :
    (Kcore ^ 10 * (2 * Kcore ^ (3 * R + 18))) * 9 ^ 3 ≤ N ^ f := by
  have e1 : (Kcore ^ 10 * (2 * Kcore ^ (3 * R + 18))) * 9 ^ 3 =
      1458 * Kcore ^ (3 * R + 28) := by ring
  rw [e1]
  exact const_mul_pow_le_rpow hN hK hP hpow (by norm_num) hc

/-- The fixed reserve pays `3 coreRadius + 28`. -/
theorem coreRadius_count_le_power :
    3 * FixedSourcePowers.coreRadius + 28 ≤ FixedSourcePowers.power := by
  have hJ := FixedSourcePowers.jet_positive
  unfold FixedSourcePowers.power
  nlinarith

/-- **`hcount` for the literal core envelope.** -/
theorem hcount_native {N κ source tolerance budget f : ℝ}
    (hN : 1 ≤ N) (hκone : 1 ≤ κ) (hbudget : 0 < budget)
    (hκ : κ ≤ N ^ (budget / FixedSourcePowers.slack))
    (hsource : source ≤ N ^ (budget / FixedSourcePowers.slack))
    (hconstant : 2304 ≤ N ^ (budget / FixedSourcePowers.slack))
    (htol0 : 0 ≤ tolerance) (htolerance : tolerance ≤ 2 * budget / FixedSourcePowers.slack)
    (hf : 1458 ≤ N ^ (f - budget / 256)) :
    (Parent.ParentSource.Native.nativePreGeometryEnvelope κ source N tolerance ^ 10 *
        (2 * Parent.ParentSource.Native.nativePreGeometryEnvelope κ source N tolerance ^
          (3 * FixedSourcePowers.coreRadius + 18))) * 9 ^ 3 ≤ N ^ f := by
  have hK1 : 1 ≤ Parent.ParentSource.Native.nativePreGeometryEnvelope κ source N tolerance :=
    (by norm_num : (1 : ℝ) ≤ 2304).trans
      (Parent.ParentSource.Native.native_pre_geometry_envelope_bounds hκone hN htol0).1
  exact hcount_le hN hK1 coreRadius_count_le_power
    (FixedSourcePowers.native_envelope_power hN hκone hbudget hκ hsource hconstant htolerance) hf

/-- **`hcount` for the literal core envelope, eventually**, at any exponent `f > budget/256`. -/
theorem eventually_hcount_native (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {budget f : ℝ} (hbudget : 0 < budget) (hf : budget / 256 < f) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ N k ^ σ → source ≤ N k ^ σ → 0 ≤ tolerance →
        tolerance ≤ 2 * budget / FixedSourcePowers.slack →
        (Parent.ParentSource.Native.nativePreGeometryEnvelope κ source (N k) tolerance ^ 10 *
            (2 * Parent.ParentSource.Native.nativePreGeometryEnvelope κ source (N k) tolerance ^
              (3 * FixedSourcePowers.coreRadius + 18))) * 9 ^ 3 ≤ N k ^ f := by
  have hs := FixedSourcePowers.slack_positive
  have hbs : 0 < budget / FixedSourcePowers.slack := div_pos hbudget hs
  refine ⟨min 1 (budget / FixedSourcePowers.slack), lt_min one_pos hbs, min_le_left _ _, ?_⟩
  have hNlarge : ∀ᶠ k in atTop, 1 ≤ N k := hN.eventually (eventually_ge_atTop 1)
  have hconstant : ∀ᶠ k in atTop, 2304 ≤ N k ^ (budget / FixedSourcePowers.slack) :=
    ((tendsto_rpow_atTop hbs).comp hN).eventually (eventually_ge_atTop 2304)
  have hlarge : ∀ᶠ k in atTop, 1458 ≤ N k ^ (f - budget / 256) :=
    ((tendsto_rpow_atTop (by linarith : 0 < f - budget / 256)).comp hN).eventually
      (eventually_ge_atTop 1458)
  filter_upwards [hNlarge, hconstant, hlarge] with k hk hc hl
  intro κ source tolerance hκone hκ hsource htol0 htol
  have hp : N k ^ min 1 (budget / FixedSourcePowers.slack) ≤
      N k ^ (budget / FixedSourcePowers.slack) :=
    Real.rpow_le_rpow_of_exponent_le hk (min_le_right _ _)
  exact hcount_native hk hκone hbudget (hκ.trans hp) (hsource.trans hp) hc htol0 htol hl

/-- **The census constant is below the MK4 row constant.** -/
theorem Kc_le_mk4Kg {κ Vmax Kc Cband c frontRadius δL N : ℝ} (hKc : 1 ≤ Kc)
    (hCband : 1 ≤ 8 * Cband) (hc : 0 < c) (hc1 : c ≤ 1) :
    Kc ≤ mk4Kg κ Vmax Kc Cband c frontRadius δL N := by
  have h2s : (1 : ℝ) ≤ (2 : ℝ) ^ stepsOf Kc := one_le_pow₀ (by norm_num)
  have h3 : (1 : ℝ) ≤ ((2 : ℝ) ^ stepsOf Kc) ^ 3 := one_le_pow₀ h2s
  have hKc0 : 0 ≤ Kc := by linarith
  have hterm : Kc ≤ 8 * Cband * (Kc * ((2 : ℝ) ^ stepsOf Kc) ^ 3) / c := by
    rw [le_div_iff₀ hc]
    calc Kc * c ≤ Kc * 1 := mul_le_mul_of_nonneg_left hc1 hKc0
      _ = 1 * (Kc * 1) := by ring
      _ ≤ 8 * Cband * (Kc * ((2 : ℝ) ^ stepsOf Kc) ^ 3) :=
          mul_le_mul hCband (mul_le_mul_of_nonneg_left h3 hKc0) (by positivity) (by linarith)
  unfold mk4Kg
  exact hterm.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- **Below `Kg`, below `K`** once `Brow = 28 Kg^6 ≤ K`. -/
theorem le_K_of_brow {X Kg K : ℝ} (hX : X ≤ Kg) (hKg : 1 ≤ Kg) (hBrow : 28 * Kg ^ 6 ≤ K) :
    X ≤ K := by
  have h6 : Kg ≤ Kg ^ 6 := le_self_pow₀ hKg (by norm_num)
  have h0 : 0 ≤ Kg ^ 6 := by positivity
  linarith

/-- root_slice_full's literal band constant has `8 Cband ≥ 1`. -/
theorem one_le_cband {κ Kd dimension N x : ℝ} (hκ : 1 ≤ κ) (hdim : 0 ≤ dimension) (hN : 1 ≤ N)
    (hx : 0 ≤ x) :
    1 ≤ 8 * (64 * (max κ Kd) ^ 2 * κ * 4 ^ dimension * N ^ x) := by
  have hmax : 1 ≤ max κ Kd := hκ.trans (le_max_left _ _)
  have h1 : 1 ≤ (max κ Kd) ^ 2 := one_le_pow₀ hmax
  have h2 : (1 : ℝ) ≤ 4 ^ dimension := Real.one_le_rpow (by norm_num) hdim
  have h3 : 1 ≤ N ^ x := Real.one_le_rpow hN hx
  have h12 : 1 ≤ (max κ Kd) ^ 2 * κ := one_le_mul_of_one_le_of_one_le h1 hκ
  have h123 : 1 ≤ (max κ Kd) ^ 2 * κ * 4 ^ dimension := one_le_mul_of_one_le_of_one_le h12 h2
  have h1234 : 1 ≤ (max κ Kd) ^ 2 * κ * 4 ^ dimension * N ^ x :=
    one_le_mul_of_one_le_of_one_le h123 h3
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
