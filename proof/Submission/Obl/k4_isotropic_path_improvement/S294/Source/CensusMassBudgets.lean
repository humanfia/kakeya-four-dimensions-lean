-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.CensusMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.FixedSourcePowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootCensusAt
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalEntropyBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter Parent.ParentSource
open scoped ENNReal

noncomputable section

/-- Lower and upper powers of the actual counting envelope pay the
full census loss. The geometry envelope does not enter this charge. -/
theorem census_mass_cost_le
    {N κ K fraction lower upper front gap : ℝ} (P n : ℕ)
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hκN : κ ≤ N^gap) (hKlower : N^lower ≤ K) (hKupper : K^P ≤ N^upper)
    (hfraction0 : 0 ≤ fraction) (hfraction : fraction ≤ 2*N^(-front))
    (hlowerGap : gap ≤ lower) (hupperGap : upper+gap ≤ front/2)
    (hconstantLower : 512*(n:ℝ) ≤ N^lower)
    (hconstantFront : 442368*(n:ℝ) ≤ N^(front/2)) :
    ENNReal.ofReal ((n:ℝ)*(4/K^2+1728*K^P*fraction)) ≤ ENNReal.ofReal (κ⁻¹/64) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hKpow : (N^lower)^2=N^(2*lower) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]
    congr 1
    ring
  have hfirst : 4*(n:ℝ)*N^(-lower) ≤ 1/128 := by
    rw [Real.rpow_neg hNp.le,←div_eq_mul_inv,div_le_iff₀ (Real.rpow_pos_of_pos hNp _)]
    linarith only [hconstantLower]
  have hsecond : 3456*(n:ℝ)*N^(-(front/2)) ≤ 1/128 := by
    rw [Real.rpow_neg hNp.le,←div_eq_mul_inv,div_le_iff₀ (Real.rpow_pos_of_pos hNp _)]
    linarith only [hconstantFront]
  have hcost : ((n:ℝ)*(4/K^2+1728*K^P*fraction))*κ ≤ 1/64 := by
    calc
      _ ≤ ((n:ℝ)*(4/(N^lower)^2+1728*N^upper*(2*N^(-front))))*N^gap := by
        gcongr
      _ = 4*(n:ℝ)*N^(gap-2*lower)+3456*(n:ℝ)*N^(upper-front+gap) := by
        rw [hKpow,Real.rpow_sub hNp,Real.rpow_add hNp,Real.rpow_sub hNp,Real.rpow_neg hNp.le]
        ring
      _ ≤ 4*(n:ℝ)*N^(-lower)+3456*(n:ℝ)*N^(-(front/2)) := by
        gcongr
        · linarith only [hlowerGap]
        · linarith only [hupperGap]
      _ ≤ 1/64 := by linarith only [hfirst,hsecond]
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_iff_right₀ hκp).mp
  have heq : κ*(κ⁻¹/64)=1/64 := by field_simp
  rw [heq]
  simpa only [mul_comm] using hcost

/-- The literal positive native envelope supplies the lower power,
and its fixed core-power budget supplies the upper power. The tail
and path tolerance precede all actual path and source coefficients. -/
theorem eventually_native_census_mass_budget
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (m P : ℕ)
    (hP : P ≤ FixedSourcePowers.power)
    {front budget tolerance : ℝ}
    (hfront : 0 < front) (hbudget : 0 < budget) (hbudgetFront : budget ≤ front)
    (htolerance : 0 < tolerance) (htoleranceBudget : tolerance ≤ 2*budget/FixedSourcePowers.slack) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source fraction : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        0 ≤ fraction → fraction ≤ 2*N k^(-front) → ∀ n : ℕ, n ≤ m →
        let K := Native.nativePreGeometryEnvelope κ source (N k) tolerance
        ENNReal.ofReal ((n:ℝ)*(4/K^2+1728*K^P*fraction)) ≤ ENNReal.ofReal (κ⁻¹/64) := by
  obtain ⟨sigma0,hsigma0,hsigma01,henvelope⟩ :=
    FixedSourcePowers.eventually_native_envelope_power N hN hbudget
  let sigma := min sigma0 (min tolerance (front/8))
  have hsigma : 0 < sigma := lt_min hsigma0 (lt_min htolerance (by positivity))
  have hsigma0le : sigma ≤ sigma0 := min_le_left _ _
  have hsigmaLower : sigma ≤ tolerance := (min_le_right _ _).trans (min_le_left _ _)
  have hsigmaFront : sigma ≤ front/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hlargeLower := ((tendsto_rpow_atTop htolerance).comp hN).eventually
    (eventually_ge_atTop (512*(m:ℝ)))
  have hlargeFront := ((tendsto_rpow_atTop (by positivity : 0 < front/2)).comp hN).eventually
    (eventually_ge_atTop (442368*(m:ℝ)))
  refine ⟨sigma,hsigma,hsigma0le.trans hsigma01,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),henvelope,hlargeLower,hlargeFront] with k hk henv hl hf
  intro κ source fraction hκ hκN hsourceN hfr0 hfr n hnm
  have hNp : 0 < N k := zero_lt_one.trans_le hk
  have hκN0 : κ ≤ N k^sigma0 := hκN.trans
    (Real.rpow_le_rpow_of_exponent_le hk hsigma0le)
  have hsourceN0 : source ≤ N k^sigma0 := hsourceN.trans
    (Real.rpow_le_rpow_of_exponent_le hk hsigma0le)
  have hpower := henv κ source tolerance hκ hκN0 hsourceN0 htoleranceBudget
  obtain ⟨hK,hκK,hmax,hKlower⟩ := Native.native_pre_geometry_envelope_bounds hκ hk htolerance.le
  have hKone : 1 ≤ Native.nativePreGeometryEnvelope κ source (N k) tolerance :=
    (by norm_num : (1:ℝ) ≤ 2304).trans hK
  have hKupper : (Native.nativePreGeometryEnvelope κ source (N k) tolerance)^P ≤ N k^(budget/256) :=
    (pow_le_pow_right₀ hKone hP).trans hpower
  have hcast : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
  exact census_mass_cost_le P n hk hκ hKone hκN hKlower hKupper hfr0 hfr hsigmaLower
    (by linarith only [hsigmaFront,hbudgetFront,hfront])
    ((mul_le_mul_of_nonneg_left hcast (by norm_num)).trans hl)
    ((mul_le_mul_of_nonneg_left hcast (by norm_num)).trans hf)

/-- The census power is included in the fixed core reserve. -/
theorem census_mass_power_le :
    3*FixedSourcePowers.coreRadius+32 ≤ FixedSourcePowers.power := by
  have hh := Nat.mul_le_mul_left (4*FixedSourcePowers.coreRadius+100)
    FixedSourcePowers.jet_positive
  unfold FixedSourcePowers.power
  nlinarith

/-- The exact census term of `sample_final` is paid at the actual
prepared tolerance. This includes every depth in the fixed grid and
allows any larger geometry envelope chosen by the census. -/
theorem eventually_sample_census_mass_budget
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (m : ℕ)
    {κ₁ d₁ precision loss gain L δ₀ front divisor : ℝ} {Ep : ℕ}
    (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L) (hδ0 : 0 < δ₀)
    (hfront : 0 < front) (hdivisor : 0 < divisor) (hdivisorMax : divisor ≤ 5000)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source fraction : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        0 ≤ fraction → fraction ≤ 2*N k^(-front) →
        let K := Native.nativePreGeometryEnvelope κ source (N k) (2*tauOf tune δ₀ L front)
        ∀ G : ℝ, K ≤ G → ∀ n : ℕ, n ≤ m →
          (n:ENNReal)*(ENNReal.ofReal (4*K^(3*FixedSourcePowers.coreRadius+28)*κ^2)*
            (ENNReal.ofReal ((G^(rowExpOf FixedSourcePowers.coreRadius))⁻¹*
              (K^FixedSourcePowers.coreRadius)⁻¹)+
              27*(ENNReal.ofReal (16*fraction)*ENNReal.ofReal (κ^2)))) ≤
                ENNReal.ofReal (κ⁻¹/64) := by
  let internal := tune.budget κ₁ d₁ Ep precision loss*
    (loss*gain*L/((Ep:ℝ)+1))/divisor
  let budget := min front internal
  have hB := tune.budget_pos κ₁ d₁ Ep precision loss
  have hinternal : 0 < internal := by dsimp only [internal]; positivity
  have hbudget : 0 < budget := lt_min hfront hinternal
  have hbudgetFront : budget ≤ front := min_le_left _ _
  have htune : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have htau : 0 < tauOf tune δ₀ L front := by unfold tauOf; positivity
  have htol := doubled_tau_fits_internal_budget tune hloss hgain hL hfront
    hdivisor hdivisorMax hδ
  have htolBudget : 2*tauOf tune δ₀ L front ≤ 2*budget/FixedSourcePowers.slack := by
    have hh : 2*tauOf tune δ₀ L front ≤ 2*budget/tune.slack := htol
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) FixedSourcePowers.slack_positive hslack)
  obtain ⟨sigma,hsigma,hsigma1,hcost⟩ := eventually_native_census_mass_budget N hN m
    (3*FixedSourcePowers.coreRadius+32) census_mass_power_le hfront hbudget hbudgetFront
    (by positivity : 0 < 2*tauOf tune δ₀ L front) htolBudget
  refine ⟨sigma,hsigma,hsigma1,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hcost] with k hk hc
  intro κ source fraction hκ hκN hsource hfr0 hfr
  dsimp only
  intro G hKG n hnm
  obtain ⟨hK,hκK,hmax,hpow⟩ := Native.native_pre_geometry_envelope_bounds hκ hk
    (by positivity : 0 ≤ 2*tauOf tune δ₀ L front)
  have hKone : 1 ≤ Native.nativePreGeometryEnvelope κ source (N k) (2*tauOf tune δ₀ L front) :=
    (by norm_num : (1:ℝ) ≤ 2304).trans hK
  exact (census_cost_le hKone (zero_le_one.trans hκ) ((le_max_left _ _).trans hmax) hKG hfr0).trans
    (hc κ source fraction hκ hκN hsource hfr0 hfr n hnm)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
