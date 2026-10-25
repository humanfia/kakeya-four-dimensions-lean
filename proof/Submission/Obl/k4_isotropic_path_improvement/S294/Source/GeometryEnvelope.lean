-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.GeometryEnvelope, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.InternalEntropyBudget

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.ParentSource

noncomputable section

/-- The grid tolerance fits a deterministic record-geometry envelope
at the small internal allowance. The counting envelope need not pay
the fixed grid error, so the arbitrary late front budget stays free. -/
theorem grid_error_fits_record_geometry_envelope
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    {κ₁ d₁ precision loss gain L δ₀ divisor : ℝ} {Ep : ℕ}
    (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L) (hδ0 : 0 ≤ δ₀)
    (hdivisor : 0 < divisor) (hdivisorMax : divisor ≤ 5000)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    2*δ₀*L ≤ (tune.budget κ₁ d₁ Ep precision loss*
      (loss*gain*L/((Ep:ℝ)+1))/divisor)/(256*(FixedSourcePowers.power:ℝ)) := by
  have hs : 0 < tune.slack := zero_lt_one.trans_le tune.one_le_slack
  have hB := tune.budget_pos κ₁ d₁ Ep precision loss
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  have hpNat : 0 < FixedSourcePowers.power := by unfold FixedSourcePowers.power; omega
  have hp : 0 < (FixedSourcePowers.power:ℝ) := Nat.cast_pos.mpr hpNat
  let amplitude := tune.budget κ₁ d₁ Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))
  have hamp : 0 < amplitude := by dsimp only [amplitude]; positivity
  have hδL : δ₀*L*tune.slack ≤ amplitude/10000 := by
    have hh := mul_le_mul_of_nonneg_right hδ (by positivity : (0:ℝ)≤L*tune.slack)
    have heq : tolOf tune κ₁ d₁ Ep precision loss gain*(L*tune.slack)=amplitude/10000 := by
      dsimp only [tolOf,amplitude]
      field_simp
    nlinarith only [hh,heq]
  have hcost : 2*δ₀*L*tune.slack ≤ amplitude/divisor := by
    calc
      _ ≤ amplitude/5000 := by linarith only [hδL]
      _ ≤ _ := div_le_div_of_nonneg_left hamp.le hdivisor hdivisorMax
  have hpowerSlack : 256*(FixedSourcePowers.power:ℝ) ≤ tune.slack := by
    have hh := FixedSourcePowers.slack_pays_power.trans hslack
    linarith only [hh,hp]
  rw [le_div_iff₀ (by positivity : (0:ℝ)<256*(FixedSourcePowers.power:ℝ))]
  have hh := mul_le_mul_of_nonneg_left hpowerSlack (by positivity : (0:ℝ)≤2*δ₀*L)
  exact hh.trans hcost

/-- The actual native counting envelope is below one deterministic
geometry power, uniformly in every subsequently supplied path and
source factor. The latter also pays the original frame grid error. -/
theorem eventually_native_record_geometry_envelope
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (fixedConstant : ℝ)
    {budget geometryError : ℝ} (hbudget : 0 < budget)
    (hgeometry : geometryError ≤ budget/(256*(FixedSourcePowers.power:ℝ))) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source tolerance : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        0 ≤ tolerance → tolerance ≤ 2*budget/FixedSourcePowers.slack →
        let K := Native.nativePreGeometryEnvelope κ source (N k) tolerance
        let G := N k^(budget/(256*(FixedSourcePowers.power:ℝ)))
        2304 ≤ K ∧ K ≤ G ∧ max κ source ≤ K ∧ N k^geometryError ≤ G ∧ fixedConstant ≤ G := by
  have hpNat : 0 < FixedSourcePowers.power := by unfold FixedSourcePowers.power; omega
  have hp : 0 < (FixedSourcePowers.power:ℝ) := Nat.cast_pos.mpr hpNat
  let g := budget/(256*(FixedSourcePowers.power:ℝ))
  have hg : 0 < g := by dsimp only [g]; positivity
  let sigma := min 1 (g/4)
  have hsigma : 0 < sigma := lt_min one_pos (by positivity)
  have hsigmaG : sigma ≤ g/4 := min_le_right _ _
  have htolCap : 2*budget/FixedSourcePowers.slack ≤ g/2 := by
    dsimp only [g]
    rw [div_div,div_le_div_iff₀ FixedSourcePowers.slack_positive (by positivity)]
    have hh := mul_le_mul_of_nonneg_left FixedSourcePowers.slack_pays_power hbudget.le
    nlinarith only [hh]
  have hlarge := ((tendsto_rpow_atTop (by positivity : 0 < g/4)).comp hN).eventually
    (eventually_ge_atTop 2304)
  have hfixed := ((tendsto_rpow_atTop hg).comp hN).eventually
    (eventually_ge_atTop fixedConstant)
  refine ⟨sigma,hsigma,min_le_left _ _,?_⟩
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge,hfixed] with k hk hc hfix
  intro κ source tolerance hκone hκ hsource htol0 htol
  obtain ⟨hK,hκK,hmax,hpow⟩ := Native.native_pre_geometry_envelope_bounds hκone hk htol0
  have hκG : κ ≤ N k^(g/4) := hκ.trans (Real.rpow_le_rpow_of_exponent_le hk hsigmaG)
  have hsourceG : source ≤ N k^(g/4) := hsource.trans
    (Real.rpow_le_rpow_of_exponent_le hk hsigmaG)
  have henvelope : Native.nativePreGeometryEnvelope κ source (N k) tolerance ≤ N k^g :=
    Native.native_pre_geometry_envelope_power hk hκG hsourceG hc (by linarith only [htol,htolCap])
  exact ⟨hK,henvelope,hmax,Real.rpow_le_rpow_of_exponent_le hk hgeometry,hfix⟩

/-- The actual front tolerances and grid cap produce both record and
frame envelopes. The larger deterministic power also pays any fixed
census constant, while the record count remains the actual K^12. -/
theorem eventually_sample_record_geometry_envelope
    (tune : Tuning) (hslack : FixedSourcePowers.slack ≤ tune.slack)
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (fixedConstant : ℝ)
    {κ₁ d₁ precision loss gain L δ₀ front divisor : ℝ} {Ep : ℕ}
    (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L) (hδ0 : 0 ≤ δ₀)
    (hfront : 0 < front) (hdivisor : 0 < divisor) (hdivisorMax : divisor ≤ 5000)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (htau : 0 ≤ tauOf tune δ₀ L front) :
    let internal := tune.budget κ₁ d₁ Ep precision loss*
      (loss*gain*L/((Ep:ℝ)+1))/divisor
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ source : ℝ, 1 ≤ κ → κ ≤ N k^sigma → source ≤ N k^sigma →
        let K := Native.nativePreGeometryEnvelope κ source (N k) (2*tauOf tune δ₀ L front)
        let G := N k^(internal/(256*(FixedSourcePowers.power:ℝ)))
        2304 ≤ K ∧ K ≤ G ∧ max κ source ≤ K ∧ N k^(2*δ₀*L) ≤ G ∧ fixedConstant ≤ G := by
  let internal := tune.budget κ₁ d₁ Ep precision loss*
    (loss*gain*L/((Ep:ℝ)+1))/divisor
  have hB := tune.budget_pos κ₁ d₁ Ep precision loss
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  have hinternal : 0 < internal := by dsimp only [internal]; positivity
  have hgeometry := grid_error_fits_record_geometry_envelope tune hslack
    hloss hgain hL hδ0 hdivisor hdivisorMax hδ
  have htolerance : 2*tauOf tune δ₀ L front ≤ 2*internal/FixedSourcePowers.slack := by
    have hh := doubled_tau_fits_internal_budget tune hloss hgain hL hfront hdivisor hdivisorMax hδ
    have hs : 0 ≤ tune.slack := zero_le_one.trans tune.one_le_slack
    have hmin : 2*min front internal/tune.slack ≤ 2*internal/tune.slack :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) hs
    exact hh.trans (hmin.trans (div_le_div_of_nonneg_left (by positivity)
      FixedSourcePowers.slack_positive hslack))
  obtain ⟨sigma,hsigma,hsigma1,hbudgets⟩ := eventually_native_record_geometry_envelope
    N hN fixedConstant hinternal hgeometry
  refine ⟨sigma,hsigma,hsigma1,?_⟩
  filter_upwards [hbudgets] with k hk
  intro κ source hκone hκ hsource
  exact hk κ source (2*tauOf tune δ₀ L front) hκone hκ hsource (by positivity) htolerance

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
