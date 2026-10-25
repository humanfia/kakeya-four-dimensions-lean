-- Original-floor cancellation follows this LOT tree, o114, session x0707,
-- commit c63b850d, Preparation/AngularCharge.lean.
import Mathlib

namespace Submission.Obl.k4_angular_normal_pair_preparation

open scoped ENNReal BigOperators

/-- The old true floor pays for one source's unconditioned angular exception.
The determinant and both time normalizations cancel before summation. -/
theorem angular_pair_charge {q₀ q₁ n κ d geom cap : ℝ}
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hn : 0 < n) (hκ : 0 < κ)
    (hd : 0 ≤ d) (hgeom : 0 ≤ geom) (hcap : 0 ≤ cap)
    {pairMass oldMass : ENNReal}
    (hfloor : ENNReal.ofReal (n * d / (q₀ * κ)) ≤ oldMass)
    (hpair : pairMass ≤ ENNReal.ofReal (1 / q₀) *
      ENNReal.ofReal (cap * ((1 / q₁) * (geom * d)))) :
    ENNReal.ofReal q₁ * pairMass ≤
      ENNReal.ofReal (κ * geom * cap / n) * oldMass := by
  calc
    _ ≤ ENNReal.ofReal q₁ * (ENNReal.ofReal (1 / q₀) *
        ENNReal.ofReal (cap * ((1 / q₁) * (geom * d)))) := mul_le_mul' le_rfl hpair
    _ = ENNReal.ofReal (κ * geom * cap / n) *
        ENNReal.ofReal (n * d / (q₀ * κ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / q₀),
        ← ENNReal.ofReal_mul hq₁.le,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ κ * geom * cap / n)]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul' le_rfl hfloor

/-- Sum uniform source charges with the unchanged original world weights. -/
theorem weighted_pair_charge_budget {ι : Type*} [Fintype ι]
    (w m p : ι → ENNReal) (q : ℝ) (C : ENNReal)
    (hcharge : ∀ i, ENNReal.ofReal q * p i ≤ C * m i)
    (hbudget : ∑ i, w i * m i ≤ 1) :
    (∑ i, w i * ENNReal.ofReal q * p i) ≤ C := by
  calc
    _ ≤ ∑ i, w i * (C * m i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using mul_le_mul' le_rfl (hcharge i)
    _ = C * ∑ i, w i * m i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C * 1 := mul_le_mul' le_rfl hbudget
    _ = C := mul_one _

/-- The physical hidden units cancel in the native regular sublevel bound. -/
theorem native_hidden_ratio {N δ B a : ℝ} (hN : 0 < N) (hδ : δ ≠ 0) (hB : B ≠ 0) :
    (δ * N ^ a) / ((B * N ^ (-a)) * (δ / B)) = N ^ (2 * a) := by
  have hp : N ^ a ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  rw [show 2 * a = a * 2 by ring, Real.rpow_mul hN.le, Real.rpow_two,
    Real.rpow_neg hN.le]
  field_simp

-- Adapted from this LOT tree, o114, session x0707, commit c63b850d,
-- Preparation/NormalGeometryBounds.lean, transverse_velocity_ratio_le.
/-- The intersection radius of two transverse velocity strips fits inside a
fixed multiple of the actual angular bin width. -/
theorem transverse_radius_le
    {N u κ q R₁ R₂ s s' angle δu : ℝ}
    (hN : 0 < N) (hκ : 0 ≤ κ) (hq : 0 ≤ q) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hqr : q * R₁ ≤ κ) (hs : s ≤ 2 * R₂) (hs' : s' ≤ 2 * R₂)
    (hangle : (R₂ / R₁) * N ^ u ≤ angle) (hδu : N ^ (-u) ≤ δu) :
    8 * (2 * κ * q * max s s') / angle ≤ 32 * κ ^ 2 * δu := by
  have hδupos : 0 < δu := (Real.rpow_pos_of_pos hN (-u)).trans_le hδu
  have hanglepos : 0 < angle := (mul_pos (div_pos hR₂ hR₁)
    (Real.rpow_pos_of_pos hN u)).trans_le hangle
  have hcancel : N ^ (-u) * N ^ u = 1 := by rw [← Real.rpow_add hN]; simp
  have hproduct : R₂ / R₁ ≤ δu * angle := by
    calc
      R₂ / R₁ = N ^ (-u) * ((R₂ / R₁) * N ^ u) := by rw [mul_left_comm, hcancel, mul_one]
      _ ≤ δu * angle := mul_le_mul hδu hangle (by positivity)
        ((Real.rpow_pos_of_pos hN (-u)).le.trans hδu)
  apply (div_le_iff₀ hanglepos).mpr
  calc
    _ ≤ 8 * (2 * κ * q * (2 * R₂)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (max_le hs hs') (by positivity)
    _ = 32 * κ * q * R₂ := by ring
    _ ≤ 32 * κ * (κ / R₁) * R₂ := by
      have hq' : q ≤ κ / R₁ := (le_div_iff₀ hR₁).mpr hqr
      gcongr
    _ = 32 * κ ^ 2 * (R₂ / R₁) := by ring
    _ ≤ 32 * κ ^ 2 * (δu * angle) := mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by ring

/-- Spatial, hidden-bin, old-list and transverse velocity-bin factors. -/
noncomputable def nativeGeometryLoss (κ gain Z : ℝ) : ℝ :=
  Real.pi * (κ + 2 * κ * gain) ^ 2 * (16 * (1 + Z)) * κ * (128 * κ ^ 2 + 2) ^ 2

/-- The native value and derivative losses enter only through `N^(2 A e)`.
All constants and all remaining geometric factors cost at most ten powers of `N^e`. -/
theorem native_geometry_power_bound {N A e κ gain : ℝ}
    (hN : 1 ≤ N) (hA : 0 ≤ A) (he : 0 ≤ e)
    (hlarge : (2 : ℝ) ^ (32 : ℕ) ≤ N ^ e) (hκ0 : 0 ≤ κ) (hgain0 : 0 ≤ gain)
    (hκ : κ ≤ N ^ e) (hgain : gain ≤ 2 * N ^ e) :
    nativeGeometryLoss κ gain (N ^ (2 * A * e)) ≤ N ^ ((2 * A + 10) * e) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  let X := N ^ e
  let Z := N ^ (2 * A * e)
  have hX : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2 ^ (32 : ℕ)).trans hlarge
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hZ : 1 ≤ Z := Real.one_le_rpow hN (by positivity)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hspatial : κ + 2 * κ * gain ≤ 5 * X ^ 2 := by
    have hg : κ * gain ≤ X * (2 * X) := mul_le_mul hκ hgain hgain0 hX0
    have hx2 : X ≤ X ^ 2 := by nlinarith
    nlinarith
  have hhidden : 16 * (1 + Z) ≤ 32 * Z := by linarith
  have hvelocity : 128 * κ ^ 2 + 2 ≤ 130 * X ^ 2 := by
    have hκsq : κ ^ 2 ≤ X ^ 2 := by nlinarith
    have hx2 : 1 ≤ X ^ 2 := by nlinarith
    nlinarith
  have hgeom : nativeGeometryLoss κ gain Z ≤
      Real.pi * (5 * X ^ 2) ^ 2 * (32 * Z) * X * (130 * X ^ 2) ^ 2 := by
    unfold nativeGeometryLoss
    gcongr
  have hconstant : Real.pi * 25 * 32 * 130 ^ (2 : ℕ) ≤ (2 : ℝ) ^ (32 : ℕ) := by
    nlinarith [Real.pi_lt_four]
  calc
    nativeGeometryLoss κ gain (N ^ (2 * A * e)) ≤
        (Real.pi * 25 * 32 * 130 ^ (2 : ℕ)) * X ^ 9 * Z := by
      convert hgeom using 1 <;> dsimp [Z] <;> ring
    _ ≤ (2 : ℝ) ^ (32 : ℕ) * X ^ 9 * Z := by gcongr
    _ ≤ X * X ^ 9 * Z := by gcongr
    _ = N ^ ((2 * A + 10) * e) := by
      dsimp [X, Z]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0,
        ← Real.rpow_add hN0]
      congr 1
      ring

/-- A uniform angular multiplier can be fixed using only the native loss and `S`. -/
theorem normal_depth_multiplier (A S : ℝ) (hA : 0 < A) (hS : 0 < S) :
    ∃ R : ℝ, 0 < R ∧ A ≤ R ∧ 3 * A + 20 ≤ S * R := by
  refine ⟨A + 1 + (3 * A + 20) / S, by positivity, ?_, ?_⟩
  · have : 0 < (3 * A + 20) / S := by positivity
    linarith
  · have hcancel : S * ((3 * A + 20) / S) = 3 * A + 20 := by field_simp
    nlinarith [mul_pos hS hA]

/-- The angular cap beats all native geometric losses with the chosen multiplier. -/
theorem native_charge_power_bound {N A S R e κ gain fL : ℝ}
    (hN : 1 ≤ N) (hA : 0 ≤ A) (he : 0 ≤ e)
    (hlarge : (2 : ℝ) ^ (32 : ℕ) ≤ N ^ e) (hκ0 : 0 ≤ κ) (hgain0 : 0 ≤ gain)
    (hκ : κ ≤ N ^ e) (hgain : gain ≤ 2 * N ^ e) (hR : 3 * A + 20 ≤ S * R) :
    κ * nativeGeometryLoss κ gain (N ^ (2 * A * e)) *
      N ^ (-fL - S * (R * e) + A * e) / N ^ (-fL) ≤ N ^ (-(2 : ℝ) * e) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hgeom := native_geometry_power_bound hN hA he hlarge hκ0 hgain0 hκ hgain
  have hgeom0 : 0 ≤ nativeGeometryLoss κ gain (N ^ (2 * A * e)) := by
    unfold nativeGeometryLoss
    positivity
  calc
    _ ≤ N ^ e * N ^ ((2 * A + 10) * e) *
        N ^ (-fL - S * (R * e) + A * e) / N ^ (-fL) := by gcongr
    _ = N ^ ((3 * A + 11 - S * R) * e) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
      congr 1
      ring
    _ ≤ N ^ (-(2 : ℝ) * e) := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)

/-- The finite sum of the native normal exceptions fits the pair-deletion budget. -/
theorem native_exception_budget {ι : Type*} [Fintype ι]
    (w oldMass pairMass : ι → ENNReal) (d : ι → ℝ)
    {q₀ q₁ N A S R e κ gain fL : ℝ}
    (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hN : 1 ≤ N) (hA : 0 ≤ A) (he : 0 ≤ e)
    (hlarge : (2 : ℝ) ^ (32 : ℕ) ≤ N ^ e) (hκ0 : 0 < κ) (hgain0 : 0 ≤ gain)
    (hκ : κ ≤ N ^ e) (hgain : gain ≤ 2 * N ^ e) (hR : 3 * A + 20 ≤ S * R)
    (hd : ∀ i, 0 ≤ d i)
    (hfloor : ∀ i, ENNReal.ofReal (N ^ (-fL) * d i / (q₀ * κ)) ≤ oldMass i)
    (hpair : ∀ i, pairMass i ≤ ENNReal.ofReal (1 / q₀) *
      ENNReal.ofReal (N ^ (-fL - S * (R * e) + A * e) *
        ((1 / q₁) * (nativeGeometryLoss κ gain (N ^ (2 * A * e)) * d i))))
    (hbudget : ∑ i, w i * oldMass i ≤ 1) :
    (∑ i, w i * ENNReal.ofReal q₁ * pairMass i) ≤ ENNReal.ofReal (4 * κ⁻¹) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hgeom0 : 0 ≤ nativeGeometryLoss κ gain (N ^ (2 * A * e)) := by
    unfold nativeGeometryLoss
    positivity
  have hcharge i := angular_pair_charge hq₀ hq₁ (Real.rpow_pos_of_pos hN0 _) hκ0
    (hd i) hgeom0 (Real.rpow_nonneg hN0.le _) (hfloor i) (hpair i)
  apply (weighted_pair_charge_budget w oldMass pairMass q₁ _ hcharge hbudget).trans
  apply ENNReal.ofReal_le_ofReal
  apply (native_charge_power_bound hN hA he hlarge hκ0.le hgain0 hκ hgain hR).trans
  have hX : 1 ≤ N ^ e := (by norm_num : (1 : ℝ) ≤ 2 ^ (32 : ℕ)).trans hlarge
  have hκsq : κ ≤ (N ^ e) ^ (2 : ℕ) := by nlinarith
  have hpow : N ^ (-(2 : ℝ) * e) = ((N ^ e) ^ (2 : ℕ))⁻¹ := by
    rw [show -(2 : ℝ) * e = -(e * 2) by ring, Real.rpow_neg hN0.le,
      Real.rpow_mul hN0.le, Real.rpow_two]
  rw [hpow]
  have hinv : ((N ^ e) ^ (2 : ℕ))⁻¹ ≤ κ⁻¹ := by
    exact (inv_le_inv₀ (by positivity) hκ0).mpr hκsq
  have hκinv : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ0.le
  linarith

end Submission.Obl.k4_angular_normal_pair_preparation
