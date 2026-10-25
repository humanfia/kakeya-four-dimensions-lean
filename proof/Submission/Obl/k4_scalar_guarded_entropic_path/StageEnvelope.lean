import Submission.Obl.k4_scalar_guarded_entropic_path.PowerAllowance

/-! Close the scalar numerical budgets after geometry and fixed-complexity
guards have selected a sufficiently small positive power envelope. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open Filter
open scoped Topology ENNReal

/-- The original mass reserve follows from any inverse-subpower retained
mass, with the fixed factor four absorbed before the final sample. -/
theorem power_envelope_mass_reserve {N v : ℝ} (hN : 0 < N)
    (hfour : 4 ≤ N ^ (v / 2)) {mass : ℝ≥0∞}
    (hmass : ENNReal.ofReal (N ^ (-(v / 2))) ≤ mass) :
    ENNReal.ofReal (2 * (N ^ v)⁻¹) ≤ ENNReal.ofReal (1 / 2 : ℝ) * mass := by
  have hscalar : 2 / N ^ v ≤ (1 / 2 : ℝ) * N ^ (-(v / 2)) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hN _)).2
    calc
      2 ≤ (1 / 2 : ℝ) * N ^ (v / 2) := by linarith only [hfour]
      _ = ((1 / 2 : ℝ) * N ^ (-(v / 2))) * N ^ v := by
        rw [mul_assoc, ← Real.rpow_add hN]
        congr 2
        ring
  calc
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * N ^ (-(v / 2))) :=
      ENNReal.ofReal_le_ofReal (by simpa only [div_eq_mul_inv] using hscalar)
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (N ^ (-(v / 2))) :=
      ENNReal.ofReal_mul (by norm_num)
    _ ≤ _ := mul_le_mul' le_rfl hmass

/-- Finite-stage numerical fields for `H=N₀^v`, `B=(N₀^scale)^δ`. -/
structure PowerEnvelope (N₀ K : ℝ) (mass : ℝ≥0∞) (k count M : ℕ) (scale v δ : ℝ) : Prop where
  H_two : 2 ≤ N₀ ^ v
  K_le : K ≤ N₀ ^ v
  count_le : (count : ℝ) ≤ N₀ ^ v
  H_format : N₀ ^ v ≤ N₀ ^ (M : ℝ)
  H_B : N₀ ^ v ≤ N₀ ^ (scale * δ)
  B_one : 1 ≤ N₀ ^ (scale * δ)
  B_le : N₀ ^ (scale * δ) ≤ (N₀ ^ scale) ^ δ
  resolution : (k : ℝ) + 2 ≤ N₀ ^ scale
  actual : (N₀ ^ v * Real.log N₀) ^ (k + 1) ≤ (N₀ ^ scale) ^ δ
  mass_reserve : ENNReal.ofReal (2 * (N₀ ^ v)⁻¹) ≤ ENNReal.ofReal (1 / 2 : ℝ) * mass

/-- Complexity and the power exponent are fixed before choosing this
single inner sample. All scalar stage budgets then hold on one tail. -/
theorem eventually_powerEnvelope (N K : ℕ → ℝ) (hN : ∀ j, 2 ≤ N j)
    (hNt : Tendsto N atTop atTop)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, K j ≤ N j ^ ε)
    (mass : ℕ → ℝ≥0∞)
    (hmass : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ENNReal.ofReal (N j ^ (-ε)) ≤ mass j)
    (k count M : ℕ) (hM : 1 ≤ M) {scale v δ : ℝ}
    (hscale : 0 < scale) (hv : 0 < v) (hv1 : v ≤ 1) (hδ : 0 < δ)
    (hbudget : ((k + 1 : ℕ) : ℝ) * v < scale * δ) :
    ∀ᶠ j in atTop, PowerEnvelope (N j) (K j) (mass j) k count M scale v δ := by
  have hH := ((tendsto_rpow_atTop hv).comp hNt).eventually_ge_atTop (max 2 (count : ℝ))
  have hfour := ((tendsto_rpow_atTop (half_pos hv)).comp hNt).eventually_ge_atTop 4
  have hres := ((tendsto_rpow_atTop hscale).comp hNt).eventually_ge_atTop ((k : ℝ) + 2)
  have hactual := eventually_power_allowance_le N hNt (k + 1) hbudget
  have hvB : v ≤ scale * δ := by
    have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith only [hk, hv, hbudget]
  have hvM : v ≤ (M : ℝ) := hv1.trans (by exact_mod_cast hM)
  filter_upwards [hH, hfour, hres, hactual, hK v hv, hmass (v / 2) (half_pos hv)]
    with j hHj hfourj hresj hactualj hKj hmassj
  have hN1 : 1 ≤ N j := (by norm_num : (1 : ℝ) ≤ 2).trans (hN j)
  have hN0 : 0 < N j := zero_lt_one.trans_le hN1
  have hB : N j ^ (scale * δ) = (N j ^ scale) ^ δ :=
    Real.rpow_mul hN0.le scale δ
  refine ⟨(le_max_left _ _).trans hHj, hKj, (le_max_right _ _).trans hHj,
    Real.rpow_le_rpow_of_exponent_le hN1 hvM,
    Real.rpow_le_rpow_of_exponent_le hN1 hvB,
    Real.one_le_rpow hN1 (mul_nonneg hscale.le hδ.le), hB.le, hresj, ?_,
    power_envelope_mass_reserve hN0 hfourj hmassj⟩
  exact hactualj.trans_eq hB

end Submission.Obl.k4_scalar_guarded_entropic_path
