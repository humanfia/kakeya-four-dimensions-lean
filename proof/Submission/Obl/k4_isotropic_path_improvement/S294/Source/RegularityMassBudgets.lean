-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RegularityMassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateMassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The literal row-regularity factor at P=1. All finite palettes use
their original probability, so no velocity-carrier factor is added. -/
def regularityMassFactor (A : ℝ) (L : ℕ) : ENNReal :=
  ∏ _i∈Finset.range L,
    ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*A^27*((1:ℝ)^3+1)⌋₊:ℕ))

theorem regularity_mass_factor_positive {A : ℝ} (hA : 1 ≤ A) (L : ℕ) :
    0 < regularityMassFactor A L ∧ regularityMassFactor A L≠⊤ := by
  have hpower : 1 ≤ A^27 := one_le_pow₀ hA
  have harg : 1 ≤ 10^10*A^27*((1:ℝ)^3+1) := by nlinarith only [hpower]
  have hfloor : 0 < ⌊10^10*A^27*((1:ℝ)^3+1)⌋₊ := Nat.floor_pos.mpr harg
  unfold regularityMassFactor
  simp only [Finset.prod_const,Finset.card_range]
  constructor
  · positivity
  · finiteness

/-- The exact integer-floor prefactor costs one extra N^a per scale.
The regularity ratio Ar does not occur in this retention factor. -/
theorem regularity_mass_factor_le
    {N A a : ℝ} (L : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A) (hAN : A ≤ N^a)
    (hconstant : (4:ℝ)^4*7^4*(2*10^10) ≤ N^a) :
    regularityMassFactor A L ≤ ENNReal.ofReal (N^(28*a*(L:ℝ))) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hfloor : (⌊10^10*A^27*((1:ℝ)^3+1)⌋₊:ℝ) ≤ 10^10*A^27*((1:ℝ)^3+1) :=
    Nat.floor_le (by positivity)
  have hpower : A^27 ≤ N^(27*a) := by
    calc
      _ ≤ (N^a)^27 := pow_le_pow_left₀ hA0 hAN 27
      _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]; congr 1; ring
  have hreal : (4:ℝ)^4*(((7:ℕ)^4*⌊10^10*A^27*((1:ℝ)^3+1)⌋₊:ℕ):ℝ) ≤ N^(28*a) := by
    calc
      _ = (4:ℝ)^4*7^4*(⌊10^10*A^27*((1:ℝ)^3+1)⌋₊:ℝ) := by push_cast; ring
      _ ≤ (4:ℝ)^4*7^4*(10^10*A^27*((1:ℝ)^3+1)) :=
        mul_le_mul_of_nonneg_left hfloor (by positivity)
      _ = ((4:ℝ)^4*7^4*(2*10^10))*A^27 := by ring
      _ ≤ N^a*N^(27*a) := mul_le_mul hconstant hpower (pow_nonneg hA0 27)
        (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [←Real.rpow_add hNp]; congr 1; ring
  have hstep : ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*A^27*((1:ℝ)^3+1)⌋₊:ℕ)) ≤
      ENNReal.ofReal (N^(28*a)) := by
    have hh := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤4^4),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast] using hh
  unfold regularityMassFactor
  calc
    _ ≤ ∏ _i∈Finset.range L, ENNReal.ofReal (N^(28*a)) :=
      Finset.prod_le_prod (fun _i _hi => hstep)
    _ = (ENNReal.ofReal (N^(28*a)))^L := by simp
    _ = ENNReal.ofReal ((N^(28*a))^L) :=
      (ENNReal.ofReal_pow (Real.rpow_nonneg hNp.le _) L).symm
    _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hNp.le]

/-- With the grid length fixed before k, every allowed A has the same
regularity power bound after one common sample threshold. -/
theorem eventually_regularity_mass_factor_le
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (L : ℕ) {a preg : ℝ} (ha : 0 < a) (hbudget : 28*a*(L:ℝ) < preg) :
    ∀ᶠ k in atTop, ∀ A : ℝ, 1 ≤ A → A ≤ N k^a →
      0 < regularityMassFactor A L ∧ regularityMassFactor A L≠⊤ ∧
      regularityMassFactor A L ≤ ENNReal.ofReal (N k^preg) := by
  have hlarge := ((tendsto_rpow_atTop ha).comp hN).eventually
    (eventually_ge_atTop ((4:ℝ)^4*7^4*(2*10^10)))
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge] with k hk hc
  intro A hA hAN
  obtain ⟨hpos,hfin⟩ := regularity_mass_factor_positive hA L
  exact ⟨hpos,hfin,(regularity_mass_factor_le L hk hA hAN hc).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hk hbudget.le))⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
