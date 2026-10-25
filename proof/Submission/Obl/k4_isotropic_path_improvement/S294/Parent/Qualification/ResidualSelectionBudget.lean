-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ResidualSelectionBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControlRestrictions

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- A fixed-length residual selection has a polynomial cost. The exact
ceiling and residue-class factors are those of the incidence factory. -/
theorem residual_selection_factor_le {N a : ℝ} (hN : 0<N)
    (hlarge : 1024≤N^a) (L : ℕ) (complexity : ℕ → ℝ)
    (hcomplexity : ∀ i<L, 0≤complexity i ∧ complexity i≤N^a) :
    (∏ i∈Finset.range L, (4:ENNReal)^4*(⌈complexity i⌉₊+1:ℕ))≤
      ENNReal.ofReal (N^(2*a*(L:ℝ))) := by
  have hfactor (i : ℕ) (hi : i<L) :
      (4:ENNReal)^4*(⌈complexity i⌉₊+1:ℕ)≤ENNReal.ofReal (N^(2*a)) := by
    have hceil : ((⌈complexity i⌉₊+1:ℕ):ℝ)≤N^a+2 := by
      have hh := (Nat.ceil_lt_add_one (hcomplexity i hi).1).le
      simp only [Nat.cast_add,Nat.cast_one]
      linarith [(hcomplexity i hi).2]
    have hp : 0≤N^a-1024 := by linarith
    have hreal : (4:ℝ)^4*((⌈complexity i⌉₊+1:ℕ):ℝ)≤N^(2*a) := by
      have hh := mul_le_mul_of_nonneg_left hceil (by norm_num : (0:ℝ)≤4^4)
      have hpow : N^(2*a)=(N^a)^2 := by
        rw [mul_comm (2:ℝ) a,Real.rpow_mul hN.le,Real.rpow_two]
      rw [hpow]
      nlinarith [sq_nonneg (N^a-512)]
    have hh := ENNReal.ofReal_le_ofReal hreal
    simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤4^4),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] using hh
  calc
    _ ≤ ∏ _i∈Finset.range L, ENNReal.ofReal (N^(2*a)) := by
      apply Finset.prod_le_prod
      intro i hi
      exact hfactor i (Finset.mem_range.mp hi)
    _ = (ENNReal.ofReal (N^(2*a)))^L := by simp
    _ = ENNReal.ofReal ((N^(2*a))^L) := (ENNReal.ofReal_pow (Real.rpow_nonneg hN.le _) L).symm
    _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]

/-- The polynomial residual-selection cost is absorbed by the total
native qualification failure. It never cuts the physical source. -/
theorem residual_selection_native_error_le {N a native target : ℝ}
    (hN : 1≤N) (L : ℕ) (complexity : ℕ → ℝ)
    (hlarge : 1024≤N^a)
    (hcomplexity : ∀ i<L, 0≤complexity i ∧ complexity i≤N^a)
    (hgap : 2*a*(L:ℝ)+target≤native)
    (htwo : 2≤N^(native-2*a*(L:ℝ)-target)) :
    (∏ i∈Finset.range L, (4:ENNReal)^4*(⌈complexity i⌉₊+1:ℕ))*
      ENNReal.ofReal (2*N^(-native))≤ENNReal.ofReal (N^(-target)) := by
  have hN0 : 0<N := zero_lt_one.trans_le hN
  have hfactor := residual_selection_factor_le hN0 hlarge L complexity hcomplexity
  apply (mul_le_mul' hfactor le_rfl).trans
  rw [←ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    N^(2*a*(L:ℝ))*(2*N^(-native))=
        2*N^(2*a*(L:ℝ)-native) := by rw [Real.rpow_sub hN0,Real.rpow_neg hN0.le]; ring
    _ ≤ N^(native-2*a*(L:ℝ)-target)*N^(2*a*(L:ℝ)-native) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hN0.le _)
    _ = N^(-target) := by rw [←Real.rpow_add hN0]; congr 1; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
