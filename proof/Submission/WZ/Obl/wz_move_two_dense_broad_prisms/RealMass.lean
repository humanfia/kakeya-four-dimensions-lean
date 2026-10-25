-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RealMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.InputMass

/-! Real-valued mass inequalities used by the finite residual iteration. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal

lemma admissible_real_mass_pos {d h m l : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hd : 0 < d) (hA : A d h m l n x v Y) :
    0 < ∑ i, volume.real (Y i) := by
  have hh := ENNReal.toReal_pos (admissible_mass_pos hd hA).ne'
    (ENNReal.sum_ne_top.mpr (fun i _ => admissible_finite_mass hA i))
  simpa only [Measure.real, ENNReal.toReal_sum (fun i _ => admissible_finite_mass hA i)] using hh

lemma cover_real_retention {d h m l τ ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hτ : h ≤ τ)
    (hA : A d h m l n x v Y) (hC : C d h n x v Y S Z ρ N y w f True) :
    d^τ*(∑ i, volume.real (Y i)) ≤ ∑ i, volume.real (Z i) := by
  have hZfin (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset
    (hC.1 i).2.1 (admissible_finite_mass hA i)
  have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun i _ => hZfin i)) (cover_mass_all hC)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.le h),
    ENNReal.toReal_sum (fun i _ => admissible_finite_mass hA i),
    ENNReal.toReal_sum (fun i _ => hZfin i)] at hh
  exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hd hd1 hτ)
    (Finset.sum_nonneg (fun i _ => measureReal_nonneg))).trans hh

lemma longer_prism_length_budget {d ω c : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hω : 0 ≤ ω) (hc : 0 ≤ c) : d^(-ω/150)*c ≤ 10*(d^(-ω/100)*c) := by
  have hh := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -ω/100 ≤ -ω/150)) hc
  have hp : 0 ≤ d^(-ω/100)*c := mul_nonneg (Real.rpow_nonneg hd.le _) hc
  linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
