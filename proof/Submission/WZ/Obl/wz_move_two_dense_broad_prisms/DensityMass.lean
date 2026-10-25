-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DensityMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.InputMass

/-! Incidence density from uniform fine masses and a cardinal lower bound. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal

/-- Convert a cardinal estimate and uniform per-tube mass into incidence
density on a finite-measure carrier. -/
theorem incidence_density_of_cardinal {n : ℕ} (F : Finset (Fin n)) (Q : Fin n → Set V)
    (hQfin : ∀ i, volume (Q i) ≠ ∞) (E : Set V) (hEfin : volume E ≠ ∞)
    {t m C D : ℝ} (ht : 0 ≤ t) (hC : 0 < C) (hD : 0 ≤ D)
    (hcount : m ≤ C*(F.card : ℝ)) (hmass : ∀ i ∈ F, O t ≤ volume (Q i))
    (hbudget : D*volume.real E*C ≤ m*t) :
    O D*volume E ≤ ∑ i, volume (Q i) := by
  have htotal : (F.card : ℝ)*t ≤ ∑ i, volume.real (Q i) := by
    calc
      _ = ∑ _i ∈ F, t := by simp
      _ ≤ ∑ i ∈ F, volume.real (Q i) := Finset.sum_le_sum fun i hi =>
        (ENNReal.ofReal_le_iff_le_toReal (hQfin i)).mp (hmass i hi)
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hreal : D*volume.real E ≤ ∑ i, volume.real (Q i) := by
    apply (mul_le_mul_iff_left₀ hC).mp
    calc
      _ ≤ m*t := hbudget
      _ ≤ (C*(F.card : ℝ))*t := mul_le_mul_of_nonneg_right hcount ht
      _ = C*((F.card : ℝ)*t) := by ring
      _ ≤ C*(∑ i, volume.real (Q i)) := mul_le_mul_of_nonneg_left htotal hC.le
      _ = _ := mul_comm _ _
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin)
    (ENNReal.sum_ne_top.mpr (fun i _ => hQfin i))).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD,
    ENNReal.toReal_sum (fun i _ => hQfin i), Measure.real] using hreal

lemma cover_incidence_lower {d h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hA : A d h (d^(-h)) (d^(-h)) n x v Y)
    (hC : C d h n x v Y S Z ρ N y w f True) :
    O (d^(2*h)*(n : ℝ)*d^2) ≤ ∑ i, volume (Z i) := by
  calc
    _ = O (d^h)*O (d^h*(n : ℝ)*d^2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _)]
      congr 1
      rw [show 2*h = h+h by ring, Real.rpow_add hd]
      ring
    _ ≤ O (d^h)*∑ i, volume (Y i) := mul_le_mul_right hA.2.2.2.1 _
    _ ≤ _ := cover_mass_all hC

lemma half_mass_of_real {n : ℕ} {Y Z : Fin n → Set V}
    (hYfin : ∀ i, volume (Y i) ≠ ∞) (hZfin : ∀ i, volume (Z i) ≠ ∞)
    (h : (∑ i, volume.real (Y i))/2 ≤ ∑ i, volume.real (Z i)) :
    (1/2 : ENNReal)*(∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr (fun i _ => hYfin i)))
    (ENNReal.sum_ne_top.mpr (fun i _ => hZfin i))).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ENNReal.toReal_inv, mul_one, one_mul, ENNReal.toReal_sum (fun i _ => hYfin i),
    ENNReal.toReal_sum (fun i _ => hZfin i), Measure.real, div_eq_mul_inv, mul_comm] using h

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
