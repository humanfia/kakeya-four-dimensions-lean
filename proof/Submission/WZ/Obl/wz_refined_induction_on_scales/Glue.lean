-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_refined_induction_on_scales.Glue.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_refined_induction_on_scales.Basic
import Submission.WZ.Obl.wz_refined_induction_on_scales.Interfaces

namespace WangZahlLot.Obl.wz_refined_induction_on_scales

open MeasureTheory

namespace Interfaces

/-- Shrinking the density/counting error strengthens the bundled input. -/
theorem a_mono_normalized {δ η η' : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (h : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    A δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
  have h' : Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y :=
    hypotheses_iff.mpr h
  exact hypotheses_iff.mp (h'.mono_normalized hδ hδ1 hη)

/-- A larger slab constant preserves the above-slab inequality. -/
theorem f_mono {d l l' : ℝ} {n : ℕ} {x v : Fin n → V}
    (hF : F d l n x v) (hl : l ≤ l') : F d l' n x v := by
  intro u t r hu hr
  apply (hF u t r hu hr).trans
  exact mul_le_mul_left
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg n))) _

/-- A larger slab constant preserves every assigned fiber's inequality. -/
theorem b_mono {d ρ l l' : ℝ} {n N : ℕ} {x v : Fin n → V}
    {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hB : B d ρ l n N x v S y w f) (hl : l ≤ l') :
    B d ρ l' n N x v S y w f := by
  intro k u t r hu hr
  apply (hB k u t r hu hr).trans
  exact mul_le_mul_left
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg _))) _

/-- The smaller gain and smaller coefficient work for either volume branch. -/
theorem gain_mono {δ σ ω α α' κ κ' : ℝ} {n : ℕ} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hα : α ≤ α')
    (hκ : κ ≤ κ') (hκ' : 0 ≤ κ')
    (h : o (κ' * δ ^ (ω - α') * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i)) :
    o (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have hp : δ ^ (ω - α) ≤ δ ^ (ω - α') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hκ hp (Real.rpow_nonneg hδ.le _) hκ') (by positivity))
    (Real.rpow_nonneg (by positivity) _)

end Interfaces
end WangZahlLot.Obl.wz_refined_induction_on_scales
