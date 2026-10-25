-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.ScaleAlgebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseFamily
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

noncomputable abbrev coarseUniversalConstant : ℝ :=
  max (144 / coarseContraction) (coarseContraction⁻¹ ^ 3 / coarseFraction)

theorem coarseUniversalConstant_pos : 0 < coarseUniversalConstant :=
  lt_of_lt_of_le (by norm_num : 0 < 144 / coarseContraction) (le_max_left _ _)

theorem exists_small_rpow {s C : ℝ} (hs : 0 < s) (hC : 0 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ^ s ≤ C := by
  refine ⟨C ^ s⁻¹, Real.rpow_pos_of_pos hC _, ?_⟩
  intro δ hδ hδd
  calc
    _ ≤ (C ^ s⁻¹) ^ s := Real.rpow_le_rpow hδ.le hδd hs.le
    _ = C := Real.rpow_inv_rpow hC.le hs.ne'

theorem constant_le_negative_power {δ C s : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hsmall : δ ^ s ≤ C⁻¹) : C ≤ δ ^ (-s) := by
  rw [Real.rpow_neg hδ.le, ← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ s)).mpr
  exact (mul_le_mul_of_nonneg_left hsmall hC.le).trans_eq (mul_inv_cancel₀ hC.ne')

theorem absorb_power_constant {δ C Z s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C)
    (hsmall : δ ^ (Z / 2) ≤ C⁻¹) (hs : s ≤ Z / 2) :
    C * δ ^ (-s) ≤ δ ^ (-Z) := by
  calc
    _ ≤ δ ^ (-(Z / 2)) * δ ^ (-s) :=
      mul_le_mul_of_nonneg_right (constant_le_negative_power hδ hC hsmall) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-(Z / 2) + -s) := (Real.rpow_add hδ _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

theorem nonflat_ratio_bounds {δ a b β : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hflat : δ ^ β * b ≤ a) : δ ^ β ≤ a / b ∧ b / a ≤ δ ^ (-β) := by
  refine ⟨(le_div_iff₀ hb).mpr hflat, ?_⟩
  apply (div_le_iff₀ ha).mpr
  calc
    b = δ ^ (-β) * (δ ^ β * b) := by rw [← mul_assoc, ← Real.rpow_add hδ]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hflat (Real.rpow_nonneg hδ.le _)

theorem coarse_coefficients_power_bound {δ a b ν β : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (hb : 0 < b) (hν : 0 ≤ ν)
    (hflat : δ ^ β * b ≤ a) :
    coarseConvexCoefficient a b (δ ^ (-ν)) ≤ coarseUniversalConstant * δ ^ (-(5 * ν + β)) ∧
    coarseSlabCoefficient a b (δ ^ (-ν)) (δ ^ (-2 * ν)) ≤
      coarseUniversalConstant * δ ^ (-(5 * ν + β)) := by
  have hratio := (nonflat_ratio_bounds hδ ha hb hflat).2
  have hpow : δ ^ (-ν) * δ ^ (-β) = δ ^ (-(ν + β)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hpow3 : (δ ^ (-ν)) ^ 3 * δ ^ (-2 * ν) * δ ^ (-β) = δ ^ (-(5 * ν + β)) := by
    rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    norm_num
    ring
  constructor
  · calc
      _ = (144 / coarseContraction) * (δ ^ (-ν) * (b / a)) := by dsimp [coarseConvexCoefficient]; ring
      _ ≤ (144 / coarseContraction) * (δ ^ (-ν) * δ ^ (-β)) := by gcongr
      _ = (144 / coarseContraction) * δ ^ (-(ν + β)) := by rw [hpow]
      _ ≤ coarseUniversalConstant * δ ^ (-(5 * ν + β)) := by
        apply mul_le_mul (le_max_left _ _)
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (by positivity) coarseUniversalConstant_pos.le
  · have he : coarseSlabCoefficient a b (δ ^ (-ν)) (δ ^ (-2 * ν)) =
        (coarseContraction⁻¹ ^ 3 / coarseFraction) *
          ((δ ^ (-ν)) ^ 3 * δ ^ (-2 * ν)) * (b / a) := by
      dsimp [coarseSlabCoefficient, coarseMassFraction]
      field_simp
    rw [he]
    calc
      _ ≤ (coarseContraction⁻¹ ^ 3 / coarseFraction) *
          ((δ ^ (-ν)) ^ 3 * δ ^ (-2 * ν)) * δ ^ (-β) := by
        apply mul_le_mul_of_nonneg_left hratio
        have hcf := coarseFraction_pos
        positivity
      _ = (coarseContraction⁻¹ ^ 3 / coarseFraction) * δ ^ (-(5 * ν + β)) := by
        rw [mul_assoc, hpow3]
      _ ≤ coarseUniversalConstant * δ ^ (-(5 * ν + β)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem coarse_mass_power_lower {δ a b ν β : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hflat : δ ^ β * b ≤ a) :
    coarseFraction * δ ^ (β + 2 * ν) ≤ coarseMassFraction a b (δ ^ (-ν)) := by
  have hh := (nonflat_ratio_bounds hδ ha hb hflat).1
  have hpow : (δ ^ (-ν)) ^ 2 = δ ^ (-(2 * ν)) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
    ring
  calc
    _ = coarseFraction * δ ^ β / (δ ^ (-ν)) ^ 2 := by
      rw [Real.rpow_add hδ, hpow, Real.rpow_neg hδ.le, div_inv_eq_mul]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh coarseFraction_pos.le) (sq_nonneg _)

theorem excess_power_lower {δ a b ν β σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hνβ : 0 ≤ ν + β) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hflat : δ ^ β * b ≤ a) :
    δ ^ (ν + β) ≤ (δ ^ (-ν) * b / a) ^ (-σ) := by
  have hh : δ ^ (-ν) * b / a ≤ δ ^ (-(ν + β)) := by
    calc
      _ = δ ^ (-ν) * (b / a) := by ring
      _ ≤ δ ^ (-ν) * δ ^ (-β) := mul_le_mul_of_nonneg_left
        (nonflat_ratio_bounds hδ ha hb hflat).2 (by positivity)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  calc
    _ ≤ δ ^ ((ν + β) * σ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    _ = (δ ^ (-(ν + β))) ^ (-σ) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hh (by linarith)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
