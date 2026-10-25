-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.NarrowBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RegularPowers

/-! The high-count narrow cap survives global maximization and has a safe length. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

lemma narrow_scale_upper {d η ω c θ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η) (hηω : η ≤ ω/1000)
    (hdc : d ≤ c) (hθ : 0 ≤ θ) (hnarrow : θ*(d^(-ω/100)*c) ≤ d)
    (hsmall : (10:ℝ)^40*d^(η/4) ≤ 1) : θ ≤ 1/10000 := by
  have hs : (10:ℝ)^40*d^((η/2)/2) ≤ 1 := by
    convert hsmall using 1 <;> congr 1 <;> ring
  have hb := small_power_budget hd hd1 hs (by linarith : (η/2)/2 ≤ ω/100)
    (by norm_num : (0:ℝ) ≤ 10000) (by norm_num : (10000:ℝ) ≤ 10^40)
  have hlow : θ*d^(-ω/100)*d ≤ d := by
    have hh' := mul_le_mul_of_nonneg_left hdc (mul_nonneg hθ (Real.rpow_nonneg hd.le (-ω/100)))
    calc
      _ ≤ θ*d^(-ω/100)*c := hh'
      _ ≤ _ := by simpa only [mul_assoc] using hnarrow
  have hc : θ*d^(-ω/100) ≤ 1 := by nlinarith
  have hp : d^(-ω/100)*d^(ω/100) = 1 := by
    rw [← Real.rpow_add hd, show -ω/100+ω/100 = 0 by ring, Real.rpow_zero]
  have hθup : θ ≤ d^(ω/100) := by
    have hh' := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hd.le (ω/100))
    simpa only [mul_assoc, hp, mul_one, one_mul] using hh'
  linarith

/-- The high-count cut in the narrow prism loses only an arbitrarily small
power in both density and broadness. -/
lemma narrow_cut_budgets {d η ε β : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hη : 0 < η) (hηε : η ≤ ε/1000) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hsmall : (10:ℝ)^40*d^(η/4) ≤ 1) :
    d^ε ≤ (d^η/1000000000000)/2 ∧
      (4/(d^η/1000000000000))*(1000:ℝ)^β ≤ d^(-ε) := by
  have hs : (10:ℝ)^40*d^((η/2)/2) ≤ 1 := by
    convert hsmall using 1 <;> congr 1 <;> ring
  have hb := small_power_budget hd hd1 hs (by linarith : (η/2)/2 ≤ ε-η)
    (by norm_num : (0:ℝ) ≤ 4000000000000000) (by norm_num : (4000000000000000:ℝ) ≤ 10^40)
  have hp : d^(ε-η)*d^η = d^ε := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hden : 2000000000000*d^ε ≤ d^η := by
    have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hd.le η)
    rw [mul_assoc, hp, one_mul] at hh
    nlinarith [Real.rpow_pos_of_pos hd ε]
  have hpow : (1000:ℝ)^β ≤ 1000 := by
    calc
      _ ≤ (1000:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
      _ = _ := Real.rpow_one _
  refine ⟨by linarith, ?_⟩
  have hD : 0 < d^η/1000000000000 := by positivity
  have hleft : (4/(d^η/1000000000000))*(1000:ℝ)^β ≤ 4000000000000000/d^η := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4/(d^η/1000000000000) by positivity)
    convert hh using 1 <;> field_simp <;> norm_num
  apply hleft.trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hd η)).mpr
  have hc := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hd.le (-ε+η))
  have he : d^(ε-η)*d^(-ε+η) = 1 := by
    rw [← Real.rpow_add hd, show ε-η+(-ε+η) = 0 by ring, Real.rpow_zero]
  rw [mul_assoc, he, mul_one, one_mul] at hc
  rwa [← Real.rpow_add hd]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
