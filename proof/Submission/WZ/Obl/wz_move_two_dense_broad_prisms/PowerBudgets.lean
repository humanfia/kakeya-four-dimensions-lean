-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PowerBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs

/-! Uniform numerical budgets for residual preparation and lengthening. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- One small positive power absorbs every fixed constant used below. -/
lemma small_power_budget {d η p K : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) (hp : η/2 ≤ p)
    (hK : 0 ≤ K) (hKmax : K ≤ (10:ℝ)^40) : K*d^p ≤ 1 := by
  calc
    _ ≤ (10:ℝ)^40*d^(η/2) := mul_le_mul hKmax
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 hp) (Real.rpow_nonneg hd.le _) (by positivity)
    _ ≤ _ := hsmall

structure PrepPowers (ω β η d h ρ c : ℝ) : Prop where
  lambda_pos : 0 < d^η
  lambda_one : d^η ≤ 1
  length_pos : 0 < d^(-ω/100)*c
  length_gain : 100000000*c ≤ d^(-ω/100)*c
  length_small : (d^(-ω/100)*c)/8 ≤ 1
  radius_small : d ≤ (d^(-ω/100)*c)/64
  endpoint_radius : d ≤ 1000000000000*(d^(-ω/100)*c)
  endpoint_clearance : 4*(d^(-ω/100)*c) ≤ 1000000000000*(d^(-ω/100)*c)
  endpoint_budget : 4608*(1000000000000*(d^(-ω/100)*c)) ≤ d^η
  angle_low : d ≤ ρ*d^(4*η/β)
  angle_high : ρ*d^(4*η/β) ≤ ρ
  fibre_cost : 32 ≤ d^(-η)
  mass_cost : 32*d^η ≤ d^(2*h)
  cap_cost : d^(-(h+η))*((ρ*d^(4*η/β))/ρ)^β ≤ 1/2
  output_length : 10*(d^(-ω/100)*c) ≤ 1
  output_gain : d^(-ω/150)*c ≤ 10*(d^(-ω/100)*c)

/-- All preparatory powers can be chosen uniformly before the input family. -/
theorem prep_powers {ω β η d h ρ c : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hβ : 0 < β) (hη : 0 < η)
    (hηω : η ≤ ω/1000) (hηβ : η ≤ β*ω/1000)
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ η/4)
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1)
    (hρ : d^(ω/100) ≤ ρ) (hρ1 : ρ ≤ 1)
    (hdc : d ≤ c) (hc : c ≤ d^(9*ω/20)) : PrepPowers ω β η d h ρ c := by
  have hcp : 0 < c := hd.trans_le hdc
  have hρp : 0 < ρ := (Real.rpow_pos_of_pos hd _).trans_le hρ
  have hLp : 0 < d^(-ω/100)*c := mul_pos (Real.rpow_pos_of_pos hd _) hcp
  have hp (p K : ℝ) (hK : 0 ≤ K) (hKmax : K ≤ (10:ℝ)^40) (hep : η/2 ≤ p) :
      K*d^p ≤ 1 := small_power_budget hd hd1 hsmall hep hK hKmax
  have hD : 100000000 ≤ d^(-ω/100) := by
    have hh' := hp (ω/100) 100000000 (by norm_num) (by norm_num) (by linarith)
    have hprod : d^(ω/100)*d^(-ω/100) = 1 := by
      rw [← Real.rpow_add hd, show ω/100 + -ω/100 = 0 by ring, Real.rpow_zero]
    nlinarith [Real.rpow_pos_of_pos hd (-ω/100)]
  have hlen : 100000000*c ≤ d^(-ω/100)*c := mul_le_mul_of_nonneg_right hD hcp.le
  have hLupper : d^(-ω/100)*c ≤ d^(11*ω/25) := by
    calc
      _ ≤ d^(-ω/100)*d^(9*ω/20) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by rw [← Real.rpow_add hd]; congr 1; ring
  have hend : 4608*(1000000000000*(d^(-ω/100)*c)) ≤ d^η := by
    have hbudget := hp (11*ω/25-η) 4608000000000000 (by norm_num) (by norm_num) (by linarith)
    calc
      _ ≤ 4608000000000000*d^(11*ω/25) := by nlinarith
      _ = d^η*(4608000000000000*d^(11*ω/25-η)) := by
        rw [← mul_assoc, mul_comm (d^η) 4608000000000000, mul_assoc,
          ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ d^η*1 := mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := mul_one _
  have hangleexp : 0 ≤ 4*η/β ∧ ω/100+4*η/β ≤ 1 := by
    have hh' : 4*η/β ≤ ω/250 := (div_le_iff₀ hβ).mpr (by nlinarith)
    exact ⟨by positivity, by linarith⟩
  have halow : d ≤ ρ*d^(4*η/β) := by
    calc
      d = d^(1:ℝ) := (Real.rpow_one d).symm
      _ ≤ d^(ω/100+4*η/β) := Real.rpow_le_rpow_of_exponent_ge hd hd1 hangleexp.2
      _ = d^(ω/100)*d^(4*η/β) := Real.rpow_add hd _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hρ (by positivity)
  have hfibre : 32 ≤ d^(-η) := by
    have hh' := hp η 32 (by norm_num) (by norm_num) (by linarith)
    have hprod : d^η*d^(-η) = 1 := by rw [← Real.rpow_add hd]; simp
    nlinarith [Real.rpow_pos_of_pos hd (-η)]
  have hmass : 32*d^η ≤ d^(2*h) := by
    have hbudget := hp (η-2*h) 32 (by norm_num) (by norm_num) (by linarith)
    calc
      _ = d^(2*h)*(32*d^(η-2*h)) := by
        rw [← mul_assoc, mul_comm (d^(2*h)) 32, mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ d^(2*h)*1 := mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := mul_one _
  have hcap : d^(-(h+η))*((ρ*d^(4*η/β))/ρ)^β ≤ 1/2 := by
    have he : (ρ*d^(4*η/β))/ρ = d^(4*η/β) := by field_simp
    rw [he, ← Real.rpow_mul hd.le, show 4*η/β*β = 4*η by field_simp,
      ← Real.rpow_add hd, show -(h+η)+4*η = 3*η-h by ring]
    have hh' := hp (3*η-h) 2 (by norm_num) (by norm_num) (by linarith)
    linarith
  have hL10 : 10*(d^(-ω/100)*c) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hLupper (by norm_num)).trans
      (hp (11*ω/25) 10 (by norm_num) (by norm_num) (by linarith))
  refine ⟨Real.rpow_pos_of_pos hd _, Real.rpow_le_one hd.le hd1 hη.le,
    hLp, hlen, by linarith, by linarith, by linarith, by linarith, hend, halow,
    ?_, hfibre, hmass, hcap, hL10, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1 hangleexp.1) hρp.le).trans_eq (mul_one ρ)
  · have hh' : d^(-ω/150) ≤ d^(-ω/100) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    have hh'' := mul_le_mul_of_nonneg_right hh' hcp.le
    linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
