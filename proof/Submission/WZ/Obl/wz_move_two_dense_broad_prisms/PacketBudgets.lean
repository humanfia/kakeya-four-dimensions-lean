-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PacketBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PowerBudgets

/-! Scalar budgets for angular packet pruning and the Córdoba prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- An extra arbitrarily small power pays the absolute packet-label cost. -/
lemma packet_row_budget {d η L : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η)
    (hL : 0 ≤ L) (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) :
    (2*6^3*22^3 : ℝ)*(d^(3*η)*L*d^2) ≤ d^η*(d^η*L*d^2/256)/4 := by
  have hb := small_power_budget hd hd1 hsmall (by linarith : η/2 ≤ η)
    (by norm_num : (0:ℝ) ≤ 1024*(2*6^3*22^3)) (by norm_num : (1024*(2*6^3*22^3):ℝ) ≤ 10^40)
  have h3 : d^(3*η) = d^η*d^η*d^η := by
    rw [← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ d^η*d^η*L*d^2 by positivity)
  rw [h3]
  nlinarith

/-- A subpower decrement from the packet angle still exceeds the fine angle. -/
lemma packet_partner_radius {d θ ω β η : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hβ : 0 < β) (hη : 0 < η) (hηβ : η ≤ β*ω/1000)
    (hθlow : d^(1-ω/100) ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) :
    d ≤ θ*d^(η/β) ∧ θ*d^(η/β) ≤ 1 ∧ 8*((θ*d^(η/β))/θ)^β < 1 := by
  have hθ : 0 < θ := (Real.rpow_pos_of_pos hd _).trans_le hθlow
  have hω : 0 < ω := by nlinarith
  have hfrac : η/β ≤ ω/1000 := (div_le_iff₀ hβ).mpr (by nlinarith)
  have hlow : d ≤ θ*d^(η/β) := by
    calc
      d = d^(1:ℝ) := (Real.rpow_one d).symm
      _ ≤ d^((1-ω/100)+η/β) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
      _ = d^(1-ω/100)*d^(η/β) := Real.rpow_add hd _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hθlow (by positivity)
  refine ⟨hlow, ?_, ?_⟩
  · calc
      θ*d^(η/β) ≤ θ*1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1 (by positivity)) hθ.le
      _ ≤ 1 := by simpa using hθ1
  · have he : (θ*d^(η/β))/θ = d^(η/β) := by field_simp
    rw [he, ← Real.rpow_mul hd.le, show η/β*β = η by field_simp]
    have hh := small_power_budget hd hd1 hsmall (by linarith : η/2 ≤ η)
      (by norm_num : (0:ℝ) ≤ 16) (by norm_num : (16:ℝ) ≤ 10^40)
    linarith

/-- The side-rounding factor costs only a small power when the thin side is
bounded by `20000*d^(1-b)`. -/
lemma packet_broadness_budget {d η ε β b A : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η) (hε : 0 < ε)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hb : 0 ≤ b) (hbε : b ≤ ε/100)
    (hηε : η ≤ ε/1000) (hA : 0 ≤ A) (hAmax : A ≤ 20000*d^(1-b))
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) :
    8*(1000000*A/d)^β ≤ d^(-ε) := by
  have hbase : 1000000*A/d ≤ 20000000000*d^(-b) := by
    have he : d^(1-b) = d*d^(-b) := by rw [sub_eq_add_neg, Real.rpow_add hd, Real.rpow_one]
    rw [he] at hAmax
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hcoef : (20000000000:ℝ)^β ≤ 20000000000 := by
    calc
      _ ≤ (20000000000:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
      _ = _ := Real.rpow_one _
  have hbb : b*β ≤ b := by nlinarith
  have hbudget := small_power_budget hd hd1 hsmall (by linarith : η/2 ≤ ε-b*β)
    (by norm_num : (0:ℝ) ≤ 160000000000) (by norm_num : (160000000000:ℝ) ≤ 10^40)
  calc
    _ ≤ 8*(20000000000*d^(-b))^β := by gcongr
    _ = 8*((20000000000:ℝ)^β)*d^(-b*β) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hd.le]
      ring
    _ ≤ 160000000000*d^(-b*β) := by nlinarith [Real.rpow_nonneg hd.le (-b*β)]
    _ = d^(-ε)*(160000000000*d^(ε-b*β)) := by
      rw [← mul_assoc, mul_comm (d^(-ε)) 160000000000, mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ d^(-ε)*1 := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := mul_one _

/-- The numerical density condition in the local Córdoba lemma. -/
lemma packet_cordoba_budget {d η ε β b A L θ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hβ : 0 < β) (hη : 0 < η)
    (hε : 0 < ε) (hbε : b ≤ ε/100) (hηε : η ≤ ε/1000) (hηβε : η ≤ β*ε/1000)
    (hA : 0 ≤ A) (hAmax : A ≤ 20000*d^(1-b)) (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (hlog : (10:ℝ)^40*(1+Real.log (1/d))*d^(ε/2) ≤ 1) :
    (1000000000*L*d^5*(1+Real.log (1/d)))*d^ε*
      (100000000000000*(A^2/d)*θ*L^2) ≤
      (d^(3*η)*L*d^2)^3*(θ*d^(η/β)) := by
  have hlog0 : 0 ≤ 1+Real.log (1/d) := by
    have hh : (1:ℝ) ≤ 1/d := (le_div_iff₀ hd).mpr (by simpa using hd1)
    linarith [Real.log_nonneg hh]
  have hfrac : η/β ≤ ε/1000 := (div_le_iff₀ hβ).mpr (by nlinarith)
  have hgap : ε/2 ≤ ε-2*b-9*η-η/β := by linarith
  have hpow : d^(ε-2*b-9*η-η/β) ≤ d^(ε/2) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 hgap
  have hsmall : 40000000000000000000000000000000*(1+Real.log (1/d))*d^(ε-2*b-9*η-η/β) ≤ 1 := by
    refine (mul_le_mul (mul_le_mul_of_nonneg_right (by norm_num : (40000000000000000000000000000000:ℝ) ≤ 10^40) hlog0)
      hpow (Real.rpow_nonneg hd.le _) (by positivity)).trans hlog
  have hD2 : (d^(1-b))^2 = d^(2-2*b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    congr 1
    ring
  have hD3 : (d^(3*η))^3 = d^(9*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    congr 1
    ring
  have hscalar : 40000000000000000000000000000000*(1+Real.log (1/d))*d^(ε-2*b) ≤ d^(9*η+η/β) := by
    calc
      _ = d^(9*η+η/β)*(40000000000000000000000000000000*(1+Real.log (1/d))*d^(ε-2*b-9*η-η/β)) := by
        have he : d^(9*η+η/β)*d^(ε-2*b-9*η-η/β) = d^(ε-2*b) := by
          rw [← Real.rpow_add hd]
          congr 1
          ring
        calc
          _ = (40000000000000000000000000000000*(1+Real.log (1/d)))*
              (d^(9*η+η/β)*d^(ε-2*b-9*η-η/β)) := by rw [he]
          _ = _ := by ring
      _ ≤ d^(9*η+η/β)*1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ (1000000000*L*d^5*(1+Real.log (1/d)))*d^ε*
        (100000000000000*((20000*d^(1-b))^2/d)*θ*L^2) := by gcongr
    _ = (θ*L^3*d^6)*(40000000000000000000000000000000*(1+Real.log (1/d))*d^(ε-2*b)) := by
      rw [mul_pow, hD2]
      have he : d^5*(d^(2-2*b)/d)*d^ε = d^6*d^(ε-2*b) := by
        have hp : d^(2-2*b)*d^ε = d^2*d^(ε-2*b) := by
          rw [← Real.rpow_add hd, ← Real.rpow_two, ← Real.rpow_add hd]
          congr 1
          ring
        calc
          _ = (d^5/d)*(d^(2-2*b)*d^ε) := by ring
          _ = _ := by rw [hp]; field_simp
      calc
        _ = 40000000000000000000000000000000*θ*L^3*(1+Real.log (1/d))*(d^5*(d^(2-2*b)/d)*d^ε) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ (θ*L^3*d^6)*d^(9*η+η/β) := mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by rw [Real.rpow_add hd, mul_pow, mul_pow, hD3]; ring

/-- The strong incident density excludes angular scales below the frozen
lower bound, even after a small-power packet loss. -/
lemma packet_lower_angle_budget {d η h ω β : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hω : 0 < ω) (hβ : 0 ≤ β)
    (hβω : β ≤ ω/1000) (hη : 0 < η) (hηω : η ≤ ω/1000)
    (hh : h ≤ η/4) (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) :
    1728*d^(-h)*(d^(1-ω/100))^(2-β) < (d^η*d^(-ω/2))*d^2 := by
  let gap : ℝ := -h+(1-ω/100)*(2-β)-(η-ω/2+2)
  have hgap : η/2 ≤ gap := by
    dsimp [gap]
    nlinarith [mul_nonneg hω.le hβ]
  have hs := small_power_budget hd hd1 hsmall hgap
    (by norm_num : (0:ℝ) ≤ 3456) (by norm_num : (3456:ℝ) ≤ 10^40)
  have he : -h+(1-ω/100)*(2-β) = (η-ω/2+2)+gap := by dsimp [gap]; ring
  have hr : (d^η*d^(-ω/2))*d^2 = d^(η-ω/2+2) := by
    rw [← Real.rpow_two, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  have hl : 1728*d^(-h)*(d^(1-ω/100))^(2-β) =
      d^(η-ω/2+2)*(1728*d^gap) := by
    rw [← Real.rpow_mul hd.le, mul_assoc, ← Real.rpow_add hd, he,
      Real.rpow_add hd]
    ring
  rw [hl, hr]
  exact (mul_lt_mul_of_pos_left (by linarith : 1728*d^gap < 1)
    (Real.rpow_pos_of_pos hd _)).trans_eq (mul_one _)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
