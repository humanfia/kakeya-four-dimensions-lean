-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RegularPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PowerBudgets

/-! Cutoff estimates for simultaneous regularity and longer narrow prisms. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

lemma small_power_comparison {d η K p q : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1)
    (hgap : η/2 ≤ p-q) (hK : 0 ≤ K) (hKmax : K ≤ (10:ℝ)^40) :
    K*d^p ≤ d^q := by
  have hs := small_power_budget hd hd1 hsmall hgap hK hKmax
  calc
    _ = d^q*(K*d^(p-q)) := by
      rw [← mul_assoc, mul_comm (d^q) K, mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ d^q*1 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := mul_one _

/-- A common endpoint clearance covers both the original enlarged length and
all narrow extensions whose angle exceeds the required lower bound. -/
lemma regular_endpoint_budgets {d η ω c : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hη : 0 < η) (hηω : η ≤ ω/1000)
    (hc : c ≤ d^(9*ω/20)) (hsmall : (10:ℝ)^40*d^(η/4) ≤ 1) :
    d ≤ d^(ω/1000) ∧ 4608*d^(ω/1000) ≤ d^(η/2) ∧
      1000000000000*(d^(-ω/100)*c) ≤ d^(ω/1000) ∧
      ∀ θ : ℝ, d^(1-ω/100) ≤ θ → 40*(d/θ) ≤ d^(ω/1000) := by
  have hs : (10:ℝ)^40*d^((η/2)/2) ≤ 1 := by convert hsmall using 1 <;> congr 1 <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      d = d^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  · exact small_power_comparison hd hd1 hs (by linarith)
      (by norm_num : (0:ℝ) ≤ 4608) (by norm_num)
  · calc
      _ ≤ 1000000000000*(d^(-ω/100)*d^(9*ω/20)) := by gcongr
      _ = 1000000000000*d^(11*ω/25) := by
        rw [← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ _ := small_power_comparison hd hd1 hs (by linarith)
        (by norm_num) (by norm_num)
  · intro θ hθ
    have hθp : 0 < θ := (Real.rpow_pos_of_pos hd _).trans_le hθ
    have he : d/d^(1-ω/100) = d^(ω/100) := by
      calc
        _ = d^(1:ℝ)/d^(1-ω/100) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_sub hd]
          congr 1
          ring
    calc
      _ ≤ 40*(d/d^(1-ω/100)) := by gcongr
      _ = 40*d^(ω/100) := by rw [he]
      _ ≤ _ := small_power_comparison hd hd1 hs (by linarith)
        (by norm_num) (by norm_num)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
