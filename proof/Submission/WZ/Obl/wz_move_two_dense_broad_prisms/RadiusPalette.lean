-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RadiusPalette.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RegularPowers

/-! The finite radius palette used before selecting either kind of prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- The first radius prepares the enlarged prism. Remaining radii cover all
narrow-cap extension lengths, with harmless clamping at unused scales. -/
def radiusPalette (d L : ℝ) (K : ℕ) : Fin (K+2) → ℝ :=
  Fin.cases (L/8) (fun k : Fin (K+1) => max (8*d) (min 1 (d/(2*(1/2:ℝ)^(k:ℕ)))))

lemma radiusPalette_bounds {d L : ℝ} {K : ℕ} (hd : 0 < d) (hd1 : d ≤ 1/100)
    (hL : 0 < L) (hL1 : L/8 ≤ 1) (hdL : d ≤ L/64) :
    (∀ j, 0 < radiusPalette d L K j) ∧ (∀ j, radiusPalette d L K j ≤ 1) ∧
      ∀ j, d ≤ radiusPalette d L K j/8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change 0 < L/8
      positivity
    · change 0 < max (8*d) _
      exact (by positivity : 0 < 8*d).trans_le (le_max_left _ _)
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact hL1
    · change max (8*d) (min 1 _) ≤ 1
      exact max_le (by linarith) (min_le_left _ _)
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change d ≤ L/8/8
      linarith
    · change d ≤ max (8*d) _/8
      have hh := le_max_left (8*d) (min 1 (d/(2*(1/2:ℝ)^(k:ℕ))))
      linarith

lemma radiusPalette_narrow {d L : ℝ} {K : ℕ} (k : Fin (K+1))
    (hd : 0 < d) (hθ : (1/2:ℝ)^(k:ℕ) ≤ 1/10000)
    (hell : d/((1/2:ℝ)^(k:ℕ)) ≤ 1) :
    radiusPalette d L K k.succ = (d/((1/2:ℝ)^(k:ℕ)))/2 := by
  have hθp : 0 < (1/2:ℝ)^(k:ℕ) := by positivity
  change max (8*d) (min 1 (d/(2*(1/2:ℝ)^(k:ℕ)))) = _
  have he : d/(2*(1/2:ℝ)^(k:ℕ)) = (d/((1/2:ℝ)^(k:ℕ)))/2 := by ring
  rw [he, min_eq_right (by linarith : (d/((1/2:ℝ)^(k:ℕ)))/2 ≤ 1)]
  apply max_eq_right
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  apply (le_div_iff₀ hθp).mpr
  nlinarith

/-- One angular packet budget also pays the extra radius and two extraction modes. -/
lemma palette_count_budget {d η ε : ℝ} {K : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hη : 0 < η) (hηε : η ≤ ε/1000)
    (hsmall : (10:ℝ)^40*d^(η/4) ≤ 1)
    (hcount : d^(η/2) ≤ 1/(2*((K:ℝ)+1))) :
    ((K+2:ℕ):ℝ)*d^η ≤ d^(η/2) ∧
      d^η ≤ 1/(2*((K:ℝ)+1)) ∧
      2*((K+1)+(K+1):ℕ)*d^ε ≤ d^(ε/2) := by
  have hcount' : (2*((K:ℝ)+1))*d^(η/2) ≤ 1 := by
    exact (by simpa only [mul_comm] using (le_div_iff₀ (by positivity : (0:ℝ) < 2*((K:ℝ)+1))).mp hcount)
  have hp : d^η = d^(η/2)*d^(η/2) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  refine ⟨?_, (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)).trans hcount, ?_⟩
  · have hh : ((K+2:ℕ):ℝ)*d^(η/2) ≤ 1 := by
      push_cast
      have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
      nlinarith [Real.rpow_pos_of_pos hd (η/2)]
    rw [hp]
    nlinarith [Real.rpow_pos_of_pos hd (η/2)]
  · have hs : (10:ℝ)^40*d^((η/2)/2) ≤ 1 := by
      convert hsmall using 1 <;> congr 1 <;> ring
    have hconst := small_power_comparison hd hd1 hs
      (by linarith : (η/2)/2 ≤ (ε-η/2)-ε/2)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 10^40)
    have hmul := mul_le_mul_of_nonneg_right hcount' (Real.rpow_nonneg hd.le (ε-η/2))
    have he : d^(η/2)*d^(ε-η/2) = d^ε := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    rw [mul_assoc, he, one_mul] at hmul
    push_cast
    nlinarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
