-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormZoom

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory

/-- All numerical requirements for the final mild zoom. -/
structure NormBounds (η β δ lam dmax : ℝ) (L : ℕ) : Prop where
  half_scale : lam * δ ≤ δ ^ (1 / 2 : ℝ)
  scale : lam * δ ≤ dmax
  tiny : lam * δ ≤ 1 / 10 ^ 12
  first : 25 * (lam * δ) ≤ (lam * δ) ^ β
  last : (lam * δ) ^ β ≤ 25 * (lam * δ) * ((lam * δ) ^ (-(β / 2))) ^ (L - 1)
  step : δ ^ (-η) * (lam * δ) ^ (-(β / 2)) ≤ (lam * δ) ^ (-β)
  start : 25 * δ ^ (-η) ≤ (lam * δ) ^ (-β)
  coarse : 3 * 10 ^ 8 * δ ^ (-η) * (lam * δ) ^ β ≤ 25
  count : 2 * (7200000 * lam ^ 2) * (384 * δ ^ 2) ≤ δ ^ η * δ ^ η
  density : 27440 * (normColors lam : ℝ) ^ (L + 1) * (lam * δ) ^ β ≤ δ ^ η
  frostman : 5000000 * lam ^ 2 * δ ^ (-η) / normRet δ η lam L ≤ (lam * δ) ^ (-β)
  top : 8000 * δ ^ (-η) / normRet δ η lam L ≤ (lam * δ) ^ (-β)

/-- A single large constant absorbs all fixed losses in the normalization. -/
theorem norm_constant_bound {δ η : ℝ} {L : ℕ} (hδ : 0 < δ)
    (hsmall : δ ^ η ≤ 1 / (10 ^ 60 * ((L + 1 : ℕ) : ℝ))) :
    (10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ) ≤ δ ^ (-η) := by
  have hp : 0 < (10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ) := by positivity
  have h := (le_div_iff₀ hp).mp hsmall
  have hi : δ ^ η * δ ^ (-η) = 1 := by rw [← Real.rpow_add hδ]; simp
  calc (10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ) =
        (δ ^ η * ((10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ))) * δ ^ (-η) := by
          calc _ = (δ ^ η * δ ^ (-η)) * ((10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ)) := by rw [hi, one_mul]
            _ = _ := by ring
    _ ≤ 1 * δ ^ (-η) := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-η) := one_mul _

set_option maxHeartbeats 4000000 in
/-- Power comparisons used by `zoomed_dense_weak`, with all constants absorbed first. -/
theorem norm_numerics {δ η β dmax : ℝ} {L : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (hη100 : η ≤ 1 / 100)
    (hβ : 0 < β) (hβ4 : β ≤ 1 / 4)
    (hbudget : (22 + 9 * (L : ℝ)) * η ≤ β / 2)
    (hgrid : 1 ≤ β / 2 * ((L - 1 : ℕ) : ℝ))
    (hC : (10 : ℝ) ^ 60 * ((L + 1 : ℕ) : ℝ) ≤ δ ^ (-η))
    (hcut : δ ^ (1 / 2 : ℝ) ≤ min dmax (1 / 10 ^ 12)) :
    NormBounds η β δ (3 * δ ^ (-η)) dmax L := by
  let lam := 3 * δ ^ (-η)
  let d := lam * δ
  have hδη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
  have hδη1 : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith only [hη])
  have hlam : 1 ≤ lam := by dsimp [lam]; linarith only [hδη1]
  have hlam0 : 0 < lam := by linarith only [hlam]
  have hd : 0 < d := mul_pos hlam0 hδ
  have hconst {a : ℝ} (ha : a ≤ (10 : ℝ) ^ 60) : a ≤ δ ^ (-η) := by
    have hN : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
    exact ha.trans ((le_mul_of_one_le_right (by norm_num) hN).trans hC)
  have hlampow : lam ≤ δ ^ (-2 * η) := by
    calc lam = 3 * δ ^ (-η) := rfl
      _ ≤ δ ^ (-η) * δ ^ (-η) := mul_le_mul_of_nonneg_right (hconst (by norm_num)) hδη.le
      _ = δ ^ (-2 * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
  have hlampow2 : lam ^ 2 ≤ δ ^ (-4 * η) := by
    calc lam ^ 2 ≤ (δ ^ (-2 * η)) ^ 2 := pow_le_pow_left₀ hlam0.le hlampow 2
      _ = δ ^ (-4 * η) := by rw [← Real.rpow_mul_natCast hδ.le]; congr 1; ring
  have hhalf : d ≤ δ ^ (1 / 2 : ℝ) := by
    calc d ≤ δ ^ (-2 * η) * δ := mul_le_mul_of_nonneg_right hlampow hδ.le
      _ = δ ^ (-2 * η) * δ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = δ ^ (1 - 2 * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hη100])
  have hd1 : d ≤ 1 := hhalf.trans (Real.rpow_le_one hδ.le hδ1 (by norm_num))
  have hupper (a : ℝ) (ha : 0 ≤ a) : d ^ a ≤ δ ^ (a / 2) := by
    calc d ^ a ≤ (δ ^ (1 / 2 : ℝ)) ^ a := Real.rpow_le_rpow hd.le hhalf ha
      _ = δ ^ (a / 2) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have hlower (a : ℝ) (ha : 0 ≤ a) : δ ^ (-(a / 2)) ≤ d ^ (-a) := by
    calc δ ^ (-(a / 2)) = (δ ^ (1 / 2 : ℝ)) ^ (-a) := by
          rw [← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ d ^ (-a) := Real.rpow_le_rpow_of_nonpos hd hhalf (neg_nonpos.mpr ha)
  have hηβ : 4 * η ≤ β := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith only [hbudget, hL0, hη.le]
  have hK : (normColors lam : ℝ) ≤ δ ^ (-9 * η) := by
    calc (normColors lam : ℝ) ≤ 2 * 10 ^ 50 * lam ^ 4 := normColors_le hlam
      _ ≤ δ ^ (-η) * (δ ^ (-2 * η)) ^ 4 := by
        apply mul_le_mul (hconst (by norm_num)) (pow_le_pow_left₀ hlam0.le hlampow 4)
          (by positivity) hδη.le
      _ = δ ^ (-9 * η) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]; congr 1; ring
  have hKP : (normColors lam : ℝ) ^ (L + 1) ≤ δ ^ (-9 * η * ((L + 1 : ℕ) : ℝ)) := by
    calc _ ≤ (δ ^ (-9 * η)) ^ (L + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hK _
      _ = _ := (Real.rpow_mul_natCast hδ.le _ _).symm
  have hden : 2 * 10 ^ 14 * lam ^ 2 * (normColors lam : ℝ) ^ (L + 1) * ((L + 1 : ℕ) : ℝ) ≤
      δ ^ (-(5 + 9 * ((L + 1 : ℕ) : ℝ)) * η) := by
    calc _ = (2 * 10 ^ 14 * ((L + 1 : ℕ) : ℝ)) * lam ^ 2 * (normColors lam : ℝ) ^ (L + 1) := by ring
      _ ≤ δ ^ (-η) * δ ^ (-4 * η) * δ ^ (-9 * η * ((L + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul (mul_le_mul ?_ hlampow2 (sq_nonneg _) hδη.le) hKP (by positivity) (by positivity)
        exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) * 10 ^ 14 ≤ 10 ^ 60)
          (Nat.cast_nonneg _)).trans hC
      _ = _ := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
  have hden0 : 0 < 2 * 10 ^ 14 * lam ^ 2 * (normColors lam : ℝ) ^ (L + 1) * ((L + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) < normColors lam := by exact_mod_cast normColors_pos lam
    positivity
  have hret : δ ^ ((7 + 9 * ((L + 1 : ℕ) : ℝ)) * η) ≤ normRet δ η lam L := by
    calc _ = δ ^ (2 * η) / δ ^ (-(5 + 9 * ((L + 1 : ℕ) : ℝ)) * η) := by
          rw [← Real.rpow_sub hδ]; congr 1; ring
      _ ≤ normRet δ η lam L := div_le_div_of_nonneg_left (by positivity) hden0 hden
  have ht : 0 < normRet δ η lam L := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ _) hret
  have hD7 : 5000000 * lam ^ 2 * δ ^ (-η) / normRet δ η lam L ≤ d ^ (-β) := by
    calc _ ≤ δ ^ (-η) * δ ^ (-4 * η) * δ ^ (-η) / δ ^ ((7 + 9 * ((L + 1 : ℕ) : ℝ)) * η) := by
          apply div_le_div₀ (by positivity) ?_ (Real.rpow_pos_of_pos hδ _) hret
          gcongr
          exact hconst (by norm_num)
      _ = δ ^ (-(13 + 9 * ((L + 1 : ℕ) : ℝ)) * η) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]; congr 1; ring
      _ ≤ δ ^ (-(β / 2)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
        push_cast; linarith only [hbudget])
      _ ≤ d ^ (-β) := hlower β hβ.le
  refine ⟨hhalf, hhalf.trans (hcut.trans (min_le_left _ _)), hhalf.trans (hcut.trans (min_le_right _ _)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hD7, ?_⟩
  · have hpow : d ^ (1 - β) ≤ δ ^ η :=
      (hupper (1 - β) (by linarith only [hβ4])).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hβ4, hη100]))
    have hi : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
    have hx : 25 * d ^ (1 - β) ≤ 1 := by
      calc _ ≤ δ ^ (-η) * δ ^ η := mul_le_mul (hconst (by norm_num)) hpow (by positivity) hδη.le
        _ = 1 := hi
    calc 25 * d = (25 * d ^ (1 - β)) * d ^ β := by
          rw [mul_assoc, ← Real.rpow_add hd]; simp
      _ ≤ 1 * d ^ β := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = d ^ β := one_mul _
  · have hx : 1 ≤ d ^ (1 - β / 2 * ((L - 1 : ℕ) : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith only [hgrid])
    have he : d * (d ^ (-(β / 2))) ^ (L - 1) = d ^ (1 - β / 2 * ((L - 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_mul_natCast hd.le]
      calc d * d ^ (-(β / 2) * ((L - 1 : ℕ) : ℝ)) = d ^ (1 : ℝ) * d ^ (-(β / 2) * ((L - 1 : ℕ) : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hd]; congr 1; ring
    have : d ^ β ≤ 1 := Real.rpow_le_one hd.le hd1 hβ.le
    calc d ^ β ≤ 1 := this
      _ ≤ 25 * (d * (d ^ (-(β / 2))) ^ (L - 1)) := by rw [he]; linarith only [hx]
      _ = _ := by ring
  · have hx : δ ^ (-η) ≤ d ^ (-(β / 2)) :=
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hηβ])).trans
        (hlower (β / 2) (by positivity))
    calc _ ≤ d ^ (-(β / 2)) * d ^ (-(β / 2)) := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = d ^ (-β) := by rw [← Real.rpow_add hd]; congr 1; ring
  · calc 25 * δ ^ (-η) ≤ δ ^ (-η) * δ ^ (-η) := mul_le_mul_of_nonneg_right (hconst (by norm_num)) hδη.le
      _ = δ ^ (-2 * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (-(β / 2)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hηβ])
      _ ≤ d ^ (-β) := hlower β hβ.le
  · calc _ ≤ δ ^ (-η) * δ ^ (-η) * δ ^ (β / 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hconst (by norm_num)) hδη.le)
            (hupper β hβ.le) (by positivity) (by positivity)
      _ = δ ^ (β / 2 - 2 * η) := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith only [hηβ])
      _ ≤ 25 := by norm_num
  · calc _ = (2 * 7200000 * 384) * lam ^ 2 * δ ^ 2 := by ring
      _ ≤ δ ^ (-η) * δ ^ (-4 * η) * δ ^ 2 := by
        gcongr
        exact hconst (by norm_num)
      _ = δ ^ (2 - 5 * η) := by
        rw [← Real.rpow_two δ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (2 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hη100])
      _ = δ ^ η * δ ^ η := by rw [← Real.rpow_add hδ]; congr 1; ring
  · calc _ ≤ δ ^ (-η) * δ ^ (-9 * η * ((L + 1 : ℕ) : ℝ)) * δ ^ (β / 2) := by
          apply mul_le_mul (mul_le_mul (hconst (by norm_num)) hKP (by positivity) hδη.le)
            (hupper β hβ.le) (by positivity) (by positivity)
      _ = δ ^ (β / 2 - (1 + 9 * ((L + 1 : ℕ) : ℝ)) * η) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
        push_cast; nlinarith only [hbudget, hη.le])
  · apply le_trans ?_ hD7
    apply div_le_div_of_nonneg_right _ ht.le
    have hlampow1 : (1 : ℝ) ≤ lam ^ 2 := one_le_pow₀ hlam
    apply mul_le_mul_of_nonneg_right _ hδη.le
    linarith only [hlampow1]



/-- The same budget gives the compactification and covering constants. -/
theorem norm_output_bounds {δ d η ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 < d) (hhalf : d ≤ δ ^ (1 / 2 : ℝ)) (hε : 0 < ε) (hηε : 4 * η ≤ ε)
    (h32 : 32 ≤ δ ^ (-η)) :
    d ^ ε ≤ d ^ (ε / 2) / 2 ∧ 32 * δ ^ (-η) ≤ d ^ (-ε) := by
  have hsmall : δ ^ η ≤ 1 / 2 := by
    have hi : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
    have hh := mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hδ.le η)
    rw [hi] at hh
    linarith only [hh]
  have hpow : d ^ (ε / 2) ≤ 1 / 2 := by
    calc d ^ (ε / 2) ≤ (δ ^ (1 / 2 : ℝ)) ^ (ε / 2) := Real.rpow_le_rpow hd.le hhalf (by positivity)
      _ = δ ^ (ε / 4) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hηε])
      _ ≤ 1 / 2 := hsmall
  constructor
  · calc d ^ ε = d ^ (ε / 2) * d ^ (ε / 2) := by rw [← Real.rpow_add hd]; congr 1; ring
         _ ≤ d ^ (ε / 2) / 2 := by nlinarith only [hpow, Real.rpow_nonneg hd.le (ε / 2)]
  · calc 32 * δ ^ (-η) ≤ δ ^ (-η) * δ ^ (-η) := mul_le_mul_of_nonneg_right h32 (by positivity)
         _ = δ ^ (-2 * η) := by rw [← Real.rpow_add hδ]; congr 1; ring
         _ ≤ δ ^ (-(ε / 2)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hηε])
         _ = (δ ^ (1 / 2 : ℝ)) ^ (-ε) := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
         _ ≤ d ^ (-ε) := Real.rpow_le_rpow_of_nonpos hd hhalf (by linarith only [hε])

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
