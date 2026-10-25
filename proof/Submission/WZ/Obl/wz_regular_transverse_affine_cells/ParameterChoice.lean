-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.ParameterChoice.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.IteratePackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PowerDepth

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

lemma iteration_exponents {s : ℝ} (hs : 0 < s) :
    ∃ (N : ℕ) (ε p : ℝ), 0 < ε ∧ 0 < p ∧ 4 ≤ ε * N ∧
      p * (N * (2 * N + 5) + 2 : ℕ) ≤ s ∧ p * (N + 1 : ℕ) ≤ s ∧
      p / 2 ≤ s - ε - p * (N + 1 : ℕ) ∧ p / 2 ≤ s - ε ∧ p / 2 ≤ s := by
  let ε := s / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ε)
  have hεN : 4 ≤ ε * N := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  let L : ℕ := N * (2 * N + 5) + 2
  have hLpos : (0 : ℝ) < L := by dsimp [L]; positivity
  have hNL : (N + 1 : ℕ) ≤ L := by dsimp [L]; nlinarith
  have hNLr : ((N + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hNL
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ L by dsimp [L]; omega)
  let p := s / (4 * (L : ℝ))
  have hp : 0 < p := by dsimp [p]; positivity
  have hpL : p * L = s / 4 := by dsimp [p]; field_simp
  have hpN : p * (N + 1 : ℕ) ≤ s / 4 := by
    rw [← hpL]
    exact mul_le_mul_of_nonneg_left hNLr hp.le
  have hpupper : p ≤ s / 4 := by nlinarith [mul_le_mul_of_nonneg_left hL1 hp.le]
  refine ⟨N, ε, p, hε, hp, hεN, ?_, ?_, ?_, ?_, ?_⟩
  · change p * L ≤ s
    rw [hpL]
    linarith
  · linarith
  all_goals (try dsimp [ε]); linarith

lemma power_comparison_of_slack {δ C c η a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hsmall : C * δ ^ η ≤ 1) (hexp : η ≤ b - a) :
    c * δ ^ b ≤ δ ^ a := by
  have hfactor : c * δ ^ (b - a) ≤ 1 := by
    calc c * δ ^ (b - a) ≤ c * δ ^ η :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp) hc
      _ ≤ C * δ ^ η := mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg hδ.le _)
      _ ≤ 1 := hsmall
  calc c * δ ^ b = δ ^ a * (c * δ ^ (b - a)) := by
        rw [mul_left_comm, ← Real.rpow_add hδ]
        congr 1
        ring
    _ ≤ δ ^ a * 1 := mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hδ.le _)
    _ = _ := mul_one _

set_option maxHeartbeats 1000000 in
/-- The finite geometric losses can all be absorbed into the requested power. -/
lemma asymptotic_iteration_parameters (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ (N K : ℕ) (τ κ t θ : ℝ),
        IterationParameters δ (δ ^ s) 1000000000 τ κ t θ N K ∧
        768 * τ ≤ δ ^ η ∧ δ ^ s ≤ τ ^ (N * (2 * N + 5) + 2) ∧
        (1 / 2 : ℝ) ^ K * (384 * δ ^ (-100 : ℝ)) ≤ 1 := by
  obtain ⟨N, ε, p, hε, hp, hεN, hpL, hpN, hgap, hgapAngle, hgapSmall⟩ := iteration_exponents hs
  let S : ℝ := 1000000000
  let C : ℝ := 10 ^ (40 : ℕ)
  have hS : 0 < S := by norm_num [S]
  have hC : 0 < C := by norm_num [C]
  have hC1 : 1 ≤ C := by norm_num [C]
  obtain ⟨δ₁, hδ₁, hδ₁small, hdepth⟩ := dyadic_depth_with_power_budget 102 (p / 2) C
    (by norm_num) (by positivity) hC
  refine ⟨p / 2, by positivity, min δ₁ C⁻¹, lt_min hδ₁ (inv_pos.mpr hC),
    (min_le_left _ _).trans hδ₁small, ?_⟩
  intro δ hδ hδmax
  have hδlog : δ ≤ δ₁ := hδmax.trans (min_le_left _ _)
  have hδC : δ ≤ C⁻¹ := hδmax.trans (min_le_right _ _)
  have hδ100 : δ ≤ 1 / 100 := hδlog.trans hδ₁small
  have hδ1 : δ ≤ 1 := by linarith
  have hδ12 : δ ≤ 1 / (12 * S) := hδC.trans (by norm_num [C, S])
  have hδ512 : δ ≤ 1 / (512 * S ^ 3) := hδC.trans (by norm_num [C, S])
  obtain ⟨K, hKpow, hlog₀⟩ := hdepth δ hδ hδlog
  let z := δ ^ (p / 2)
  let τ := δ ^ p
  let κ := δ ^ ε
  let t := κ / (2048 * S)
  let θ := t / 9
  have hz : 0 < z := Real.rpow_pos_of_pos hδ _
  have hz1 : z ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hδ _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hp.le
  have hκ : 0 < κ := Real.rpow_pos_of_pos hδ _
  have hκ1 : κ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hε.le
  have ht : 0 < t := by dsimp [t]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hK1 : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K))
  have hlog : C * (K + 1 : ℕ) * z ≤ 1 := by
    simpa only [z, Nat.cast_add, Nat.cast_one] using hlog₀
  have hsmall : C * z ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hK1 (mul_nonneg hC.le hz.le)
    nlinarith
  have hτz2 : τ = z ^ (2 : ℕ) := by
    dsimp [τ, z]
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
  have hτz : τ ≤ z := by rw [hτz2]; nlinarith
  have hlogτ : C * (K + 1 : ℕ) * τ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hτz (by positivity)).trans hlog
  have hlogc (c : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) : c * (K + 1 : ℕ) * τ ≤ 1 := by
    apply le_trans _ hlogτ
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC (by positivity)) hτ.le
  have hsmallc (c : ℝ) (hcC : c ≤ C) : c * z ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcC hz.le).trans hsmall
  have hτdensity : 3072 * τ ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hτz (by norm_num)).trans (hsmallc 3072 (by norm_num [C]))
  have hτbudget : 8 * (1000000 * (K + 1 : ℕ)) * (400000 * S) * 384 * τ ≤ 1 := by
    have h := hlogc (8 * 1000000 * (400000 * S) * 384) (by positivity) (by norm_num [C, S])
    convert h using 1 <;> ring
  have hτshape : τ * (K + 1 : ℕ) ^ 2 ≤ 1 := by
    have hKz : (K + 1 : ℕ) * z ≤ (1 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ (K + 1 : ℕ) * z)
      nlinarith
    calc τ * (K + 1 : ℕ) ^ 2 = ((K + 1 : ℕ) * z) ^ (2 : ℕ) := by rw [hτz2]; ring
      _ ≤ 1 := pow_le_one₀ (by positivity) hKz
  have hτslab : 768 * (1 + 320 * K : ℝ) * τ ≤ 1 := by
    have h := hlogc 246528 (by norm_num) (by norm_num [C])
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    push_cast at h
    nlinarith [mul_nonneg hk hτ.le]
  have hinit : 768 * τ ≤ δ ^ (p / 2) := by
    have h := hsmallc 768 (by norm_num [C])
    rw [hτz2]
    change 768 * z ^ 2 ≤ z
    nlinarith [mul_le_mul_of_nonneg_right h hz.le]
  have hqualityDensity : δ ^ s ≤ τ ^ (N + 1) := by
    dsimp [τ]
    rw [← Real.rpow_mul_natCast hδ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hpN
  have hqualityAngle : δ ^ s ≤ θ := by
    have h := power_comparison_of_slack hδ hδ1 (by positivity : 0 ≤ 18432 * S)
      (by norm_num [C, S] : 18432 * S ≤ C) hsmall hgapAngle
    change δ ^ s ≤ δ ^ ε / (2048 * S) / 9
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith [h]
  have hqualitySlab : δ ^ s * 6144 ≤ t * τ ^ (N + 1) := by
    have h := power_comparison_of_slack hδ hδ1 (by positivity : 0 ≤ 12582912 * S)
      (by norm_num [C, S] : 12582912 * S ≤ C) hsmall (by linarith : p / 2 ≤ s - (ε + p * (N + 1 : ℕ)))
    change δ ^ s * 6144 ≤ δ ^ ε / (2048 * S) * (δ ^ p) ^ (N + 1)
    rw [← Real.rpow_mul_natCast hδ.le, div_mul_eq_mul_div, ← Real.rpow_add hδ,
      le_div_iff₀ (by positivity)]
    nlinarith [h]
  have hqualitySmall : δ ^ s ≤ 1 / (12 * S) := by
    have h := power_comparison_of_slack (a := 0) hδ hδ1 (by positivity : 0 ≤ 12 * S)
      (by norm_num [C, S] : 12 * S ≤ C) hsmall (by simpa using hgapSmall)
    rw [Real.rpow_zero] at h
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hδsquare : δ ^ (2 : ℕ) ≤ δ / (12 * S) := by
    have h := mul_le_mul_of_nonneg_left hδ12 hδ.le
    nlinarith [h]
  have hshape : δ ^ (100 : ℕ) ≤ δ / (12 * S) :=
    (pow_le_pow_of_le_one hδ.le hδ1 (by norm_num : (2 : ℕ) ≤ 100)).trans hδsquare
  have hKnat : (1 / 2 : ℝ) ^ K ≤ δ ^ (102 : ℕ) := by simpa only [Real.rpow_ofNat] using hKpow
  have hKscale : (1 / 2 : ℝ) ^ K < δ / (6 * S) := by
    apply (hKnat.trans ((pow_le_pow_of_le_one hδ.le hδ1 (by norm_num : (2 : ℕ) ≤ 102)).trans hδsquare)).trans_lt
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hDupper : 512 * S ^ 3 ≤ δ ^ (-100 : ℝ) := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 512 * S ^ 3)).mp hδ512
    have hinv : 512 * S ^ 3 ≤ δ⁻¹ := by rw [← one_div, le_div_iff₀ hδ]; nlinarith
    calc 512 * S ^ 3 ≤ δ⁻¹ := hinv
      _ = δ ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hextinct : 8 * κ ^ N < δ ^ 3 / 8 := by
    have hκ4 : κ ^ N ≤ δ ^ (4 : ℕ) := by
      dsimp [κ]
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_ofNat]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεN
    have hδ3 : 0 < δ ^ (3 : ℕ) := pow_pos hδ _
    have h := mul_le_mul_of_nonneg_right hδ100 hδ3.le
    nlinarith [hκ4, h]
  have hret : δ ^ s ≤ τ ^ (N * (2 * N + 5) + 2) := by
    dsimp [τ]
    rw [← Real.rpow_mul_natCast hδ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hpL
  have hbottom : (1 / 2 : ℝ) ^ K * (384 * δ ^ (-100 : ℝ)) ≤ 1 := by
    have he : δ ^ (102 : ℕ) * δ ^ (-100 : ℝ) = δ ^ (2 : ℕ) := by
      have h : δ ^ (102 : ℝ) * δ ^ (-100 : ℝ) = δ ^ (2 : ℝ) := by rw [← Real.rpow_add hδ]; norm_num
      simpa only [Real.rpow_ofNat] using h
    calc (1 / 2 : ℝ) ^ K * (384 * δ ^ (-100 : ℝ))
        ≤ δ ^ (102 : ℕ) * (384 * δ ^ (-100 : ℝ)) :=
          mul_le_mul_of_nonneg_right hKnat (by positivity)
      _ = 384 * δ ^ (2 : ℕ) := by rw [mul_left_comm, he]
      _ ≤ 1 := by nlinarith [hδ100]
  refine ⟨N, K, τ, κ, t, θ, ?_, hinit, hret, hbottom⟩
  refine {
    delta_pos := hδ, delta_small := hδ1, scale_large := by norm_num,
    depth_scale := hKscale, tau_pos := hτ, tau_small := hτ1,
    tau_density := hτdensity, tau_budget := hτbudget, tau_shape := hτshape, tau_slab := hτslab,
    quality_pos := Real.rpow_pos_of_pos hδ _, width_pos := ht, width_small := ?_,
    angle_pos := hθ, shrink_pos := hκ, quality_density := hqualityDensity,
    quality_angle := hqualityAngle, quality_slab := hqualitySlab,
    width_shrink := ?_, angle_width := ?_, shape_lower := hshape,
    quality_small := hqualitySmall, jacobian_lower := ?_, jacobian_upper := hDupper,
    extinction := hextinct }
  · dsimp [t]
    apply le_trans (div_le_div_of_nonneg_right hκ1 (by positivity))
    norm_num [S]
  · dsimp [t]
    apply le_of_eq
    rw [← mul_div_assoc, mul_div_cancel_left₀ κ (by positivity : (2048 * S : ℝ) ≠ 0)]
  · dsimp [θ]
    linarith
  · exact pow_le_pow_of_le_one hδ.le hδ1 (by norm_num : (3 : ℕ) ≤ 100)

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
