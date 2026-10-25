-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/NormalizedArms.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.PathJets
import Submission.Obl.k4_matching_switching_target_certificate.LevelTranslate

/-!
# Normalized arms on a coarse interval

On the coarse interval with center `ta` and length scale `lam`, an arm `φ` is
normalized by subtracting a reference polynomial `T` (the order-`J` Taylor polynomial
of a starting arm), rescaling time by `lam`, and scaling so that the `m`-th
derivative is multiplied by `W` (`= N^(β_m)` in the paper):

  `normArm φ T ta lam W m s = W lam^(-m) (φ - T)(ta + lam s)`,

so that `(normArm ..)^(j)(s) = W lam^(j-m) (φ - T)^(j)(ta + lam s)`. The `m`-th
derivative is the control of the constant-control jet ODE.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The normalized arm. -/
noncomputable def normArm (φ T : ℝ → ℝ) (ta lam W : ℝ) (m : ℕ) : ℝ → ℝ :=
  fun s => W * (lam ^ m)⁻¹ * (φ (ta + lam * s) - T (ta + lam * s))

/-- The order-`J` Taylor polynomial with jet `c` at `ta`. -/
noncomputable def taylorPoly (J : ℕ) (c : ℕ → ℝ) (ta : ℝ) : ℝ → ℝ :=
  pathJet (J + 1) c (fun _ => 0) (fun _ => ta) 0 0

lemma contDiff_taylorPoly (J : ℕ) (c : ℕ → ℝ) (ta : ℝ) : ContDiff ℝ ⊤ (taylorPoly J c ta) :=
  contDiff_pathJet _ _ _ _ _ _

lemma iteratedDeriv_taylorPoly (J : ℕ) (c : ℕ → ℝ) (ta : ℝ) {j : ℕ} (hj : j ≤ J + 1) (t : ℝ) :
    iteratedDeriv j (taylorPoly J c ta) t =
      ∑ i ∈ Finset.range (J + 1 - j), c (j + i) * (t - ta) ^ i / (i.factorial : ℝ) := by
  rw [taylorPoly, iteratedDeriv_pathJet _ _ _ _ _ hj]
  simp [pathJet]

lemma iteratedDeriv_normArm {φ T : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hφ : ContDiffOn ℝ n φ U) (hT : ContDiff ℝ ⊤ T) (ta lam W : ℝ) (m : ℕ) {j : ℕ}
    (hj : j ≤ n) {s : ℝ} (hs : ta + lam * s ∈ U) :
    iteratedDeriv j (normArm φ T ta lam W m) s =
      W * (lam ^ m)⁻¹ * lam ^ j *
        (iteratedDeriv j φ (ta + lam * s) - iteratedDeriv j T (ta + lam * s)) := by
  set g : ℝ → ℝ := fun t => φ t - T t with hg
  have h1 : normArm φ T ta lam W m = fun s => (W * (lam ^ m)⁻¹) * g (ta + lam * s) := rfl
  rw [h1, iteratedDeriv_const_mul_field, iteratedDeriv_comp_affine g ta lam j]
  have hφa : ContDiffAt ℝ j φ (ta + lam * s) :=
    (hφ.contDiffAt (hU.mem_nhds hs)).of_le (by exact_mod_cast hj)
  have hTa : ContDiffAt ℝ j T (ta + lam * s) := (hT.of_le le_top).contDiffAt
  show W * (lam ^ m)⁻¹ * (lam ^ j * iteratedDeriv j (fun t => φ t - T t) (ta + lam * s)) = _
  rw [iteratedDeriv_fun_sub hφa hTa]
  ring

lemma contDiffOn_normArm {φ T : ℝ → ℝ} {U : Set ℝ} {n : ℕ}
    (hφ : ContDiffOn ℝ n φ U) (hT : ContDiff ℝ ⊤ T) (ta lam W : ℝ) (m : ℕ) :
    ContDiffOn ℝ n (normArm φ T ta lam W m) ((fun s => ta + lam * s) ⁻¹' U) := by
  have haff : ContDiff ℝ ⊤ (fun s : ℝ => ta + lam * s) := by fun_prop
  have hcomp : ContDiffOn ℝ n (fun s => φ (ta + lam * s)) ((fun s => ta + lam * s) ⁻¹' U) :=
    hφ.comp (haff.of_le le_top).contDiffOn (fun s hs => hs)
  have hcompT : ContDiffOn ℝ n (fun s => T (ta + lam * s)) ((fun s => ta + lam * s) ⁻¹' U) :=
    ((hT.comp haff).of_le le_top).contDiffOn
  exact contDiffOn_const.mul (hcomp.sub hcompT)

/-- The top derivative of a normalized arm does not depend on `lam`. -/
lemma iteratedDeriv_normArm_top {φ T : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hφ : ContDiffOn ℝ n φ U) (hT : ContDiff ℝ ⊤ T) (ta W : ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    {m : ℕ} (hm : m ≤ n) {s : ℝ} (hs : ta + lam * s ∈ U) :
    iteratedDeriv m (normArm φ T ta lam W m) s =
      W * (iteratedDeriv m φ (ta + lam * s) - iteratedDeriv m T (ta + lam * s)) := by
  rw [iteratedDeriv_normArm hU hφ hT ta lam W m hm hs]
  field_simp

/-- The scale factor of the `j`-th normalized derivative on an active piece:
`N^(β_m) lam^(j-m) ≤ 2^m N^(l_j(a))` when `lam ≥ N^(-r(a))/2` and
`l_j(a) = β_m + (m - j) r(a)`. -/
lemma scale_factor_le {N lam βm ra lja : ℝ} (hN : 1 ≤ N) (hlam : N ^ (-ra) / 2 ≤ lam)
    {m j : ℕ} (hjm : j ≤ m) (hl : lja = βm + ((m : ℝ) - (j : ℝ)) * ra) :
    N ^ βm * (lam ^ m)⁻¹ * lam ^ j ≤ 2 ^ m * N ^ lja := by
  have hN0 : 0 < N := by linarith
  have hpos : 0 < N ^ (-ra) / 2 := by positivity
  have hlam0 : 0 < lam := hpos.trans_le hlam
  have hsplit : (lam ^ m)⁻¹ * lam ^ j = (lam ^ (m - j))⁻¹ := by
    rw [← Nat.sub_add_cancel hjm, pow_add, mul_inv, Nat.add_sub_cancel, mul_assoc,
      inv_mul_cancel₀ (pow_pos hlam0 j).ne', mul_one]
  rw [mul_assoc, hsplit]
  have h1 : (lam ^ (m - j))⁻¹ ≤ ((N ^ (-ra) / 2) ^ (m - j))⁻¹ :=
    inv_anti₀ (pow_pos hpos _) (pow_le_pow_left₀ hpos.le hlam _)
  have h2 : ((N ^ (-ra) / 2) ^ (m - j))⁻¹ = 2 ^ (m - j) * N ^ (((m - j : ℕ) : ℝ) * ra) := by
    rw [div_pow, inv_div, ← Real.rpow_natCast (N ^ (-ra)), ← Real.rpow_mul hN0.le,
      div_eq_mul_inv, ← Real.rpow_neg hN0.le]
    ring_nf
  have h3 : (2 : ℝ) ^ (m - j) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le m j)
  calc N ^ βm * (lam ^ (m - j))⁻¹ ≤ N ^ βm * (2 ^ (m - j) * N ^ (((m - j : ℕ) : ℝ) * ra)) := by
        rw [← h2]; gcongr
    _ ≤ N ^ βm * (2 ^ m * N ^ (((m - j : ℕ) : ℝ) * ra)) := by gcongr
    _ = 2 ^ m * N ^ lja := by
        rw [hl, Nat.cast_sub hjm, Real.rpow_add hN0]; ring

/-- **Normalized gap.** The reference polynomial cancels: the `j`-th derivatives of two
normalized arms differ by the scale factor times the gap of the arms. -/
lemma normArm_gap {φ φ' T : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hφ : ContDiffOn ℝ n φ U) (hφ' : ContDiffOn ℝ n φ' U) (hT : ContDiff ℝ ⊤ T)
    (ta lam W : ℝ) (m : ℕ) {j : ℕ} (hj : j ≤ n) {s : ℝ} (hs : ta + lam * s ∈ U) :
    iteratedDeriv j (normArm φ T ta lam W m) s - iteratedDeriv j (normArm φ' T ta lam W m) s =
      W * (lam ^ m)⁻¹ * lam ^ j *
        (iteratedDeriv j φ (ta + lam * s) - iteratedDeriv j φ' (ta + lam * s)) := by
  rw [iteratedDeriv_normArm hU hφ hT ta lam W m hj hs,
    iteratedDeriv_normArm hU hφ' hT ta lam W m hj hs]
  ring

/-- **Control approximation.** On an active piece with margin `γ`, the top derivative of
a normalized arm stays within `(3K + N^ε) N^(-γ)` of the constant `W (φ^(m)(ta) - c m)`,
whenever the arm's jets at the coarse center are within `K N^(-l_i(a))` of the reference
jets `c`. -/
theorem normArm_control {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ} {m : ℕ} (hmJ : m ≤ J)
    {N ε K γ : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ (J + 1 : ℕ) φ (Ioo (-1 : ℝ) 2))
    (hφB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) φ t| ≤ N ^ ε)
    {c : ℕ → ℝ} {ta lam : ℝ} (hlam : lam ≠ 0) {a : ℝ} (ha : 0 ≤ a)
    (hta : ta ∈ Icc (0 : ℝ) 1)
    (hc : ∀ i : ℕ, i ≤ J → |iteratedDeriv i φ ta - c i| ≤
      K * N ^ (-jetAccuracy (jetRadius J β) i a))
    (hlm : jetAccuracy (jetRadius J β) m a = β m)
    (hγ1 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - jetAccuracy (jetRadius J β) m a)
    (hγ2 : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    {s : ℝ} (hts : ta + lam * s ∈ Icc (0 : ℝ) 1)
    (hdist : |lam * s| ≤ N ^ (-jetRadius J β a)) :
    |iteratedDeriv m (normArm φ (taylorPoly J c ta) ta lam (N ^ β m) m) s
        - N ^ β m * (iteratedDeriv m φ ta - c m)| ≤ (3 * K + N ^ ε) * N ^ (-γ) := by
  have hN0 : 0 < N := by linarith
  set r := jetRadius J β with hr_def
  set l := jetAccuracy r with hl_def
  set t := ta + lam * s with ht_def
  have hU : IsOpen (Ioo (-1 : ℝ) 2) := isOpen_Ioo
  have htU : t ∈ Ioo (-1 : ℝ) 2 := ⟨by linarith [hts.1], by linarith [hts.2]⟩
  rw [iteratedDeriv_normArm_top hU hφ (contDiff_taylorPoly J c ta) ta (N ^ β m) hlam
    (by omega) htU, iteratedDeriv_taylorPoly J c ta (by omega) t]
  have hd : |t - ta| = |lam * s| := by rw [ht_def]; ring_nf
  have hd0 : 0 ≤ |t - ta| := abs_nonneg _
  have hdist' : |t - ta| ≤ N ^ (-r a) := hd ▸ hdist
  -- Taylor remainder of `φ^(m)` from `ta` to `t`
  have hseg : uIcc ta t ⊆ Ioo (-1 : ℝ) 2 := fun x hx =>
    let h := uIcc_subset_Icc hta hts hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hT := taylor_iteratedDeriv_bound hU hφ hseg
    (fun x hx => hφB x (uIcc_subset_Icc hta hts hx)) (by omega : m < J + 1)
  set R := iteratedDeriv m φ t - ∑ i ∈ Finset.range (J + 1 - m),
      iteratedDeriv (m + i) φ ta * (t - ta) ^ i / (i.factorial : ℝ) with hR
  obtain ⟨k, hk⟩ : ∃ k, J + 1 - m = k + 1 := ⟨J - m, by omega⟩
  have hdecomp : N ^ β m * (iteratedDeriv m φ t - ∑ i ∈ Finset.range (J + 1 - m),
        c (m + i) * (t - ta) ^ i / (i.factorial : ℝ)) - N ^ β m * (iteratedDeriv m φ ta - c m)
      = N ^ β m * R + N ^ β m * ∑ i ∈ Finset.range k,
          (iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))) * (t - ta) ^ (i + 1) /
            ((i + 1).factorial : ℝ) := by
    rw [hR, hk, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, add_zero]
    rw [show ∑ i ∈ Finset.range k, (iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))) *
        (t - ta) ^ (i + 1) / ((i + 1).factorial : ℝ) =
        ∑ i ∈ Finset.range k, iteratedDeriv (m + (i + 1)) φ ta * (t - ta) ^ (i + 1) /
          ((i + 1).factorial : ℝ) - ∑ i ∈ Finset.range k, c (m + (i + 1)) * (t - ta) ^ (i + 1) /
          ((i + 1).factorial : ℝ) by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  rw [hdecomp]
  have hNβ : 0 < N ^ β m := Real.rpow_pos_of_pos hN0 _
  -- the remainder term
  have hRb : |N ^ β m * R| ≤ N ^ ε * N ^ (-γ) := by
    rw [abs_mul, abs_of_pos hNβ]
    have hfac : (1 : ℝ) ≤ ((J + 1 - m).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : |R| ≤ N ^ ε * |t - ta| ^ (J + 1 - m) :=
      hT.trans (div_le_self (by positivity) hfac)
    have h2 : |t - ta| ^ (J + 1 - m) ≤ N ^ (-(0 + ((J + 1 - m : ℕ) : ℝ) * r a)) :=
      rpow_mul_pow_le (x := 0) hN _ hd0 hdist' |>.trans_eq' (by simp)
    have hcast : ((J + 1 - m : ℕ) : ℝ) = (J : ℝ) + 1 - (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast, zero_add] at h2
    calc N ^ β m * |R| ≤ N ^ β m * (N ^ ε * N ^ (-(((J : ℝ) + 1 - (m : ℝ)) * r a))) := by
          gcongr; exact h1.trans (by gcongr)
      _ = N ^ ε * N ^ (β m - ((J : ℝ) + 1 - (m : ℝ)) * r a) := by
          rw [show β m - ((J : ℝ) + 1 - (m : ℝ)) * r a =
            β m + -(((J : ℝ) + 1 - (m : ℝ)) * r a) by ring, Real.rpow_add hN0]
          ring
      _ ≤ N ^ ε * N ^ (-γ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by rw [← hlm]; linarith))
            (by positivity)
  -- the higher jet terms
  have hSb : |N ^ β m * ∑ i ∈ Finset.range k,
      (iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))) * (t - ta) ^ (i + 1) /
        ((i + 1).factorial : ℝ)| ≤ 3 * K * N ^ (-γ) := by
    rw [abs_mul, abs_of_pos hNβ]
    have hterm : ∀ i ∈ Finset.range k, N ^ β m * |(iteratedDeriv (m + (i + 1)) φ ta -
        c (m + (i + 1))) * (t - ta) ^ (i + 1) / ((i + 1).factorial : ℝ)| ≤
        K * N ^ (-γ) * (1 / ((i + 1).factorial : ℝ)) := by
      intro i hi
      have hi' : m + (i + 1) ≤ J := by have := Finset.mem_range.mp hi; omega
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      have hb := hc (m + (i + 1)) hi'
      have hp : |t - ta| ^ (i + 1) ≤ N ^ (-(0 + ((i + 1 : ℕ) : ℝ) * r a)) :=
        rpow_mul_pow_le (x := 0) hN _ hd0 hdist' |>.trans_eq' (by simp)
      rw [zero_add] at hp
      have hexp : N ^ β m * (N ^ (-l (m + (i + 1)) a) * N ^ (-(((i + 1 : ℕ) : ℝ) * r a))) ≤
          N ^ (-γ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
        refine Real.rpow_le_rpow_of_exponent_le hN ?_
        have := hγ2 (i + 1) (by omega) hi'
        push_cast at this ⊢
        linarith
      calc N ^ β m * (|iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))| *
            |t - ta| ^ (i + 1) / ((i + 1).factorial : ℝ))
          ≤ N ^ β m * (K * N ^ (-l (m + (i + 1)) a) *
            N ^ (-(((i + 1 : ℕ) : ℝ) * r a)) / ((i + 1).factorial : ℝ)) := by
            gcongr
        _ = K * (N ^ β m * (N ^ (-l (m + (i + 1)) a) * N ^ (-(((i + 1 : ℕ) : ℝ) * r a)))) *
            (1 / ((i + 1).factorial : ℝ)) := by ring
        _ ≤ K * N ^ (-γ) * (1 / ((i + 1).factorial : ℝ)) := by gcongr
    have hsum1 := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs (fun i =>
      (iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))) * (t - ta) ^ (i + 1) /
        ((i + 1).factorial : ℝ)) (Finset.range k)) hNβ.le
    refine hsum1.trans ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have he : ∑ i ∈ Finset.range k, 1 / ((i + 1).factorial : ℝ) ≤ 3 := by
      have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (k + 1)
      have h2 := Real.exp_one_lt_d9
      rw [Finset.sum_range_succ'] at h1
      simp only [one_pow, Nat.factorial_zero, Nat.cast_one, div_one] at h1
      linarith
    have hpos : 0 ≤ K * N ^ (-γ) := by positivity
    nlinarith
  calc _ ≤ |N ^ β m * R| + |N ^ β m * ∑ i ∈ Finset.range k,
        (iteratedDeriv (m + (i + 1)) φ ta - c (m + (i + 1))) * (t - ta) ^ (i + 1) /
          ((i + 1).factorial : ℝ)| := abs_add_le _ _
    _ ≤ N ^ ε * N ^ (-γ) + 3 * K * N ^ (-γ) := add_le_add hRb hSb
    _ = (3 * K + N ^ ε) * N ^ (-γ) := by ring

end Submission.Obl.k4_matching_switching_target_certificate
