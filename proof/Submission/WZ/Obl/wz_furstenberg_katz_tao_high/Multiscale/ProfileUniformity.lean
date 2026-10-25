-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileUniformity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileObstruction

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

/-- The obstruction on an additive integer palette.  In particular the
reflected angular levels `a-y` are still recorded levels. -/
theorem exists_discrete_cell_energy_obstruction
    (G F : ℕ → ℝ) {s β E : ℝ} {a ℓ H : ℕ}
    (hs : s < 1) (hβ : β < s) (hE : 0 ≤ E)
    (_hH : 0 < H) (hHℓ : H ≤ ℓ) (hℓa : ℓ ≤ a)
    (hpoint : ∀ t, H ≤ t → t ≤ a → (t : ℝ) - E ≤ G t)
    (hpointUpper : ∀ t, H ≤ t → t ≤ ℓ → G t ≤ 2 * (t : ℝ) + E)
    (hbush : ∀ t, H ≤ t → t ≤ ℓ → s * (t : ℝ) - E ≤ F t)
    (htail : ∀ z, z ≤ ℓ → F a - β * (z : ℝ) - E ≤ F (a - z))
    (hlip : ∀ u v, u ≤ v → v ≤ a → F v - F u ≤ (v : ℝ) - u)
    (hgap : 4 * E < (s - β) * (H : ℝ))
    (hbudget : (2 - s) * ((2 - β) * (H : ℝ) + 2 * E) + 5 * E * (1 - β) <
      (1 - β) ^ 2 * (ℓ : ℝ)) :
    ∃ h : ℕ, H ≤ h ∧ h ≤ ℓ ∧
      ∀ y, h ≤ y → y ≤ a →
        F a + G h - F h + E < G y + F (a - y) := by
  classical
  let T := Finset.Icc H ℓ
  have hHT : H ∈ T := Finset.mem_Icc.mpr ⟨le_rfl, hHℓ⟩
  obtain ⟨h, hhT, hmin⟩ := Finset.exists_min_image T (fun t => G t - β * (t : ℝ))
    ⟨H, hHT⟩
  obtain ⟨hHh, hhℓ⟩ := Finset.mem_Icc.mp hhT
  have hβ1 : 0 < 1 - β := by linarith
  have h2s : 0 ≤ 2 - s := by linarith
  have hlocation := profile_minimum_location
    (hpoint h hHh (hhℓ.trans hℓa))
    (hpointUpper H le_rfl hHℓ) (hmin H hHT)
  have hfar : (2 - s) * (h : ℝ) + 5 * E < (1 - β) * (ℓ : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlocation h2s
    have hh : ((2 - s) * (h : ℝ) + 5 * E) * (1 - β) <
        ((1 - β) * (ℓ : ℝ)) * (1 - β) := by
      nlinarith only [hmul, hbudget]
    exact (mul_lt_mul_iff_left₀ hβ1).mp hh
  have hgap' : 4 * E < (s - β) * (h : ℝ) := hgap.trans_le
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hHh) (sub_pos.mpr hβ).le)
  refine ⟨h, hHh, hhℓ, ?_⟩
  intro y hhy hya
  have hb := hbush h hHh hhℓ
  by_cases hyℓ : y ≤ ℓ
  · have hm := hmin y (Finset.mem_Icc.mpr ⟨hHh.trans hhy, hyℓ⟩)
    have ht := htail y hyℓ
    nlinarith only [hm, ht, hb, hgap', hE]
  · have hyℓ' : ℓ ≤ y := (lt_of_not_ge hyℓ).le
    have ht := htail ℓ le_rfl
    have hf := hlip (a - y) (a - ℓ) (Nat.sub_le_sub_left hyℓ' a) (Nat.sub_le _ _)
    rw [Nat.cast_sub hℓa, Nat.cast_sub hya] at hf
    have hp := hpoint y (hHh.trans hhy) hya
    have hu := hpointUpper h hHh hhℓ
    nlinarith only [ht, hf, hp, hu, hb, hfar]

/-- Frontloading forces failure of the stronger energy inequality at a
coarsened resolution.  Unlike a change of the average bush exponent,
this conclusion uses the actual angular profile at every reflected level. -/
theorem frontloading_forces_energy_failure
    (G F : ℕ → ℝ) {n K H : ℕ} {s d E : ℝ}
    (hKn : K ≤ n) (hn : 0 < n) (hd : 0 < d) (hds : d ≤ s) (hs : s < 1)
    (hE : 0 ≤ E) (hH : 0 < H) (hHsmall : (H : ℝ) ≤ 3 * d * (n : ℝ) / 4)
    (hFn : F n = s * (n : ℝ))
    (hFmono : ∀ i j, i ≤ j → j ≤ n → F i ≤ F j)
    (hFlip : ∀ i j, i ≤ j → j ≤ n → F j - F i ≤ (j : ℝ) - i)
    (hpoint : ∀ t, H ≤ t → t ≤ n → (t : ℝ) - E ≤ G t)
    (hpointUpper : ∀ t, H ≤ t → t ≤ n → G t ≤ 2 * (t : ℝ) + E)
    (hbush : ∀ t, H ≤ t → t ≤ n → s * (t : ℝ) - E ≤ F t)
    (hfront : s * (K : ℝ) + d * (n : ℝ) ≤ F K)
    (hgap : 4 * E < (d / 4) * (H : ℝ))
    (hbudget : (2 - s) * ((2 - (s - d / 4)) * (H : ℝ) + 2 * E) +
        5 * E * (1 - (s - d / 4)) <
      (1 - (s - d / 4)) ^ 2 * (3 * d * (n : ℝ) / 4)) :
    ∃ a h : ℕ, K < a ∧ a ≤ n ∧ H ≤ h ∧ h ≤ a ∧
      ∀ y, h ≤ y → y ≤ a →
        F a + G h - F h + E < G y + F (a - y) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨a, hKa, han, hspan, htail⟩ := frontloading_terminal_interval F (fun i => (i : ℝ))
    hKn hnR hd hds hs (Nat.cast_nonneg _) rfl hFn
    (fun _ _ hij _ => by exact_mod_cast hij) hFmono hfront
  let ℓ := a - K
  have hℓa : ℓ ≤ a := Nat.sub_le _ _
  have hspan' : 3 * d * (n : ℝ) / 4 ≤ (ℓ : ℝ) := by
    simpa only [ℓ, Nat.cast_sub hKa.le] using hspan
  have hHℓ : H ≤ ℓ := by exact_mod_cast hHsmall.trans hspan'
  have hbudget' : (2 - s) * ((2 - (s - d / 4)) * (H : ℝ) + 2 * E) +
      5 * E * (1 - (s - d / 4)) < (1 - (s - d / 4)) ^ 2 * (ℓ : ℝ) :=
    hbudget.trans_le (mul_le_mul_of_nonneg_left hspan' (sq_nonneg _))
  have htail' : ∀ z, z ≤ ℓ →
      F a - (s - d / 4) * (z : ℝ) - E ≤ F (a - z) := by
    intro z hz
    have hza : z ≤ a := hz.trans hℓa
    have hKsub : K ≤ a - z := by dsimp [ℓ] at hz; omega
    have hh := htail (a - z) hKsub (Nat.sub_le _ _)
    rw [Nat.cast_sub hza] at hh
    nlinarith only [hh, hE]
  obtain ⟨h, hHh, hhℓ, hh⟩ := exists_discrete_cell_energy_obstruction G F hs
    (show s - d / 4 < s by linarith) hE hH hHℓ hℓa
    (fun t ht hta => hpoint t ht (hta.trans han))
    (fun t ht htℓ => hpointUpper t ht ((htℓ.trans hℓa).trans han))
    (fun t ht htℓ => hbush t ht ((htℓ.trans hℓa).trans han))
    htail' (fun i j hij hja => hFlip i j hij (hja.trans han))
    (by convert hgap using 1 <;> ring) hbudget'
  exact ⟨a, h, hKa, han, hHh, hhℓ.trans hℓa, hh⟩

/-- The stronger energy inequality at all resolutions rules out any fixed
amount of angular frontloading.  The tolerance and the number of recorded
levels are chosen before the profiles. -/
theorem small_frontloading_of_all_scale_energy {s d : ℝ}
    (hd : 0 < d) (hds : d ≤ s) (hs : s < 1) :
    ∃ ε : ℝ, ∃ n₀ : ℕ, 0 < ε ∧ 0 < n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ G F : ℕ → ℝ,
        F n = s * (n : ℝ) →
        (∀ i j, i ≤ j → j ≤ n → F i ≤ F j) →
        (∀ i j, i ≤ j → j ≤ n → F j - F i ≤ (j : ℝ) - i) →
        (∀ t, t ≤ n → (t : ℝ) - ε * n ≤ G t) →
        (∀ t, t ≤ n → G t ≤ 2 * (t : ℝ) + ε * n) →
        (∀ t, t ≤ n → s * (t : ℝ) - ε * n ≤ F t) →
        (∀ a h, a ≤ n → 0 < h → h ≤ a →
          ∃ y, h ≤ y ∧ y ≤ a ∧
            G y + F (a - y) ≤ F a + G h - F h + ε * n) →
        ∀ K, K ≤ n → F K < s * (K : ℝ) + d * n := by
  let β := s - d / 4
  have hβ : β < s := by dsimp [β]; linarith
  obtain ⟨H₀, ε, hH₀, hε, hHℓ, hbudgets⟩ :=
    profile_obstruction_budgets hs hβ (show 0 < 3 * d / 4 by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 / H₀) 1)
  have hn₀R : (0 : ℝ) < n₀ := lt_trans (by positivity) hn₀
  have hn₀N : 0 < n₀ := by exact_mod_cast hn₀R
  refine ⟨ε, n₀, hε, hn₀N, ?_⟩
  intro n hn G F hFn hmono hlip hpoint hpointUpper hbush henergy K hKn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn₀N.trans_le hn
  have hnN : 0 < n := hn₀N.trans_le hn
  have hn₀n : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hstart : 1 < H₀ * (n : ℝ) := by
    have hh : 1 / H₀ < (n : ℝ) := ((le_max_left _ _).trans_lt hn₀).trans_le hn₀n
    rw [div_lt_iff₀ hH₀] at hh
    nlinarith only [hh]
  let H : ℕ := ⌈H₀ * (n : ℝ)⌉₊
  have hHlower : H₀ * (n : ℝ) ≤ H := Nat.le_ceil _
  have hHupper : (H : ℝ) ≤ 2 * H₀ * n := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ H₀ * (n : ℝ) by positivity)
    change (H : ℝ) < H₀ * (n : ℝ) + 1 at hh
    linarith
  have hH : 0 < H := by
    have : (0 : ℝ) < H := (mul_pos hH₀ hnR).trans_le hHlower
    exact_mod_cast this
  have hHnormLow : H₀ ≤ (H : ℝ) / n := (le_div_iff₀ hnR).mpr hHlower
  have hHnormHigh : (H : ℝ) / n ≤ 2 * H₀ := (div_le_iff₀ hnR).mpr hHupper
  obtain ⟨hgap₀, hbudget₀⟩ := hbudgets ((H : ℝ) / n) ε hHnormLow hHnormHigh le_rfl
  have hHsmall : (H : ℝ) ≤ 3 * d * (n : ℝ) / 4 := by
    have hh := mul_le_mul_of_nonneg_right hHℓ hnR.le
    nlinarith only [hHupper, hh]
  have hgap : 4 * (ε * n) < (d / 4) * (H : ℝ) := by
    convert mul_lt_mul_of_pos_right hgap₀ hnR using 1
    all_goals
      try dsimp [β]
      field_simp <;> ring
  have hbudget : (2 - s) * ((2 - (s - d / 4)) * (H : ℝ) + 2 * (ε * n)) +
      5 * (ε * n) * (1 - (s - d / 4)) <
        (1 - (s - d / 4)) ^ 2 * (3 * d * (n : ℝ) / 4) := by
    convert mul_lt_mul_of_pos_right hbudget₀ hnR using 1
    all_goals
      try dsimp [β]
      field_simp <;> ring
  apply lt_of_not_ge
  intro hfront
  obtain ⟨a, h, _, han, hHh, hha, hfail⟩ := frontloading_forces_energy_failure G F
    hKn hnN hd hds hs (mul_nonneg hε.le hnR.le) hH hHsmall hFn hmono hlip
    (fun t _ ht => hpoint t ht) (fun t _ ht => hpointUpper t ht)
    (fun t _ ht => hbush t ht) hfront hgap hbudget
  obtain ⟨y, hhy, hya, hy⟩ := henergy a h han (hH.trans_le hHh) hha
  exact (not_lt_of_ge hy) (hfail y hhy hya)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
