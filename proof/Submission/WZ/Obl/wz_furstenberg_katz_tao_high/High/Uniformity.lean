-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Uniformity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/Uniformity.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Leaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileUniformity

/-!
# The uniformity leaf

`uniformityLeaf`: `UniformityLeaf s` for `0 < s < 1`, from x0651's
`small_frontloading_of_all_scale_energy` (ported by x0672 under `O214/`), which needs an exactly
monotone, `1`-Lipschitz bush profile with `F n = s n`. A measured profile `F` with additive
slack `e n` is replaced by its envelope `H j = min_{i ≤ n} (F i + max 0 (j - i))`, shifted so
that it ends at `s n`: `H` is monotone and `1`-Lipschitz, and `F - e n ≤ H ≤ F` on `[0, n]`, so
every hypothesis passes to the envelope with slack `O(e n)`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

noncomputable section

/-- The `1`-Lipschitz monotone envelope of `F` on `[0, n]`. -/
def envelope (F : ℕ → ℝ) (n : ℕ) (j : ℕ) : ℝ :=
  (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun i => F i + max 0 ((j : ℝ) - i))

theorem envelope_le (F : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) : envelope F n j ≤ F j := by
  unfold envelope
  have h := Finset.inf'_le (fun i => F i + max 0 ((j : ℝ) - i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  simp only [sub_self, max_self, add_zero] at h
  exact h

theorem envelope_mono (F : ℕ → ℝ) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    envelope F n i ≤ envelope F n j := by
  unfold envelope
  apply Finset.le_inf'
  intro k hk
  refine (Finset.inf'_le _ hk).trans ?_
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  have : max 0 ((i : ℝ) - k) ≤ max 0 ((j : ℝ) - k) := max_le_max le_rfl (by linarith)
  linarith

theorem envelope_lip (F : ℕ → ℝ) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    envelope F n j - envelope F n i ≤ (j : ℝ) - i := by
  unfold envelope
  obtain ⟨k, hk, hkmin⟩ := Finset.exists_mem_eq_inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun i' => F i' + max 0 ((i : ℝ) - i'))
  rw [hkmin]
  have h1 := Finset.inf'_le (fun i' => F i' + max 0 ((j : ℝ) - i')) hk
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have h2 : max 0 ((j : ℝ) - k) ≤ max 0 ((i : ℝ) - k) + ((j : ℝ) - i) := by
    apply max_le
    · have := le_max_left 0 ((i : ℝ) - k); linarith
    · have := le_max_right 0 ((i : ℝ) - k); linarith
  beta_reduce at h1 ⊢
  linarith

/-- With approximate monotonicity and slope, the envelope is within `e n` of `F`. -/
theorem le_envelope (F : ℕ → ℝ) {n : ℕ} {E : ℝ}
    (hmono : ∀ i j : ℕ, i ≤ j → j ≤ n → F i ≤ F j + E)
    (hlip : ∀ i j : ℕ, i ≤ j → j ≤ n → F j - F i ≤ ((j : ℝ) - i) + E) {j : ℕ} (hj : j ≤ n) :
    F j - E ≤ envelope F n j := by
  unfold envelope
  apply Finset.le_inf'
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rcases le_total k j with hkj | hjk
  · have h1 := hlip k j hkj hj
    have h2 := le_max_right 0 ((j : ℝ) - k)
    beta_reduce
    linarith
  · have h1 := hmono j k hjk hkn
    have h2 := le_max_left 0 ((j : ℝ) - k)
    beta_reduce
    linarith

/-- **The uniformity leaf** from x0651's `small_frontloading_of_all_scale_energy`. -/
theorem uniformityLeaf {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : UniformityLeaf s := by
  intro d hd
  obtain ⟨d', hd'⟩ : ∃ d' : ℝ, d' = min (d / 2) s := ⟨_, rfl⟩
  have hd'0 : 0 < d' := by rw [hd']; exact lt_min (by positivity) hs0
  have hd's : d' ≤ s := by rw [hd']; exact min_le_right _ _
  have hd'd : d' ≤ d / 2 := by rw [hd']; exact min_le_left _ _
  obtain ⟨εx, n₀, hεx, _, hX⟩ :=
    Multiscale.small_frontloading_of_all_scale_energy hd'0 hd's hs1
  refine ⟨min (εx / 8) (d / 8), lt_min (by positivity) (by positivity), n₀, ?_⟩
  intro n hn F G hFn hmono hlip hFge hG hprem t ht
  set e := min (εx / 8) (d / 8) with he
  have he0 : 0 < e := lt_min (by positivity) (by positivity)
  have heεx : e ≤ εx / 8 := min_le_left _ _
  have hed : e ≤ d / 8 := min_le_right _ _
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hen : 0 ≤ e * n := by positivity
  have heεn : 8 * (e * n) ≤ εx * n := by nlinarith
  have hedn : 8 * (e * n) ≤ d * n := by nlinarith
  -- the shifted envelope
  set H : ℕ → ℝ := envelope F n with hH
  set δ : ℝ := s * n - H n with hδ
  have hHle : ∀ j, j ≤ n → H j ≤ F j := fun j hj => envelope_le F hj
  have hHge : ∀ j, j ≤ n → F j - e * n ≤ H j := fun j hj => le_envelope F hmono hlip hj
  have hFn' := abs_le.mp hFn
  have hδ1 : δ ≤ 2 * (e * n) := by
    have := hHge n le_rfl
    rw [hδ]; linarith
  have hδ2 : -(e * n) ≤ δ := by
    have := hHle n le_rfl
    rw [hδ]; linarith
  have hfin := hX n hn G (fun j => H j + δ)
    (by simp only [hδ]; ring)
    (fun i j hij _ => by
      have := envelope_mono F n hij
      simp only [hH] at this ⊢
      linarith)
    (fun i j hij _ => by
      have := envelope_lip F n hij
      simp only [hH] at this ⊢
      linarith)
    (fun t ht => by
      have := (hG t ht).1
      linarith)
    (fun t ht => by
      have := (hG t ht).2
      linarith)
    (fun t ht => by
      have h1 := hFge t ht
      have h2 := hHge t ht
      beta_reduce
      linarith)
    (fun a h ha hh hha => by
      obtain ⟨y, hy1, hy2, hy3⟩ := hprem h a hh hha ha
      refine ⟨y, hy1, hy2, ?_⟩
      have h1 := hHle (a - y) (le_trans (Nat.sub_le a y) ha)
      have h2 := hHge a ha
      have h3 := hHle h (le_trans hha ha)
      beta_reduce
      linarith)
    t ht
  have h1 := hHge t ht
  have h2 : d' * n ≤ d / 2 * n := mul_le_mul_of_nonneg_right hd'd hn'
  beta_reduce at hfin
  linarith

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
