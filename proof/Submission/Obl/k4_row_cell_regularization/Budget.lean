import Mathlib

/-!
# The exponent budget of the regularization

For `S, a, ε > 0` we fix the separation exponent `rho = min ε a` (`R = N ^ rho`), the input
loss exponent `eta` (`L = N ^ eta`), the number `levels` of weight levels of ratio `L`, and the
output loss `K = 2^30 J L^8`.  `budget` gives a threshold `N₀` above which every numerical
inequality of the regularization holds: `K ≤ R ≤ N ^ ε`, the mesh `h = N ^ (-a)` lies below
`2 / R`, the bins below the lowest level are negligible, and the interval cap at radius `2 / R`
gives the near-direction cap.
-/

namespace Submission.Obl.k4_row_cell_regularization

/-- The direction separation exponent: `R = N ^ rho a ε`. -/
noncomputable def rho (a ε : ℝ) : ℝ := min ε a

/-- The input loss exponent: `L = N ^ eta S a ε`. -/
noncomputable def eta (S a ε : ℝ) : ℝ := min (rho a ε / 16) (rho a ε * S / 64)

/-- The number of weight levels of ratio `L`. -/
noncomputable def levels (S a ε : ℝ) : ℕ := ⌈a / eta S a ε⌉₊ + 6

/-- The output loss `K = 2^30 J L^8`. -/
noncomputable def lossK (J : ℕ) (L : ℝ) : ℝ := 2 ^ 30 * (J : ℝ) * L ^ 8

theorem rho_pos {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) : 0 < rho a ε := lt_min hε ha

theorem eta_pos {S a ε : ℝ} (hS : 0 < S) (ha : 0 < a) (hε : 0 < ε) : 0 < eta S a ε := by
  have := rho_pos ha hε
  exact lt_min (by positivity) (by positivity)

theorem levels_pos (S a ε : ℝ) : 0 < levels S a ε := by
  unfold levels; omega

theorem one_le_lossK {J : ℕ} {L : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) : 1 ≤ lossK J L := by
  unfold lossK
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have : 1 ≤ L ^ 8 := one_le_pow₀ hL
  have : (1 : ℝ) ≤ 2 ^ 30 * (J : ℝ) := by nlinarith
  nlinarith

/-- The numerical inequalities of the regularization, above an explicit threshold. -/
theorem budget (S a ε : ℝ) (hS : 0 < S) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      128 ≤ N ^ eta S a ε ∧ 0 < N ^ (-a) ∧ N ^ (-a) < 1 ∧
      2 ≤ N ^ rho a ε ∧
      lossK (levels S a ε) (N ^ eta S a ε) ≤ N ^ rho a ε ∧
      N ^ rho a ε ≤ N ^ ε ∧
      N ^ (-a) ≤ 2 / N ^ rho a ε ∧
      128 * (N ^ eta S a ε) ^ 5 ≤ N ^ (-a) * (N ^ eta S a ε) ^ levels S a ε ∧
      512 * (levels S a ε : ℝ) * (N ^ eta S a ε) ^ 6 *
        lossK (levels S a ε) (N ^ eta S a ε) ^ 3 * 2 ^ S ≤ (N ^ rho a ε) ^ S := by
  set ρ := rho a ε with hρdef
  set η := eta S a ε with hηdef
  set J := levels S a ε with hJdef
  have hρ : 0 < ρ := rho_pos ha hε
  have hη : 0 < η := eta_pos hS ha hε
  have hηρ : η ≤ ρ / 16 := min_le_left _ _
  have hηρS : η ≤ ρ * S / 64 := min_le_right _ _
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρa : ρ ≤ a := min_le_right _ _
  have hJ0 : 0 < J := levels_pos S a ε
  have hJ : (J : ℝ) = (⌈a / η⌉₊ : ℝ) + 6 := by
    rw [hJdef, levels]; push_cast; rfl
  have hρS : 0 < ρ * S / 2 := by positivity
  have e1 := (tendsto_rpow_atTop hη).eventually_ge_atTop (128 : ℝ)
  have e2 := (tendsto_rpow_atTop hρ).eventually_ge_atTop (2 : ℝ)
  have e3 := (tendsto_rpow_atTop (half_pos hρ)).eventually_ge_atTop (2 ^ 30 * (J : ℝ))
  have e4 := (tendsto_rpow_atTop hρS).eventually_ge_atTop
    ((2 : ℝ) ^ 99 * 2 ^ S * (J : ℝ) ^ 4)
  have e5 := Filter.eventually_ge_atTop (2 : ℝ)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max N₁ 2, le_max_right _ _, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN₁ N (le_trans (le_max_left _ _) hN)
  have hN1 : 1 < N := by linarith
  have hN0 : 0 < N := by linarith
  have hN1' : 1 ≤ N := hN1.le
  set L := N ^ η with hLdef
  have hL0 : 0 < L := Real.rpow_pos_of_pos hN0 η
  -- powers of `L` are powers of `N`
  have hLpow : ∀ n : ℕ, L ^ n = N ^ (η * n) := fun n => by
    rw [hLdef, Real.rpow_mul_natCast hN0.le]
  have hhalf : N ^ (ρ / 2) * N ^ (ρ / 2) = N ^ ρ := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hhalfS : N ^ (ρ * S / 2) * N ^ (ρ * S / 2) = (N ^ ρ) ^ S := by
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le]; ring_nf
  refine ⟨h1, Real.rpow_pos_of_pos hN0 _,
    Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_lt_zero.mpr ha), h2, ?_, ?_, ?_, ?_, ?_⟩
  · -- `K ≤ R`
    have hL8 : L ^ 8 ≤ N ^ (ρ / 2) := by
      rw [hLpow]
      apply Real.rpow_le_rpow_of_exponent_le hN1'
      push_cast; linarith
    unfold lossK
    calc 2 ^ 30 * (J : ℝ) * L ^ 8 ≤ N ^ (ρ / 2) * N ^ (ρ / 2) := by
          apply mul_le_mul h3 hL8 (by positivity) (by positivity)
      _ = N ^ ρ := hhalf
  · -- `R ≤ N ^ ε`
    exact Real.rpow_le_rpow_of_exponent_le hN1' hρε
  · -- `h ≤ 2 / R`
    have hR0 : 0 < N ^ ρ := Real.rpow_pos_of_pos hN0 ρ
    calc N ^ (-a) ≤ N ^ (-ρ) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ = 1 / N ^ ρ := by rw [Real.rpow_neg hN0.le, one_div]
      _ ≤ 2 / N ^ ρ := div_le_div_of_nonneg_right (by norm_num) hR0.le
  · -- the lowest level is negligible
    have hceil : a / η ≤ (⌈a / η⌉₊ : ℝ) := Nat.le_ceil _
    have hηJ : a + 6 * η ≤ η * J := by
      rw [hJ]
      have : a = η * (a / η) := by field_simp
      nlinarith
    have hsix : N ^ (6 * η) ≤ N ^ (-a) * L ^ J := by
      rw [hLpow, ← Real.rpow_add hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN1'
      linarith
    have hL6 : L ^ 6 = N ^ (6 * η) := by rw [hLpow]; push_cast; ring_nf
    calc 128 * L ^ 5 ≤ L * L ^ 5 := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = L ^ 6 := by ring
      _ = N ^ (6 * η) := hL6
      _ ≤ N ^ (-a) * L ^ J := hsix
  · -- the near-direction cap
    have hL30 : L ^ 30 ≤ N ^ (ρ * S / 2) := by
      rw [hLpow]
      apply Real.rpow_le_rpow_of_exponent_le hN1'
      push_cast; linarith
    have hS2 : (0 : ℝ) < 2 ^ S := Real.rpow_pos_of_pos (by norm_num) S
    unfold lossK
    calc 512 * (J : ℝ) * L ^ 6 * (2 ^ 30 * (J : ℝ) * L ^ 8) ^ 3 * 2 ^ S
        = ((2 : ℝ) ^ 99 * 2 ^ S * (J : ℝ) ^ 4) * L ^ 30 := by ring
      _ ≤ N ^ (ρ * S / 2) * N ^ (ρ * S / 2) := by
          apply mul_le_mul h4 hL30 (by positivity) (by positivity)
      _ = (N ^ ρ) ^ S := hhalfS

end Submission.Obl.k4_row_cell_regularization
