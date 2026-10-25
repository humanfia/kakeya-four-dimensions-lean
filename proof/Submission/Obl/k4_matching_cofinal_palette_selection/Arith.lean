import Mathlib

/-!
# The large-`q`, large-`N` count of bad steps (o069)

With `C = 6(J+1)` windows, palette count `M = (⌊N^(6/q)⌋₊ + 2)^2`,
`θ = δ/(4(J+1)q)` and `α = 2^(-(J+10))`, the finite palette theorem plus two
Markov bounds give, for each active order `v`, a count `b v` of bad steps with
`b v * (θ log N α) ≤ C log M + L`.  Since `log M ≤ 2 log 3 + (12/q) log N`,
each `b v` is at most `288 (J+1)^2 2^(J+10)/δ + 1` once `N` is large
(depending on `q`), and the total over `v ∈ [1, J]` is at most `δ q` once `q`
is large (depending on `J`, `δ` only).
-/

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- `log M ≤ 2 log 3 + (12/q) log N` for the palette count `M`. -/
theorem log_paletteCount_le (N : ℝ) (hN : 1 ≤ N) (q : ℕ) :
    Real.log (((⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 : ℕ) : ℝ) ≤
      2 * Real.log 3 + 12 / (q : ℝ) * Real.log N := by
  set w : ℝ := N ^ (6 / (q : ℝ)) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hN (by positivity)
  have hfl : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le (by linarith)
  have hpos : (0 : ℝ) < (⌊w⌋₊ : ℝ) + 2 := by positivity
  have hle : (⌊w⌋₊ : ℝ) + 2 ≤ 3 * w := by linarith
  push_cast
  rw [Real.log_pow]
  have h1 : Real.log ((⌊w⌋₊ : ℝ) + 2) ≤ Real.log (3 * w) := Real.log_le_log hpos hle
  have h2 : Real.log (3 * w) = Real.log 3 + 6 / (q : ℝ) * Real.log N := by
    rw [Real.log_mul (by norm_num) (by linarith), hw,
      Real.log_rpow (by linarith : (0 : ℝ) < N)]
  have h3 : (12 : ℝ) / (q : ℝ) = 2 * (6 / (q : ℝ)) := by ring
  rw [h3]
  push_cast
  nlinarith

/-- The uniform large-`q`/large-`N` estimate for the bad-step count. -/
theorem bad_count_arith (J : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q → ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ L : ℕ, L ≤ q → ∀ b : ℕ → ℕ,
      (∀ v : ℕ, 1 ≤ v → v ≤ J →
        (b v : ℝ) * (δ / (4 * ((J : ℝ) + 1) * (q : ℝ)) * Real.log N *
          (1 / (2 : ℝ) ^ (J + 10))) ≤
        ((6 * (J + 1) : ℕ) : ℝ) * Real.log (((⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 : ℕ) : ℝ) +
          (L : ℝ)) →
      (∑ v ∈ Finset.Icc 1 J, (b v : ℝ)) ≤ δ * (q : ℝ) := by
  set K : ℝ := (2 : ℝ) ^ (J + 10) with hK
  have hKpos : 0 < K := by positivity
  set B₀ : ℝ := 288 * ((J : ℝ) + 1) ^ 2 * K / δ with hB₀
  have hB₀pos : 0 ≤ B₀ := by positivity
  refine ⟨⌈(J : ℝ) * (B₀ + 1) / δ⌉₊, ?_⟩
  intro q hQq hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hJpos : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  set A₁ : ℝ := 12 * ((J : ℝ) + 1) * Real.log 3 + q with hA₁
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA₁pos : 0 < A₁ := by positivity
  set τ : ℝ := δ / (4 * ((J : ℝ) + 1) * (q : ℝ)) * (1 / K) with hτ
  have hτpos : 0 < τ := by positivity
  refine ⟨max 2 (Real.exp (A₁ / τ)), le_max_left _ _, ?_⟩
  intro N hN L hL b hb
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hlogN : A₁ / τ ≤ Real.log N := by
    have := le_trans (le_max_right _ _) hN
    calc A₁ / τ = Real.log (Real.exp (A₁ / τ)) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) this
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le (by positivity) hlogN
  have hA₁le : A₁ ≤ τ * Real.log N := by
    rw [div_le_iff₀ hτpos] at hlogN
    linarith
  have hB₀τ : B₀ * τ = 72 * ((J : ℝ) + 1) / (q : ℝ) := by
    rw [hB₀, hτ]
    field_simp
    ring
  have hbv : ∀ v : ℕ, 1 ≤ v → v ≤ J → (b v : ℝ) ≤ B₀ + 1 := by
    intro v hv1 hvJ
    have h := hb v hv1 hvJ
    have hM := log_paletteCount_le N hN1 q
    have hLq : (L : ℝ) ≤ q := by exact_mod_cast hL
    have hlhs : (b v : ℝ) * (δ / (4 * ((J : ℝ) + 1) * (q : ℝ)) * Real.log N *
        (1 / (2 : ℝ) ^ (J + 10))) = (b v : ℝ) * (τ * Real.log N) := by
      rw [hτ, hK]; ring
    rw [hlhs] at h
    have hC : ((6 * (J + 1) : ℕ) : ℝ) = 6 * ((J : ℝ) + 1) := by push_cast; ring
    rw [hC] at h
    have hrhs : 6 * ((J : ℝ) + 1) *
        Real.log (((⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 : ℕ) : ℝ) + (L : ℝ) ≤
        A₁ + 72 * ((J : ℝ) + 1) / (q : ℝ) * Real.log N := by
      have h6 : 0 ≤ 6 * ((J : ℝ) + 1) := by positivity
      have := mul_le_mul_of_nonneg_left hM h6
      have e : 6 * ((J : ℝ) + 1) * (2 * Real.log 3 + 12 / (q : ℝ) * Real.log N) =
          12 * ((J : ℝ) + 1) * Real.log 3 + 72 * ((J : ℝ) + 1) / (q : ℝ) * Real.log N := by
        ring
      rw [hA₁]
      linarith
    have hfin : (b v : ℝ) * (τ * Real.log N) ≤ (B₀ + 1) * (τ * Real.log N) := by
      have e : (B₀ + 1) * (τ * Real.log N) = B₀ * τ * Real.log N + τ * Real.log N := by ring
      rw [e, hB₀τ]
      linarith
    exact le_of_mul_le_mul_right hfin (by positivity)
  calc ∑ v ∈ Finset.Icc 1 J, (b v : ℝ) ≤ ∑ _v ∈ Finset.Icc 1 J, (B₀ + 1) :=
        Finset.sum_le_sum (fun v hv =>
          hbv v (Finset.mem_Icc.mp hv).1 (Finset.mem_Icc.mp hv).2)
    _ = (J : ℝ) * (B₀ + 1) := by simp; ring
    _ ≤ δ * (q : ℝ) := by
      have hceil : (J : ℝ) * (B₀ + 1) / δ ≤ (q : ℝ) :=
        le_trans (Nat.le_ceil _) (by exact_mod_cast hQq)
      rw [div_le_iff₀ hδ] at hceil
      linarith

end Submission.Obl.k4_matching_cofinal_palette_selection
