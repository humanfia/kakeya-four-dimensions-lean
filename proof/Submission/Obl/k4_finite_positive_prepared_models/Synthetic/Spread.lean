import Mathlib

/-!
# Digit spreading for the synthetic hidden coordinate

`spread e e₁ G i` rewrites the `G` base-`2^e₁` digits of `i` as base-`2^e` digits. With
`e₁ ≤ e` this is injective on `[0, 2^(e₁ G))`, its values lie below `2^(e G)`, and dividing by
`2^(e m)` corresponds to dropping `m` digits of `i`. The synthetic model uses it to place a
Cantor-type hidden coordinate of dimension `e₁ / e`. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

/-- Spread the `G` lowest base-`2^e₁` digits of `i` into base `2^e`. -/
def spread (e e₁ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | G + 1, i => i % 2 ^ e₁ + 2 ^ e * spread e e₁ G (i / 2 ^ e₁)

variable {e e₁ : ℕ}

theorem spread_lt (h : e₁ ≤ e) (G i : ℕ) : spread e e₁ G i < 2 ^ (e * G) := by
  induction G generalizing i with
  | zero => simp [spread]
  | succ G ih =>
    have h1 : i % 2 ^ e₁ < 2 ^ e :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) h)
    have h2 := ih (i / 2 ^ e₁)
    simp only [spread]
    rw [show e * (G + 1) = e + e * G by ring, pow_add]
    calc i % 2 ^ e₁ + 2 ^ e * spread e e₁ G (i / 2 ^ e₁)
        < 2 ^ e + 2 ^ e * spread e e₁ G (i / 2 ^ e₁) := by omega
      _ = 2 ^ e * (spread e e₁ G (i / 2 ^ e₁) + 1) := by ring
      _ ≤ 2 ^ e * 2 ^ (e * G) := Nat.mul_le_mul_left _ h2

theorem spread_div (h : e₁ ≤ e) (G m i : ℕ) :
    spread e e₁ (G + m) i / 2 ^ (e * m) = spread e e₁ G (i / 2 ^ (e₁ * m)) := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    have h1 : i % 2 ^ e₁ < 2 ^ e :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) h)
    rw [show G + (m + 1) = (G + m) + 1 by ring]
    simp only [spread]
    rw [show e * (m + 1) = e + e * m by ring, pow_add, ← Nat.div_div_eq_div_mul]
    have h2 : (i % 2 ^ e₁ + 2 ^ e * spread e e₁ (G + m) (i / 2 ^ e₁)) / 2 ^ e =
        spread e e₁ (G + m) (i / 2 ^ e₁) := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h1, zero_add]
    rw [h2, ih, Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    ring

theorem spread_mod (h : e₁ ≤ e) (G i : ℕ) :
    spread e e₁ (G + 1) i % 2 ^ e = i % 2 ^ e₁ := by
  have h1 : i % 2 ^ e₁ < 2 ^ e :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) h)
  simp only [spread]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]

theorem spread_injective (h : e₁ ≤ e) (G : ℕ) {i i' : ℕ} (hi : i < 2 ^ (e₁ * G))
    (hi' : i' < 2 ^ (e₁ * G)) (heq : spread e e₁ G i = spread e e₁ G i') : i = i' := by
  induction G generalizing i i' with
  | zero => simp at hi hi'; omega
  | succ G ih =>
    have hm : i % 2 ^ e₁ = i' % 2 ^ e₁ := by
      rw [← spread_mod h G i, ← spread_mod h G i', heq]
    have hd : spread e e₁ G (i / 2 ^ e₁) = spread e e₁ G (i' / 2 ^ e₁) := by
      have := spread_div h G 1 i
      have h' := spread_div h G 1 i'
      simp only [mul_one] at this h'
      rw [← this, ← h', heq]
    have hlt : ∀ j, j < 2 ^ (e₁ * (G + 1)) → j / 2 ^ e₁ < 2 ^ (e₁ * G) := by
      intro j hj
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      rw [show e₁ * (G + 1) = e₁ * G + e₁ by ring, pow_add] at hj
      exact hj
    have hq := ih (hlt i hi) (hlt i' hi') hd
    rw [← Nat.div_add_mod i (2 ^ e₁), ← Nat.div_add_mod i' (2 ^ e₁), hq, hm]

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
