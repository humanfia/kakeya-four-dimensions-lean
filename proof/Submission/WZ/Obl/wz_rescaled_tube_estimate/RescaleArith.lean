-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.RescaleArith.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Exponent bookkeeping for the local rescaling of `E(σ,ω)`

`far_arith` compares the bound that `E` gives for the rescaled subfamily with the target bound
for the fibre; `close_arith` is the elementary bound used when the rescaled scale is not small.
-/

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate

/-- The rescaled `E` bound dominates the target bound for the fibre. Here `κ` is the contraction,
`k` the size of the extracted subfamily and `D` the extraction loss. -/
theorem far_arith {a κ D δ ρ m l ε₁ η ε σ ω : ℝ} {n k : ℕ}
    (ha : 0 < a) (hκ : 0 < κ) (hD : 0 < D) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hm : 1 ≤ m) (hl : 1 ≤ l) (hk : 0 < k) (hcount : δ ^ η * n ≤ 384 * D * k)
    (hε₁ : 0 ≤ ε₁) (hεsum : ε₁ + η ≤ ε) :
    (a * κ ^ (ω + ε₁) * (κ / (κ ^ (-(3 / 2 : ℝ)) * κ ^ 3)) ^ (-σ) / (384 * D)) * δ ^ ε *
        (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ) *
        (κ ^ 3 * (ρ⁻¹) ^ 2) ≤
      a * (κ * ρ⁻¹ * δ) ^ (ω + ε₁) * (m / κ)⁻¹ * (k * (κ * ρ⁻¹ * δ) ^ 2) *
        ((m / κ) ^ (-(3 / 2 : ℝ)) * (l / κ ^ 3 * n / k) * (k * (κ * ρ⁻¹ * δ))) ^ (-σ) := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := hδρ.trans hρ1
  have hm0 : 0 < m := by linarith
  have hl0 : 0 < l := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set s : ℝ := ρ⁻¹ * δ with hs_def
  have hs0 : 0 < s := by positivity
  have hsδ : δ ≤ s := by
    rw [hs_def, le_inv_mul_iff₀ hρ]
    exact mul_le_of_le_one_left hδ.le hρ1
  have hdiv : δ / ρ = s := by rw [hs_def]; ring
  have hndiv : (n : ℝ) * δ / ρ = n * s := by rw [hs_def]; ring
  rw [hdiv, hndiv]
  set X : ℝ := m ^ (-(3 / 2 : ℝ)) * l * (n * s) with hX_def
  have hX0 : 0 ≤ X := by positivity
  set c₀ : ℝ := κ / (κ ^ (-(3 / 2 : ℝ)) * κ ^ 3) with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  have hbase : (m / κ) ^ (-(3 / 2 : ℝ)) * (l / κ ^ 3 * n / k) * (k * (κ * s)) = c₀ * X := by
    rw [Real.div_rpow hm0.le hκ.le, hX_def, hc₀_def]
    have h1 : κ ^ (-(3 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hκ _).ne'
    field_simp
  have hκs : κ * ρ⁻¹ * δ = κ * s := by rw [hs_def]; ring
  rw [hκs, hbase, Real.mul_rpow hc₀.le hX0, Real.mul_rpow hκ.le hs0.le,
    Real.rpow_add hs0]
  have hkey : δ ^ ε * n ≤ s ^ ε₁ * (384 * D * k) := by
    have h1 : δ ^ ε ≤ δ ^ ε₁ * δ ^ η := by
      rw [← Real.rpow_add hδ]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεsum
    have h2 : δ ^ ε₁ ≤ s ^ ε₁ := Real.rpow_le_rpow hδ.le hsδ hε₁
    calc
      δ ^ ε * n ≤ δ ^ ε₁ * δ ^ η * n := by gcongr
      _ = δ ^ ε₁ * (δ ^ η * n) := by ring
      _ ≤ s ^ ε₁ * (384 * D * k) := by
        apply mul_le_mul h2 hcount (by positivity) (Real.rpow_nonneg hs0.le _)
  set Common : ℝ := a * κ ^ (ω + ε₁) * c₀ ^ (-σ) / (384 * D) * s ^ ω * m⁻¹ * X ^ (-σ) *
    κ ^ 3 * s ^ 2 with hCommon
  have hC0 : 0 ≤ Common := by positivity
  have hsq : δ ^ 2 * (ρ⁻¹) ^ 2 = s ^ 2 := by rw [hs_def]; ring
  calc
    _ = Common * (δ ^ ε * n) := by
      rw [hCommon, ← hsq]
      ring
    _ ≤ Common * (s ^ ε₁ * (384 * D * k)) := mul_le_mul_of_nonneg_left hkey hC0
    _ = _ := by
      rw [hCommon]
      field_simp

/-- The elementary bound: if `n (s^4) δ^η ≤ Q` and `s^(-5) ≤ B` (with `s = δ/ρ`), the target
bound is at most the trivial union bound `δ^η δ²`, provided `κ Q B δ^(ε - 2η) ≤ 1`. -/
theorem close_arith {κR δ ρ m l η ε σ ω Q B : ℝ} {n : ℕ}
    (hκR : 0 ≤ κR) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hm : 1 ≤ m) (hl : 1 ≤ l)
    (hn : 0 < n) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (hcount : (n : ℝ) * (ρ⁻¹ * δ) ^ 4 * δ ^ η ≤ Q)
    (hB : (ρ⁻¹ * δ) ^ (-(5 : ℝ)) ≤ B)
    (hsmall : κR * Q * B * δ ^ (ε - 2 * η) ≤ 1) :
    κR * δ ^ ε * (δ / ρ) ^ ω * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * δ / ρ)) ^ (-σ) ≤
      δ ^ η * δ ^ 2 := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hm0 : 0 < m := by linarith
  have hl0 : 0 < l := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set s : ℝ := ρ⁻¹ * δ with hs_def
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs_def, inv_mul_le_iff₀ hρ, mul_one]; exact hδρ
  have hdiv : δ / ρ = s := by rw [hs_def]; ring
  have hndiv : (n : ℝ) * δ / ρ = n * s := by rw [hs_def]; ring
  rw [hdiv, hndiv]
  -- the `m` and `l` factors are at most one
  have hY : (m ^ (-(3 / 2 : ℝ)) * l * (n * s)) ^ (-σ) ≤ m ^ ((3 / 2 : ℝ) * σ) * (n * s) ^ (-σ) := by
    have h1 : m ^ (-(3 / 2 : ℝ)) * (n * s) ≤ m ^ (-(3 / 2 : ℝ)) * l * (n * s) := by
      have : 0 < m ^ (-(3 / 2 : ℝ)) * (n * s) := by positivity
      nlinarith
    have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (neg_nonpos.mpr hσ)
    have h3 : (m ^ (-(3 / 2 : ℝ)) * (n * s)) ^ (-σ) = m ^ ((3 / 2 : ℝ) * σ) * (n * s) ^ (-σ) := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hm0.le]
      congr 2
      ring
    exact h2.trans h3.le
  have hmpow : m⁻¹ * m ^ ((3 / 2 : ℝ) * σ) ≤ 1 := by
    have h1 : m ^ ((3 / 2 : ℝ) * σ) ≤ m ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hm (by linarith)
    rw [Real.rpow_one] at h1
    rw [inv_mul_le_iff₀ hm0, mul_one]
    exact h1
  have hsω : s ^ ω ≤ 1 := Real.rpow_le_one hs0.le hs1 hω
  have hns : (n * s) ^ (-σ) ≤ s ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hs0 (by nlinarith) (neg_nonpos.mpr hσ)
  have hs5 : s ^ (-σ) ≤ s ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by linarith)
  -- the count
  have hn' : (n : ℝ) ≤ Q * s ^ (-(4 : ℝ)) * δ ^ (-η) := by
    have h4 : s ^ (-(4 : ℝ)) * s ^ 4 = 1 := by
      rw [Real.rpow_neg hs0.le, ← Real.rpow_natCast]
      simp only [Nat.cast_ofNat]
      field_simp
    have hη : δ ^ (-η) * δ ^ η = 1 := by
      rw [← Real.rpow_add hδ]; simp
    calc
      (n : ℝ) = (n * s ^ 4 * δ ^ η) * (s ^ (-(4 : ℝ)) * δ ^ (-η)) := by
        rw [show (n * s ^ 4 * δ ^ η) * (s ^ (-(4 : ℝ)) * δ ^ (-η)) =
          n * (s ^ (-(4 : ℝ)) * s ^ 4) * (δ ^ (-η) * δ ^ η) by ring, h4, hη]
        ring
      _ ≤ Q * (s ^ (-(4 : ℝ)) * δ ^ (-η)) := by gcongr
      _ = _ := by ring
  have hs45 : s ^ (-(4 : ℝ)) * s ^ (-(1 : ℝ)) = s ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_add hs0]; norm_num
  have hδe : δ ^ ε * δ ^ (-η) = δ ^ (ε - 2 * η) * δ ^ η := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
  calc
    κR * δ ^ ε * s ^ ω * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * l * (n * s)) ^ (-σ)
        ≤ κR * δ ^ ε * 1 * m⁻¹ * (n * δ ^ 2) * (m ^ ((3 / 2 : ℝ) * σ) * (n * s) ^ (-σ)) := by
          gcongr
    _ = κR * δ ^ ε * (m⁻¹ * m ^ ((3 / 2 : ℝ) * σ)) * (n * δ ^ 2) * (n * s) ^ (-σ) := by ring
    _ ≤ κR * δ ^ ε * 1 * (n * δ ^ 2) * s ^ (-(1 : ℝ)) := by
          gcongr
          exact hns.trans hs5
    _ ≤ κR * δ ^ ε * 1 * ((Q * s ^ (-(4 : ℝ)) * δ ^ (-η)) * δ ^ 2) * s ^ (-(1 : ℝ)) := by
          gcongr
    _ = κR * Q * (s ^ (-(4 : ℝ)) * s ^ (-(1 : ℝ))) * (δ ^ ε * δ ^ (-η)) * δ ^ 2 := by ring
    _ = (κR * Q * s ^ (-(5 : ℝ)) * δ ^ (ε - 2 * η)) * (δ ^ η * δ ^ 2) := by
          rw [hs45, hδe]; ring
    _ ≤ (κR * Q * B * δ ^ (ε - 2 * η)) * (δ ^ η * δ ^ 2) := by
          gcongr
          · have hQ : 0 ≤ Q := le_trans (by positivity) hcount
            positivity
    _ ≤ 1 * (δ ^ η * δ ^ 2) := by gcongr
    _ = δ ^ η * δ ^ 2 := one_mul _

end WangZahlLot.Obl.wz_rescaled_tube_estimate
