-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.NonconcBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.NonconcParameters

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

structure NonconcScaleBudget (δ ε ℓ α ζ L : ℝ) (N : ℕ) : Prop where
  scale_le_one : δ ≤ 1
  frostman_le : δ ^ (-ℓ) ≤ δ ^ (-ε / 10)
  error_small : (4 : ℝ) ^ N * δ ^ (2 * α) < 1 / 10
  error_density : (4 : ℝ) ^ N * δ ^ (2 * α) ≤ δ ^ α / 2
  constant_bound : δ ^ (-ε / 100) *
    (δ ^ (-ℓ) * (32 * δ ^ (-(ℓ + 6 * α / ζ))) / δ ^ (2 * α)) ^ L ≤ δ ^ (-ε / 10)
  gain_bound : δ ^ (ε - 1) * (δ ^ (-ε / 10)) ^ (2 : ℕ) ≤
    (δ ^ α / 2) ^ (4 : ℕ) * δ ^ (ε / 10 - 1)

theorem exists_nonconc_scale_budget {ε L ζ : ℝ} (N : ℕ)
    (hε : 0 < ε) (hL : 1 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      NonconcScaleBudget δ ε (nonconcEll ε L) (nonconcAlpha ε L ζ) ζ L N := by
  let ℓ := nonconcEll ε L
  let α := nonconcAlpha ε L ζ
  obtain ⟨hℓ, hα, hℓsmall, hslack, hproj⟩ := nonconc_parameter_bounds hε hL hζ hζ1
  have hαpos : 0 < α := hα
  have hconstant : -ε / 10 < -ε / 100 - (2 * ℓ + 6 * α / ζ + 2 * α) * L := by
    change ε / 100 + L * (2 * ℓ + 6 * α / ζ + 2 * α) < ε / 10 at hslack
    nlinarith
  obtain ⟨d₁, hd₁, hd₁1, hb₁⟩ := exists_monomial_bound (20 * (4 : ℝ) ^ N)
    (a := 2 * α) (b := 0) (by positivity)
  obtain ⟨d₂, hd₂, hd₂1, hb₂⟩ := exists_monomial_bound (2 * (4 : ℝ) ^ N)
    (a := 2 * α) (b := α) (by linarith)
  obtain ⟨d₃, hd₃, hd₃1, hb₃⟩ := exists_monomial_bound ((32 : ℝ) ^ L) hconstant
  obtain ⟨d₄, hd₄, hd₄1, hb₄⟩ := exists_monomial_bound 16 hproj
  refine ⟨min d₁ (min d₂ (min d₃ d₄)), by positivity, ?_⟩
  intro δ hδ hsmall
  have hs₁ := hsmall.trans (min_le_left _ _)
  have hs₂ := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs₃ := ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs₄ := ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hs₁.trans hd₁1
  have he₁ : (4 : ℝ) ^ N * δ ^ (2 * α) < 1 / 10 := by
    have h := hb₁ δ hδ hs₁
    rw [Real.rpow_zero] at h
    nlinarith
  have he₂ : (4 : ℝ) ^ N * δ ^ (2 * α) ≤ δ ^ α / 2 := by
    have h := hb₂ δ hδ hs₂
    linarith
  have hbase : δ ^ (-ℓ) * (32 * δ ^ (-(ℓ + 6 * α / ζ))) / δ ^ (2 * α) =
      32 * δ ^ (-(2 * ℓ + 6 * α / ζ + 2 * α)) := by
    rw [show δ ^ (-ℓ) * (32 * δ ^ (-(ℓ + 6 * α / ζ))) =
      32 * (δ ^ (-ℓ) * δ ^ (-(ℓ + 6 * α / ζ))) by ring,
      mul_div_assoc, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 1
    congr 1
    ring
  have hconst_eq : δ ^ (-ε / 100) *
      (δ ^ (-ℓ) * (32 * δ ^ (-(ℓ + 6 * α / ζ))) / δ ^ (2 * α)) ^ L =
      (32 : ℝ) ^ L * δ ^ (-ε / 100 - (2 * ℓ + 6 * α / ζ + 2 * α) * L) := by
    rw [hbase, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity),
      ← Real.rpow_mul hδ.le]
    calc δ ^ (-ε / 100) * ((32 : ℝ) ^ L * δ ^ (-(2 * ℓ + 6 * α / ζ + 2 * α) * L)) =
        (32 : ℝ) ^ L * (δ ^ (-ε / 100) * δ ^ (-(2 * ℓ + 6 * α / ζ + 2 * α) * L)) := by ring
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; congr 1; ring
  have hconst : δ ^ (-ε / 100) *
      (δ ^ (-ℓ) * (32 * δ ^ (-(ℓ + 6 * α / ζ))) / δ ^ (2 * α)) ^ L ≤ δ ^ (-ε / 10) := by
    rw [hconst_eq]
    exact hb₃ δ hδ hs₃
  have hleft : (δ ^ α / 2) ^ (4 : ℕ) * δ ^ (ε / 10 - 1) =
      δ ^ (4 * α + ε / 10 - 1) / 16 := by
    rw [div_pow, ← Real.rpow_mul_natCast hδ.le α 4]
    norm_num
    rw [div_mul_eq_mul_div, ← Real.rpow_add hδ]
    congr 1
    congr 1
    ring
  have hright : δ ^ (ε - 1) * (δ ^ (-ε / 10)) ^ (2 : ℕ) = δ ^ (4 * ε / 5 - 1) := by
    rw [← Real.rpow_mul_natCast hδ.le (-ε / 10) 2, ← Real.rpow_add hδ]
    congr 1
    norm_num
    <;> ring
  refine ⟨hδ1, ?_, he₁, he₂, hconst, ?_⟩
  · exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [ℓ] at *; linarith)
  · change δ ^ (ε - 1) * (δ ^ (-ε / 10)) ^ (2 : ℕ) ≤ (δ ^ α / 2) ^ (4 : ℕ) * δ ^ (ε / 10 - 1)
    rw [hleft, hright]
    have h := hb₄ δ hδ hs₄
    change 16 * δ ^ (4 * ε / 5 - 1) ≤ δ ^ (4 * α + ε / 10 - 1) at h
    linarith

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
