-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.NonconcParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

noncomputable def nonconcEll (ε L : ℝ) : ℝ := ε / (10000 * L)
noncomputable def nonconcAlpha (ε L ζ : ℝ) : ℝ := nonconcEll ε L * ζ / 100

/-- The Frostman loss depends only on the desired gain and the uniform
bootstrap depth; only the hypergraph density loss depends on `ζ`. -/
theorem nonconc_parameter_bounds {ε L ζ : ℝ} (hε : 0 < ε) (hL : 1 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    0 < nonconcEll ε L ∧ 0 < nonconcAlpha ε L ζ ∧
      nonconcEll ε L ≤ ε / 10 ∧
      ε / 100 + L * (2 * nonconcEll ε L + 6 * nonconcAlpha ε L ζ / ζ +
        2 * nonconcAlpha ε L ζ) < ε / 10 ∧
      4 * nonconcAlpha ε L ζ + ε / 10 - 1 < 4 * ε / 5 - 1 := by
  let ℓ := nonconcEll ε L
  let α := nonconcAlpha ε L ζ
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hℓ : 0 < ℓ := by dsimp [ℓ, nonconcEll]; positivity
  have hα : 0 < α := by dsimp [α, nonconcAlpha]; positivity
  have hLℓ : L * ℓ = ε / 10000 := by
    dsimp [ℓ, nonconcEll]
    field_simp
  have hℓsmall : ℓ ≤ ε / 10000 := by
    have hh := mul_le_mul_of_nonneg_right hL hℓ.le
    nlinarith
  have hαsmall : α ≤ ℓ / 100 := by
    dsimp [α, nonconcAlpha, ℓ]
    have hh := mul_le_mul_of_nonneg_left hζ1 hℓ.le
    dsimp [ℓ] at hh
    linarith
  have hLα : L * α ≤ (L * ℓ) / 100 := by
    have hh := mul_le_mul_of_nonneg_left hαsmall hLp.le
    nlinarith
  have hquot : 6 * α / ζ = 3 * ℓ / 50 := by
    dsimp [α, nonconcAlpha, ℓ]
    field_simp
    <;> ring
  refine ⟨hℓ, hα, by linarith, ?_, ?_⟩
  · change ε / 100 + L * (2 * ℓ + 6 * α / ζ + 2 * α) < ε / 10
    rw [hquot]
    nlinarith
  · change 4 * α + ε / 10 - 1 < 4 * ε / 5 - 1
    linarith

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
