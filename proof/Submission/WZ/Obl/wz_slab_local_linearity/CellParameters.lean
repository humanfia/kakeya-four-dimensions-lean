-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.SmallPowers

namespace WangZahlLot.Obl.wz_slab_local_linearity

/-- All fixed constants in the cell argument are absorbed by three strict gaps
between power exponents. -/
theorem exists_cell_parameters {σ τ A δ₀ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ)
    (hA : 0 < A) (hδ₀ : 0 < δ₀) :
    ∃ η ρ₀ : ℝ, 0 < η ∧ 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ρ ≤ 1 / 100 ∧ Real.sqrt ρ / 1000 ≤ δ₀ ∧ ρ ^ η ≤ 1 / 1000 ∧
      (4896 * A ^ 2) * ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) ≤
        ρ ^ (-(3 : ℝ) / 2 + σ / 2 + η) ∧
      (256 * 415872 * 2000000000000000 * A ^ 4) *
        ρ ^ (-6 + 2 * σ + τ / 2 - 9 * η) ≤ ρ ^ (-6 + 2 * σ + 4 * η) ∧
      12000 * ρ ^ (-2 * η) ≤ ρ ^ (-τ / 2) := by
  let η := min σ τ / 100
  have hη : 0 < η := div_pos (lt_min hσ hτ) (by norm_num)
  have hησ : 100 * η ≤ σ := by have hh := min_le_left σ τ; dsimp [η]; linarith
  have hητ : 100 * η ≤ τ := by have hh := min_le_right σ τ; dsimp [η]; linarith
  obtain ⟨rR, hrR, hR⟩ := exists_small_monomial
    (show -(3 : ℝ) / 2 + σ / 2 + η < -(3 : ℝ) / 2 + σ - 3 * η by linarith)
    (show 0 < 4896 * A ^ 2 by positivity)
  obtain ⟨rT, hrT, hT⟩ := exists_small_monomial
    (show -6 + 2 * σ + 4 * η < -6 + 2 * σ + τ / 2 - 9 * η by linarith)
    (show 0 < 256 * 415872 * 2000000000000000 * A ^ 4 by positivity)
  obtain ⟨rA, hrA, hAD⟩ := exists_small_monomial
    (show -τ / 2 < -2 * η by linarith) (show (0 : ℝ) < 12000 by norm_num)
  obtain ⟨rκ, hrκ, hκ⟩ := exists_small_rpow hη (show (0 : ℝ) < 1 / 1000 by norm_num)
  let ρ₀ := min (1 / 100) (min (δ₀ ^ 2) (min rR (min rT (min rA rκ))))
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  refine ⟨η, ρ₀, hη, hρ₀, ?_⟩
  intro ρ hρ hsmall
  have hh := le_min_iff.mp hsmall
  have hδ := le_min_iff.mp hh.2
  have hR' := le_min_iff.mp hδ.2
  have hT' := le_min_iff.mp hR'.2
  have hA' := le_min_iff.mp hT'.2
  refine ⟨hh.1, ?_, hκ ρ hρ hA'.2, hR ρ hρ hR'.1, hT ρ hρ hT'.1, hAD ρ hρ hA'.1⟩
  have hs : Real.sqrt ρ ≤ δ₀ := by nlinarith [Real.sq_sqrt hρ.le, Real.sqrt_nonneg ρ]
  linarith

end WangZahlLot.Obl.wz_slab_local_linearity
