-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Basic

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The loss in the exponent when the two error constants in E are both δ⁻η. -/
theorem normalized_expression {δ : ℝ} (hδ : 0 < δ) (a ω ε η σ : ℝ) (n : ℕ) :
    a * δ ^ (ω + ε) * (δ ^ (-η))⁻¹ * (n * δ ^ 2) *
      ((δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) * (n * δ)) ^ (-σ) =
    a * δ ^ (ω + ε + η * (1 - σ / 2)) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
  have hinv : (δ ^ (-η))⁻¹ = δ ^ η := by rw [Real.rpow_neg hδ.le, inv_inv]
  have hinner : (δ ^ (-η)) ^ (-(3 / 2 : ℝ)) * δ ^ (-η) = δ ^ (η / 2) := by
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    congr 1
    ring
  rw [hinv, hinner, Real.mul_rpow (Real.rpow_nonneg hδ.le _) (by positivity),
    ← Real.rpow_mul hδ.le]
  calc
    _ = a * (δ ^ (ω + ε) * δ ^ η * δ ^ (η / 2 * -σ)) *
        (n * δ ^ 2) * (n * δ) ^ (-σ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      rw [show ω + ε + η + η / 2 * -σ = ω + ε + η * (1 - σ / 2) by ring]

/-- A direct application of E yields the usual bound with an arbitrarily small
positive exponent loss. It does not yet yield the strict improvement in o019. -/
theorem Estimate.normalized {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : Estimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ n x v Y,
        Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
        ENNReal.ofReal (a * δ ^ (ω + ε) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
          volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, hbound⟩ := hE (ε / 2) (by positivity)
  let η := min η₀ (ε / 2)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨a, ha, η, hη, ?_⟩
  intro δ hδ hδ100 n x v Y h
  have hδ1 : δ ≤ 1 := by linarith
  have hm : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have h' : Hypotheses δ η₀ (δ ^ (-η)) (δ ^ (-η)) n x v Y :=
    h.mono hδ hδ1 (min_le_left _ _) le_rfl le_rfl
  have hb := hbound δ hδ hδ100 _ _ hm hm n x v Y h'
  rw [normalized_expression hδ] at hb
  apply le_trans (ENNReal.ofReal_le_ofReal _) hb
  have hle : ω + ε / 2 + η * (1 - σ / 2) ≤ ω + ε := by
    have hηle : η ≤ ε / 2 := min_le_right _ _
    nlinarith [mul_nonneg hη.le hσ]
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hle
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp ha.le) (by positivity))
    (Real.rpow_nonneg (by positivity) _)

/-- The interval of allowable intermediate scales is nonempty. -/
theorem intermediate_scale {δ ω : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (_hω : 0 < ω) (hω1 : ω ≤ 1) :
    δ ^ (1 - ω / 100) ≤ δ ^ (1 / 2 : ℝ) ∧
      δ ^ (1 / 2 : ℝ) ≤ δ ^ (ω / 100) := by
  constructor <;> apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1 <;> linarith

/-- The normalized E bound necessarily has a positive loss for the exponent range
of o019. This identifies why its direct substitution is insufficient. -/
theorem normalized_loss_pos {σ η ε : ℝ} (hσ : σ ≤ 1 / 2)
    (hη : 0 < η) (hε : 0 < ε) : 0 < ε + η * (1 - σ / 2) := by
  have hfactor : 0 < 1 - σ / 2 := by linarith
  positivity

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
