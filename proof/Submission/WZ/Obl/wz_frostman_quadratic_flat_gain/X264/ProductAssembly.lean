-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.ProductAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file ProductAssembly.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory

/-- Two lower estimates combine through the cellwise product inequality, including
when the measured sets have infinite measure. -/
lemma measure_product_lower {F G t C D : ℝ} (hF0 : 0 ≤ F) (hC : 0 < C) (hD : 0 < D)
    {E Z : Set Space} (hF : ENNReal.ofReal F ≤ ENNReal.ofReal (C * t))
    (hG : ENNReal.ofReal G ≤ volume Z)
    (hprod : ENNReal.ofReal t * volume Z ≤ ENNReal.ofReal D * volume E) :
    ENNReal.ofReal (F * G / (C * D)) ≤ volume E := by
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr (mul_pos hC hD)).ne' ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal (C * D) * ENNReal.ofReal (F * G / (C * D)) =
        ENNReal.ofReal F * ENNReal.ofReal G := by
      rw [← ENNReal.ofReal_mul (mul_pos hC hD).le,
        mul_div_cancel₀ _ (mul_pos hC hD).ne', ENNReal.ofReal_mul hF0]
    _ ≤ ENNReal.ofReal (C * t) * volume Z := mul_le_mul' hF hG
    _ = ENNReal.ofReal C * (ENNReal.ofReal t * volume Z) := by
      rw [ENNReal.ofReal_mul hC.le, mul_assoc]
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal D * volume E) := mul_le_mul' le_rfl hprod
    _ = ENNReal.ofReal (C * D) * volume E := by
      rw [ENNReal.ofReal_mul hC.le, mul_assoc]

/-- The shape and count factors cancel exactly in the fine/coarse product. -/
lemma prism_scalar_product {δ a b N Q : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (Af Ac ef ec σ ω : ℝ) :
    (Af * δ ^ ef * (δ / a) ^ ω * (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2)) *
      (Ac * δ ^ ec * b ^ ω * (Q * (a * b) ^ 2) ^ (σ / 2)) / 39366 =
    (Af * Ac / 39366) * δ ^ (ω + ef + ec) * (b / a) ^ ω *
      (Q * N * δ ^ 4) ^ (σ / 2) := by
  have hshape : (δ / a) ^ ω * b ^ ω = δ ^ ω * (b / a) ^ ω := by
    rw [← Real.mul_rpow (by positivity) hb.le, ← Real.mul_rpow hδ.le (by positivity)]
    congr 1
    ring
  have hweight : (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) *
      (Q * (a * b) ^ 2) ^ (σ / 2) = (Q * N * δ ^ 4) ^ (σ / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hpower : δ ^ ef * δ ^ ec * δ ^ ω = δ ^ (ω + ef + ec) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = (Af * Ac / 39366) * (δ ^ ef * δ ^ ec) * ((δ / a) ^ ω * b ^ ω) *
      ((N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) *
        (Q * (a * b) ^ 2) ^ (σ / 2)) := by ring
    _ = (Af * Ac / 39366) * (δ ^ ef * δ ^ ec * δ ^ ω) * (b / a) ^ ω *
      (Q * N * δ ^ 4) ^ (σ / 2) := by rw [hshape, hweight]; ring
    _ = _ := by rw [hpower]

/-- All losses in the retained incidence count enter the final exponent linearly. -/
lemma prism_power_product_lower {δ a b N Q n Af Ac ef ec σ ω r e : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hn : 0 ≤ n) (hAf : 0 ≤ Af) (hAc : 0 ≤ Ac)
    (hσ : 0 ≤ σ) (hcount : δ ^ r * n ≤ Q * N) (hloss : ef + ec + r * σ / 2 ≤ e) :
    (Af * Ac / 39366) * δ ^ (ω + e) * (b / a) ^ ω * (n * δ ^ 4) ^ (σ / 2) ≤
    (Af * δ ^ ef * (δ / a) ^ ω * (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2)) *
      (Ac * δ ^ ec * b ^ ω * (Q * (a * b) ^ 2) ^ (σ / 2)) / 39366 := by
  rw [prism_scalar_product hδ ha hb hN hQ]
  have hret := Real.rpow_le_rpow (by positivity : 0 ≤ δ ^ r * n * δ ^ 4)
    (mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ δ ^ 4))
    (by positivity : 0 ≤ σ / 2)
  have heq : (δ ^ r * n * δ ^ 4) ^ (σ / 2) =
      δ ^ (r * σ / 2) * (n * δ ^ 4) ^ (σ / 2) := by
    rw [mul_assoc (δ ^ r) n, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hδ.le]
    congr 2
    ring
  rw [heq] at hret
  have hp : δ ^ (ω + e) ≤ δ ^ (ω + ef + ec + r * σ / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    _ ≤ (Af * Ac / 39366) * δ ^ (ω + ef + ec + r * σ / 2) * (b / a) ^ ω *
        (n * δ ^ 4) ^ (σ / 2) := by gcongr
    _ = (Af * Ac / 39366) * δ ^ (ω + ef + ec) * (b / a) ^ ω *
        (δ ^ (r * σ / 2) * (n * δ ^ 4) ^ (σ / 2)) := by
      rw [Real.rpow_add hδ]
      ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
