-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Counts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- A containment count with its natural parent-scale normalization. -/
abbrev RelativeCount (b L δ : ℝ) {n : ℕ} (x v : Fin n → Space) : Prop :=
  ∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * b ^ 2) ≤
      ENNReal.ofReal (L * n) * volume U

/-- Relative Frostman counts also provide a Katz--Tao coefficient for the fine family. -/
theorem convexCount_of_relative {b L δ : ℝ} (hb : 0 < b)
    {n : ℕ} {x v : Fin n → Space} (h : RelativeCount b L δ x v) :
    ConvexCount δ (L * n * (δ / b) ^ 2) x v := by
  intro U hU
  calc
    _ = ENNReal.ofReal ((δ / b) ^ 2) *
        ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * b ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((δ / b) ^ 2) * (ENNReal.ofReal (L * n) * volume U) :=
      mul_le_mul' le_rfl (h U hU)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 2
      ring

/-- Testing a single fine tube bounds the reciprocal of its relative count coefficient. -/
theorem relative_coefficient_lower {b L δ : ℝ} (hb : 0 < b) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (hn : 0 < n)
    {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (h : RelativeCount b L δ x v) : 1 ≤ 56 * L * n * (δ / b) ^ 2 := by
  let i : Fin n := ⟨0, hn⟩
  have hc : 1 ≤ Set.ncard {j | tube δ (x j) (v j) ⊆ tube δ (x i) (v i)} := by
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    exact ⟨i, Set.Subset.rfl⟩
  have hu := h (tube δ (x i) (v i)) (tube_convex δ (x i) (v i))
  have hvol := tube_volume_upper hδ.le hδ1 (x i) (v i) (hv i)
  have he : ENNReal.ofReal (b ^ 2) ≤ ENNReal.ofReal (L * n * (56 * δ ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal ((Set.ncard {j | tube δ (x j) (v j) ⊆ tube δ (x i) (v i)} : ℝ) * b ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hr : (1 : ℝ) ≤ (Set.ncard {j | tube δ (x j) (v j) ⊆ tube δ (x i) (v i)} : ℝ) := by exact_mod_cast hc
        nlinarith only [mul_le_mul_of_nonneg_right hr (sq_nonneg b)]
      _ ≤ ENNReal.ofReal (L * n) * volume (tube δ (x i) (v i)) := hu
      _ ≤ ENNReal.ofReal (L * n) * ENNReal.ofReal (56 * δ ^ 2) := mul_le_mul' le_rfl hvol
      _ = _ := (ENNReal.ofReal_mul (mul_nonneg hL (Nat.cast_nonneg n))).symm
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have hsq : 0 < b ^ 2 := sq_pos_of_pos hb
  apply (mul_le_mul_iff_left₀ hsq).mp
  field_simp
  nlinarith only [hr]

end WangZahlLot.Obl.wz_separated_scales_gain
