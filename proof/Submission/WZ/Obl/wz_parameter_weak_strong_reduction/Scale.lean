-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.Scale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_parameter_weak_strong_reduction.Layers

namespace WangZahlLot.Obl.wz_parameter_weak_strong_reduction

open MeasureTheory Set
open scoped ENNReal

/-- With a polynomial bound on the multiplicity, finitely many bands convert a
weak bound at a smaller error exponent to the desired strong bound. -/
theorem weak_strong_scale_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) (hf : Measurable f) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ)
    (hK : 3 ≤ ε / 6 * ((K + 1 : ℕ) : ℝ))
    (hloss : ((K + 1 : ℕ) : ℝ) ≤ δ ^ (-(ε / 2)))
    (hlow : ∀ x, f x = 0 ∨ 1 ≤ f x)
    (hupp : ∀ x, f x ≤ ENNReal.ofReal (δ ^ (-3 : ℝ)))
    (hweak : ∀ lam : ℝ, 1 ≤ lam → μ {x | ENNReal.ofReal lam ≤ f x} ≤
      ENNReal.ofReal (δ ^ (-(ε / 4)) * lam ^ (-(3 / 2 : ℝ)))) :
    (∫⁻ x, (f x) ^ (3 / 2 : ℝ) ∂μ) ≤ ENNReal.ofReal (δ ^ (-ε)) := by
  let t : ℕ → ℝ := fun j => δ ^ (-(ε / 6) * (j : ℝ))
  have ht : ∀ j, 0 ≤ t j := fun j => Real.rpow_nonneg hδ.le _
  have ht1 : ∀ j, 1 ≤ t j := by
    intro j
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg j)
  have hbound : ∀ x, f x ≤ ENNReal.ofReal (t (K + 1)) := by
    intro x
    refine (hupp x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith [hK])
  have hprod (j : ℕ) :
      t (j + 1) ^ (3 / 2 : ℝ) * (δ ^ (-(ε / 4)) * t j ^ (-(3 / 2 : ℝ))) =
        δ ^ (-(ε / 2)) := by
    dsimp [t]
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le,
      ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  calc
    (∫⁻ x, (f x) ^ (3 / 2 : ℝ) ∂μ) ≤
        ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (t (j + 1) ^ (3 / 2 : ℝ)) *
          μ {x | ENNReal.ofReal (t j) ≤ f x} :=
      integral_le_layers μ f hf t ht (3 / 2) (by norm_num) K
        (by simpa [t] using hlow) hbound
    _ ≤ ∑ _j ∈ Finset.range (K + 1), ENNReal.ofReal (δ ^ (-(ε / 2))) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ENNReal.ofReal (t (j + 1) ^ (3 / 2 : ℝ)) *
            ENNReal.ofReal (δ ^ (-(ε / 4)) * t j ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul' le_rfl (hweak (t j) (ht1 j))
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ht _) _), hprod]
    _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * δ ^ (-(ε / 2))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (δ ^ (-(ε / 2)) * δ ^ (-(ε / 2))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg hδ.le _))
    _ = ENNReal.ofReal (δ ^ (-ε)) := by
      rw [← Real.rpow_add hδ]
      congr 2
      ring

end WangZahlLot.Obl.wz_parameter_weak_strong_reduction
