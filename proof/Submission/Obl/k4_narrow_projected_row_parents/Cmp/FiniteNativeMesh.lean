/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/FiniteNativeMesh.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.FiniteComparisonMesh
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CoarserNativeCaps

/-! Construct comparison meshes from primitive original native and palette caps. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem exists_finite_native_mesh {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (hν : ν ≤ μ)
    (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    (hnorm : ∀ᵐ p ∂ν, ‖Z p‖ ≤ 1 / 8)
    (signal : Ω → ℝ) (condition : Ω → Prop) (hcondition : ∀ᵐ p ∂ν, condition p)
    {a d C V σ : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hV : 0 < V)
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 24) (palette : ℝ≥0∞)
    (hcap : ∀ R : ℝ, a ≤ R → ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ (WithLp.ofLp (Z p)) = q ∧
        ⌊signal p / R⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * V * R ^ d * σ ^ 3) * palette) :
    ∃ M : ComparisonMesh ν,
      M.base = Z ∧ M.diameter = 3 * σ ∧ (∑ _j : Fin M.n, M.vol) ≤ 1 ∧
      ∀ R : ℝ, a ≤ R → ∀ q j,
        ν {p | M.code p = q ∧ ⌊signal p / R⌋ = j} ≤
          (ENNReal.ofReal (C * (V * a ^ d) * (R / a) ^ d) * palette) * M.vol := by
  obtain ⟨M, hbase, hvol, hdiam, hcount, htransfer⟩ :=
    exists_finite_comparison_mesh ν Z hZ hnorm hσ hσsmall
  have hvolume : (∑ _j : Fin M.n, M.vol) ≤ 1 := by
    rw [hvol]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_one.mpr hcount
  refine ⟨M, hbase, hdiam, hvolume, ?_⟩
  intro R hRa q j
  have hR : 0 ≤ R := ha.le.trans hRa
  apply htransfer (ENNReal.ofReal (C * (V * a ^ d) * (R / a) ^ d) * palette)
    (fun p => ⌊signal p / R⌋ = j) (fun raw => ?_) q
  calc
    ν {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ (WithLp.ofLp (Z p)) = raw ∧
        ⌊signal p / R⌋ = j} ≤
      ν {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ (WithLp.ofLp (Z p)) = raw ∧
        ⌊signal p / R⌋ = j ∧ condition p} := by
      apply measure_mono_ae
      filter_upwards [hcondition] with p hp hmem
      exact ⟨hmem.1, hmem.2, hp⟩
    _ ≤ μ {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ (WithLp.ofLp (Z p)) = raw ∧
        ⌊signal p / R⌋ = j ∧ condition p} := hν _
    _ ≤ ENNReal.ofReal (C * V * R ^ d * σ ^ 3) * palette := hcap R hRa raw j
    _ = _ := by
      have heq : C * V * R ^ d = C * (V * a ^ d) * (R / a) ^ d := by
        rw [fine_reference_scale ha hR]
        ring
      rw [heq, ENNReal.ofReal_mul (by positivity)]
      ac_rfl

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
