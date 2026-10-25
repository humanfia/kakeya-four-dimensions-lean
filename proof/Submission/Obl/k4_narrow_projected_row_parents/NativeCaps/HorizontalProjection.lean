import Submission.Lib.K4AffineMeshCaps.Transport

namespace Submission.Obl.k4_narrow_projected_row_parents.NativeCaps

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- The first two coordinates of a three-dimensional mesh cell. -/
def horizontalMesh (ξ : ℝ) (z : Fin 3 → ℝ) : Fin 2 → ℤ :=
  fun e => baseMesh ξ z (Fin.castLE (by decide : 2 ≤ 3) e)

/-- Sum the bounded transverse coordinate of a base-cell cap. Any unchanged
external palette weight remains a factor in the resulting horizontal cap. -/
theorem horizontal_cap_of_base_cap {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (Z : Ω → Fin 3 → ℝ) (v : Ω → ℤ)
    {ξ K C : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hY : ∀ᵐ ω ∂ν, |Z ω 2| ≤ K) (weight : ℝ≥0∞) (j : ℤ)
    (hcap : ∀ q : Fin 3 → ℤ, ν {ω | baseMesh ξ (Z ω) = q ∧ v ω = j} ≤
      ENNReal.ofReal (C * ξ ^ 3) * weight) (c : Fin 2 → ℤ) :
    ν {ω | horizontalMesh ξ (Z ω) = c ∧ v ω = j} ≤
      ENNReal.ofReal (6 * K * C * ξ ^ 2) * weight := by
  classical
  obtain ⟨F, hcard, hcover⟩ := interval_mesh_cover hξ (zero_le_one.trans hK) 0
  have hratio : 1 ≤ K / ξ := (le_div_iff₀ hξ).mpr (by simpa only [one_mul] using hξ1.trans hK)
  have hcard' : (F.card : ℝ) ≤ 6 * K / ξ := by
    calc (F.card : ℝ) ≤ 4 * K / ξ + 2 := hcard
      _ ≤ 4 * K / ξ + 2 * (K / ξ) := by linarith
      _ = 6 * K / ξ := by ring
  have hsub : {ω | horizontalMesh ξ (Z ω) = c ∧ v ω = j} ≤ᵐ[ν]
      ⋃ y ∈ F, {ω | baseMesh ξ (Z ω) = ![c 0, c 1, y] ∧ v ω = j} := by
    filter_upwards [hY] with ω hω hmem
    have heq : baseMesh ξ (Z ω) = ![c 0, c 1, baseMesh ξ (Z ω) 2] := by
      ext e
      fin_cases e
      · exact congr_fun hmem.1 0
      · exact congr_fun hmem.1 1
      · rfl
    refine mem_iUnion.mpr ⟨baseMesh ξ (Z ω) 2, mem_iUnion.mpr ⟨?_, heq, hmem.2⟩⟩
    exact hcover (Z ω 2) (by simpa only [sub_zero] using hω)
  calc ν {ω | horizontalMesh ξ (Z ω) = c ∧ v ω = j}
      ≤ ν (⋃ y ∈ F, {ω | baseMesh ξ (Z ω) = ![c 0, c 1, y] ∧ v ω = j}) :=
        measure_mono_ae hsub
    _ ≤ ∑ y ∈ F, ν {ω | baseMesh ξ (Z ω) = ![c 0, c 1, y] ∧ v ω = j} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ F, ENNReal.ofReal (C * ξ ^ 3) * weight :=
      Finset.sum_le_sum fun y hy => hcap ![c 0, c 1, y]
    _ = ENNReal.ofReal ((F.card : ℝ) * (C * ξ ^ 3)) * weight := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg F.card)]
    _ ≤ _ := by
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      calc (F.card : ℝ) * (C * ξ ^ 3) ≤ (6 * K / ξ) * (C * ξ ^ 3) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
        _ = 6 * K * C * ξ ^ 2 := by field_simp

end

end Submission.Obl.k4_narrow_projected_row_parents.NativeCaps
