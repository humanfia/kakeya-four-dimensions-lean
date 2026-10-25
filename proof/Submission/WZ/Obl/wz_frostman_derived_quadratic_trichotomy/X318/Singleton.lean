-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Singleton.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.OneScale

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Singleton.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set Metric MeasureTheory
open scoped ENNReal

/-- At error at least the inverse tube volume, even a singleton has all-scale covers. -/
lemma singleton_sticky_of_large_error {δ ξ : ℝ} (hδ : 0 < δ)
    (hK : 1 ≤ δ ^ (-ξ)) (hmass : 1 ≤ δ ^ (-ξ) * δ ^ 2)
    (x v : Space) (hv : ‖v‖ = 1) :
    Sticky ξ δ (fun _ : Fin 1 => Tube δ x v) := by
  classical
  intro ρ₀ hδρ hρ1
  have hρ0 : 0 ≤ ρ₀ := hδ.le.trans hδρ
  have hsub : Tube δ x v ⊆ Tube ρ₀ x v := thickening_mono hδρ _
  have hc : ncard {i : Fin 1 | Tube δ x v ⊆ Tube ρ₀ x v} = 1 := by simp [hsub]
  refine ⟨ρ₀, le_rfl, hρ1, le_mul_of_one_le_left hρ0 hK, 1, by omega,
    (fun _ => x), (fun _ => v), (fun _ => hv), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  · intro i
    exact ⟨0, hsub, fun _ _ => Subsingleton.elim _ _⟩
  · intro j
    exact ⟨0, hsub⟩
  · intro j j'
    simpa only [hc, Nat.cast_one, mul_one] using hK
  · intro j W _
    rw [hc]
    simp only [Nat.cast_one, mul_one]
    by_cases hW : Tube δ x v ⊆ W
    · have hc' : ncard {i : Fin 1 | Tube δ x v ⊆ Tube ρ₀ x v ∧ Tube δ x v ⊆ W} = 1 := by
        simp [hsub, hW]
      rw [hc', Nat.cast_one, one_mul]
      calc
        ENNReal.ofReal (ρ₀ ^ 2) ≤ ENNReal.ofReal (δ ^ (-ξ) * δ ^ 2) :=
          ENNReal.ofReal_le_ofReal ((by nlinarith : ρ₀ ^ 2 ≤ 1).trans hmass)
        _ = ENNReal.ofReal (δ ^ (-ξ)) * ENNReal.ofReal (δ ^ 2) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)
        _ ≤ ENNReal.ofReal (δ ^ (-ξ)) * volume W :=
          mul_le_mul' le_rfl ((tube_volume_lower hδ x v hv).trans (measure_mono hW))
    · simp [hW]

/-- For xi at least two, the non-stickiness assumption of the frozen theorem is impossible. -/
theorem exists_sticky_subfamily_of_two_le {δ ξ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 2 ≤ ξ)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧
      Sticky ξ δ (fun j => Tube δ (x (g j)) (v (g j))) := by
  have hK : 1 ≤ δ ^ (-ξ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hmass : 1 ≤ δ ^ (-ξ) * δ ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hδ]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  let i : Fin n := ⟨0, hn⟩
  refine ⟨1, (fun _ => i), (fun _ _ _ => Subsingleton.elim _ _), by omega, ?_⟩
  exact singleton_sticky_of_large_error hδ hK hmass (x i) (v i) (hv i)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
