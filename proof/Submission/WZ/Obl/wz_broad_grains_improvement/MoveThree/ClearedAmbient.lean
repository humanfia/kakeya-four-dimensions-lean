-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClearedAmbient.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClearedAmbient.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.FrozenClear
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AmbientRefinement

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

/-- Endpoint clearance can be imposed on the ambient shading itself, so
every subsequent refinement inherits it. The original tube indices and
both stage scales stay fixed. -/
theorem cleared_ambient_stage_uniform {ω ζ ε Kc : ℝ}
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζω : ζ ≤ ω / 1000)
    (hε : 0 < ε) (hKc : 1 ≤ Kc) :
    ∃ θ d₀ : ℝ, 0 < θ ∧ θ ≤ ε / 4 ∧ 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
        A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c j, J ω ζ δ h ρ c n x v Y j →
        ∃ Y₀ : Fin n → Set V,
          (∀ i, Y₀ i ⊆ Y i ∧ Disjoint (Y₀ i)
            (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ (Kc * c) (x i) (v i))) ∧
          O (δ ^ (ε / 4)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y₀ i) ∧
          A δ ε (δ ^ (-ε)) (δ ^ (-ε)) n x v Y₀ ∧ J ω ζ δ ε ρ c n x v Y₀ j := by
  obtain ⟨θ, d₀, hθ, hθε, hd₀, HC⟩ := Clear.endpoint_clear_J_frozen
    hω hω1 hζ hζω (ε := ε / 4) (by positivity) hKc
  refine ⟨θ, min d₀ 1, hθ, hθε, lt_min hd₀ one_pos, min_le_right _ _, ?_⟩
  intro δ h hδ hδ0 hh n x v Y hA ρ c j hJ
  have hδ1 : δ ≤ 1 := hδ0.trans (min_le_right _ _)
  obtain ⟨S, Y₀, N, y, w, f, a, g, hclear, hC, hρ, hg, hbr, hH, hstop⟩ :=
    HC δ h hδ (hδ0.trans (min_le_left _ _)) hh n x v Y hA ρ c j hJ
  have hsupport : ∀ i, i ∉ S → Y₀ i = ∅ := fun i => (hC.1 i).2.2
  have hretain : O (δ ^ (ε / 4)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y₀ i) :=
    hC.2.1.trans_eq (Clear.sum_supported hsupport)
  have hhε : h ≤ ε := by linarith
  have hAm := admissible_mono hδ hδ1 hhε hA
  have hA₀ : A δ ε (δ ^ (-ε)) (δ ^ (-ε)) n x v Y₀ := by
    refine ⟨hA.1, fun i => ⟨(hA.2.1 i).1, (hA.2.1 i).2.1,
      (hC.1 i).1, (hC.1 i).2.1.trans (hA.2.1 i).2.2.2⟩,
      hA.2.2.1, ?_, hAm.2.2.2.2⟩
    calc
      _ ≤ O (δ ^ (h + ε / 4) * n * δ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : h + ε / 4 ≤ ε))
          (Nat.cast_nonneg n)
      _ = O (δ ^ (ε / 4)) * O (δ ^ h * n * δ ^ 2) := by
        dsimp only [O]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ O (δ ^ (ε / 4)) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hretain
  have hC₀ : C δ (ε / 4) n x v Y₀ S Y₀ ρ N y w f True := by
    refine ⟨fun i => ⟨(hC.1 i).1, Subset.rfl, hsupport i⟩, ?_, hC.2.2⟩
    rw [Clear.sum_supported hsupport]
    apply mul_le_of_le_one_left'
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one hδ.le hδ1 (by positivity))
  exact ⟨Y₀, fun i => ⟨(hC.1 i).2.1, hclear i⟩, hretain, hA₀,
    stage_mono hδ hδ1 (by linarith : ε / 4 ≤ ε)
      ⟨S, Y₀, N, y, w, f, a, g, hC₀, hρ, hg, hbr, hH, hstop⟩⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
