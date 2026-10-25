-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_twisted_projection_volume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_cinematic_parameter_lthreehalf
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine
import Submission.WZ.Obl.wz_normalized_projection_iteration
import Submission.WZ.Obl.wz_large_offset_projection_reduction

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_twisted_projection_volume

abbrev V := LeanEval.Analysis.WangZahlKakeya.Space

def Tube (δ : ℝ) (x v : V) : Set V :=
  Metric.thickening δ (segment ℝ x (x + v))

def FamilyData (η δ : ℝ) (n : ℕ) (x v : Fin n → V)
    (Y : Fin n → Set V) : Prop :=
  0 < n ∧ (∀ i, ‖v i‖ = 1) ∧
  (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
  (∀ i j, i ≠ j → MeasureTheory.volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1/2 : ENNReal) * MeasureTheory.volume (Tube δ (x i) (v i))) ∧
  (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ Tube δ (x i) (v i)) ∧
  ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤
    Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))

def Frostman (η δ : ℝ) (n : ℕ) (x v : Fin n → V) : Prop :=
  ∀ W : Set V, Convex ℝ W →
    ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W

theorem familyData_mono {η η' δ : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : FamilyData η δ n x v Y) : FamilyData η' δ n x v Y := by
  rcases h with ⟨hn, hv, hball, hsep, hmeas, hsub, hdense⟩
  refine ⟨hn, hv, hball, hsep, hmeas, hsub, le_trans ?_ hdense⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη) (Nat.cast_nonneg n))
    (sq_nonneg δ)

theorem frostman_mono {η η' δ : ℝ} {n : ℕ} {x v : Fin n → V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : Frostman η δ n x v) : Frostman η' δ n x v := by
  intro W hW
  refine (h W hW).trans ?_
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη))
      (Nat.cast_nonneg n))) _

end WangZahlLot.Obl.wz_twisted_projection_volume

open WangZahlLot.Obl.wz_twisted_projection_volume in
theorem WangZahlLot.wz_twisted_projection_volume : (fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop => ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) → ∀ f : ℝ → ℝ, (ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) → ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume ((fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' (⋃ i, Y i))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i)))) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v))) := by
  have hbounded := WangZahlLot.wz_normalized_projection_iteration
    (WangZahlLot.wz_normalized_projection_coarse_fine
      WangZahlLot.wz_cinematic_parameter_lthreehalf)
  have hlarge := WangZahlLot.wz_large_offset_projection_reduction hbounded
  intro ε hε
  obtain ⟨η₁, hη₁, d₁, hd₁, h₁⟩ := hbounded ε hε
  obtain ⟨η₂, hη₂, d₂, hd₂, h₂⟩ := hlarge ε hε
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, min d₁ d₂, lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hd hδ100 n x v Y hH ht hF f hf
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hData : FamilyData (min η₁ η₂) δ n x v Y := hH
  have hCount : Frostman (min η₁ η₂) δ n x v := hF
  by_cases hc : |f 0| ≤ 1
  · exact h₁ δ hδ (hd.trans (min_le_left _ _)) hδ100 n x v Y
      (familyData_mono hδ hδ1 (min_le_left _ _) hData) ht
      (frostman_mono hδ hδ1 (min_le_left _ _) hCount) f hf hc
  · exact h₂ δ hδ (hd.trans (min_le_right _ _)) hδ100 n x v Y
      (familyData_mono hδ hδ1 (min_le_right _ _) hData) ht
      (frostman_mono hδ hδ1 (min_le_right _ _) hCount) f hf (lt_of_not_ge hc)
