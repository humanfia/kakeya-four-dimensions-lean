-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.QuantitativeCells
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ParameterChoice
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Basic
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_regular_transverse_affine_cells`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_regular_transverse_affine_cells/`
belong to this obligation.
-/

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

/-- The obligation, stated with the named input and output predicates. -/
theorem regular_transverse_affine_cells (s : ℝ) (hs : 0 < s) :
    ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E),
        Admissible (δ ^ η) δ n x v Y → Cells δ (δ ^ s) n x v Y := by
  obtain ⟨η, hη, δ₁, hδ₁, hδ₁small, hpar⟩ := asymptotic_iteration_parameters s hs
  obtain ⟨δ₂, hδ₂, hδ₂small, hcard⟩ := exists_card_cutoff
  refine ⟨η, hη, min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁small, ?_⟩
  intro δ hδ hδmax n x v Y hA
  obtain ⟨N, K, τ, κ, t, θ, hp, hinit, hret, hbottom⟩ :=
    hpar δ hδ (hδmax.trans (min_le_left _ _))
  have hnmax := hcard δ (δ ^ η) n x v Y hδ (hδmax.trans (min_le_right _ _)) hA
  have hbottom' : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnmax (by norm_num))
      (by positivity)) hbottom
  exact cells_of_iteration_parameters hp hA hnmax hbottom' hinit hret

end WangZahlLot.Obl.wz_regular_transverse_affine_cells

theorem WangZahlLot.wz_regular_transverse_affine_cells : (fun (E:Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasureTheory.MeasureSpace E] => (fun (B:Set E) => (fun (T:ℝ → E → E → Set E) => (fun (A:ℝ → ℝ → (n:ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop) => (fun (P:ℝ → ℝ → E → (Fin 3 → E) → Set E) => (fun (C:ℝ → ℝ → (n:ℕ) → (Fin n → E) → (Fin n → E) → (Fin n → Set E) → Prop) => ∀ s:ℝ,0 < s → ∃ η:ℝ,0 < η ∧ ∃ δ₀:ℝ,0 < δ₀ ∧ δ₀ ≤ (1/100:ℝ) ∧ ∀ δ:ℝ,0 < δ → δ ≤ δ₀ → ∀ (n:ℕ) (x v:Fin n → E) (Y:Fin n → Set E),A (δ ^ η) δ n x v Y → C δ (δ ^ s) n x v Y) (fun δ h n x v Y => 0 < n ∧ (n:ℝ) ≤ δ ^ (-100:ℝ) ∧ ∃ m:ℕ,0 < m ∧ ∃ (I:Fin m → Finset (Fin n)) (f:Fin m → AffineEquiv ℝ E E) (D:Fin m → ℝ) (a b:ℝ) (c:Fin m → Fin n → E) (u:Fin m → Fin n → Fin 3 → E) (H:Fin m → Fin n → Set E),δ ^ (100:ℕ) ≤ a ∧ a ≤ b ∧ b ≤ (1/1000000:ℝ) ∧ δ * h ≤ b ∧ (∀ j,(I j).Nonempty) ∧ h * (n:ℝ) ≤ Finset.sum Finset.univ (fun j => ((I j).card:ℝ)) ∧ (∀ j,δ ^ (100:ℕ) ≤ D j ∧ D j ≤ δ ^ (-100:ℝ)) ∧ (∀ j (Q:Set E),MeasureTheory.volume (f j '' Q) = ENNReal.ofReal (D j) * MeasureTheory.volume Q) ∧ (∀ j i,i ∈ I j → Orthonormal ℝ (u j i)) ∧ (∀ j i,i ∈ I j → P a b (c j i) (u j i) ⊆ Metric.ball (0:E) (1/100)) ∧ (∀ j i,i ∈ I j → T δ (x i) (v i) ⊆ f j '' P a b (c j i) (u j i)) ∧ (∀ j i,i ∈ I j → MeasurableSet (H j i)) ∧ (∀ j i,i ∈ I j → H j i ⊆ P a b (c j i) (u j i) ∩ f j ⁻¹' (Y i)) ∧ (∀ j i,i ∈ I j → ENNReal.ofReal h * MeasureTheory.volume (P a b (c j i) (u j i)) ≤ MeasureTheory.volume (H j i)) ∧ (∀ j i,i ∈ I j → ∀ p:E,p ∈ H j i → ∀ r:ℝ,a ≤ r → r ≤ 1 → ENNReal.ofReal h * MeasureTheory.volume (P a b (c j i) (u j i) ∩ Metric.ball p r) ≤ MeasureTheory.volume (H j i ∩ Metric.ball p r)) ∧ (∀ j (p:E),(∃ i:Fin n,i ∈ I j ∧ p ∈ H j i) → ∃ i i':Fin n,i ∈ I j ∧ i' ∈ I j ∧ p ∈ H j i ∧ p ∈ H j i' ∧ h ≤ a / b + min ‖u j i 0 - u j i' 0‖ ‖u j i 0 + u j i' 0‖) ∧ (∀ j (ν:E) (s r:ℝ),‖ν‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i:Fin n | i ∈ I j ∧ P a b (c j i) (u j i) ⊆ (B ∩ {p | |inner ℝ ν p - s| ≤ r})}:ℝ) ≤ ENNReal.ofReal (h⁻¹ * ((I j).card:ℝ)) * MeasureTheory.volume (B ∩ {p | |inner ℝ ν p - s| ≤ r})) ∧ (∀ j j',j ≠ j' → Disjoint (f j '' (⋃ i ∈ I j,H j i)) (f j' '' (⋃ i ∈ I j',H j' i))))) (fun a b c u => {p | |inner ℝ (u 0) (p - c)| ≤ a ∧ |inner ℝ (u 1) (p - c)| ≤ b ∧ |inner ℝ (u 2) (p - c)| ≤ (1/1000:ℝ)})) (fun d δ n x v Y => 0 < n ∧ (∀ i,‖v i‖ = 1) ∧ (∀ i,T δ (x i) (v i) ⊆ B) ∧ (∀ i j,i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2:ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i,MeasurableSet (Y i)) ∧ (∀ i,Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (d * (n:ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i)))) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) (Metric.ball (0:E) 1)) LeanEval.Analysis.WangZahlKakeya.Space :=
  WangZahlLot.Obl.wz_regular_transverse_affine_cells.regular_transverse_affine_cells
