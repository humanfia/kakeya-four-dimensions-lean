/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarScalePackets.lean -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

/-! Finite scalar packet data and the measurable low-gradient core at one thickness. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical

def scalarPacketBlock (q : ℕ) (j : Fin q) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / q) ((((j : ℕ) : ℝ) / q) + (q : ℝ)⁻¹)

theorem scalarPacketBlock_start_unit {q : ℕ} (hq : 0 < q) (j : Fin q) :
    (((j : ℕ) : ℝ) / q) ∈ Set.Icc (0 : ℝ) 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨div_nonneg (Nat.cast_nonneg _) hqR.le, (div_le_one hqR).mpr ?_⟩
  exact_mod_cast Nat.le_of_lt j.isLt

theorem scalarPacketBlock_end_le_one {q : ℕ} (hq : 0 < q) (j : Fin q) :
    (((j : ℕ) : ℝ) / q) + (q : ℝ)⁻¹ ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← one_div, ← add_div]
  apply (div_le_one hqR).mpr
  exact_mod_cast Nat.succ_le_of_lt j.isLt

theorem scalarPacketBlock_subset_unit {q : ℕ} (hq : 0 < q) (j : Fin q) :
    scalarPacketBlock q j ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  exact ⟨(scalarPacketBlock_start_unit hq j).1.trans ht.1,
    ht.2.trans (scalarPacketBlock_end_le_one hq j)⟩

structure ScalarScalePackets (X G : Type*) [MeasurableSpace X]
    (a : X → Fin 5 → ℝ) (K ξ : ℝ) (n q : ℕ) where
  world : Fin n → G
  block : Fin n → Fin q
  labels : Fin n → Set X
  centerY : Fin n → ℝ
  centerV : Fin n → ℝ
  predictor : Fin n → MvPolynomial (Fin 2) ℝ
  labels_measurable : ∀ i, MeasurableSet (labels i)
  labels_disjoint : ∀ i i', i ≠ i' → world i = world i' → block i = block i' →
    Disjoint (labels i) (labels i')
  center_bound : ∀ i, |centerY i| + |centerV i| ≤ K
  predictor_degree : ∀ i, (predictor i).totalDegree ≤ 2
  predictor_norm : ∀ i, ∀ t ∈ scalarPacketBlock q (block i), ∀ w ∈ Set.Icc (-1 : ℝ) 1,
    |eval ![t,centerY i + t * centerV i + (q : ℝ)⁻¹ * w] (predictor i)| ≤ K
  trajectory_fit : ∀ i, ∀ l ∈ labels i, ∀ t ∈ scalarPacketBlock q (block i),
    |scalarY (a l) t - centerY i - t * centerV i| ≤ K * (q : ℝ)⁻¹ ∧
    |scalarX (a l) t - eval ![t,scalarY (a l) t] (predictor i)| ≤ K * ξ

def scalarPacketPosition {X : Type*} (a : X → Fin 5 → ℝ) (p : X × ℝ) : Fin 3 → ℝ :=
  ![p.2,scalarY (a p.1) p.2,scalarX (a p.1) p.2]

theorem measurable_scalarPacketPosition {X : Type*} [MeasurableSpace X]
    {a : X → Fin 5 → ℝ} (ha : Measurable a) : Measurable (scalarPacketPosition a) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp [scalarPacketPosition, scalarY, scalarX] <;> fun_prop

def scalarScaleCovered {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    {a : X → Fin 5 → ℝ} {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) (g : G) : Set (X × ℝ) :=
  ⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), D.labels i ×ˢ scalarPacketBlock q (D.block i)

def scalarScaleBad {X G : Type*} [MeasurableSpace X]
    {a : X → Fin 5 → ℝ} {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) (E : Set (X × ℝ)) (M : ℝ) (i : Fin n) : Set (X × ℝ) :=
  {p | p ∈ E ∧ p.1 ∈ D.labels i ∧ p.2 ∈ scalarPacketBlock q (D.block i) ∧
    M ≤ |eval ![p.2,scalarY (a p.1) p.2] (pderiv 1 (D.predictor i))|}

def scalarScaleCore {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    {a : X → Fin 5 → ℝ} {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) (E : Set (X × ℝ)) (M : ℝ) (g : G) : Set (X × ℝ) :=
  (E ∩ scalarScaleCovered D g) \
    ⋃ i ∈ (Finset.univ.filter fun i => D.world i = g), scalarScaleBad D E M i

theorem measurableSet_scalarScaleCovered {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    {a : X → Fin 5 → ℝ} {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) (g : G) : MeasurableSet (scalarScaleCovered D g) := by
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    (D.labels_measurable i).prod measurableSet_Icc

theorem measurableSet_scalarScaleBad {X G : Type*} [MeasurableSpace X]
    {a : X → Fin 5 → ℝ} (ha : Measurable a) {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) {E : Set (X × ℝ)} (hE : MeasurableSet E)
    (M : ℝ) (i : Fin n) : MeasurableSet (scalarScaleBad D E M i) := by
  have hbase : Measurable (fun p : X × ℝ => (![p.2,scalarY (a p.1) p.2] : Fin 2 → ℝ)) := by
    apply Measurable.of_eval
    intro e
    fin_cases e <;> dsimp [scalarY] <;> fun_prop
  have hg := ((MvPolynomial.continuous_eval (pderiv 1 (D.predictor i))).measurable.comp hbase).abs
  exact hE.inter (((D.labels_measurable i).preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter (measurableSet_le measurable_const hg)))

theorem measurableSet_scalarScaleCore {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    {a : X → Fin 5 → ℝ} (ha : Measurable a) {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) {E : Set (X × ℝ)} (hE : MeasurableSet E)
    (M : ℝ) (g : G) : MeasurableSet (scalarScaleCore D E M g) := by
  apply (hE.inter (measurableSet_scalarScaleCovered D g)).diff
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    measurableSet_scalarScaleBad ha D hE M i

theorem scalarScaleCore_subset {X G : Type*} [MeasurableSpace X] [DecidableEq G]
    {a : X → Fin 5 → ℝ} {K ξ : ℝ} {n q : ℕ}
    (D : ScalarScalePackets X G a K ξ n q) (E : Set (X × ℝ)) (M : ℝ) (g : G) :
    scalarScaleCore D E M g ⊆ E := fun _ hp => hp.1.1

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
