-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_direction_density_transfer.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_direction_density_transfer

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- A separated family in two balls of radius `100000 δ` has bounded cardinality. -/
theorem two_ball_count {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {v : Fin n → Space}
    (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖)
    (F : Finset (Fin n)) (c d : Space)
    (hF : ∀ i ∈ F, dist (v i) c ≤ 100000 * δ ∨ dist (v i) d ≤ 100000 * δ) :
    (F.card : ℝ) ≤ 16 * (100001 : ℝ) ^ 3 := by
  classical
  have hd : (F : Set (Fin n)).PairwiseDisjoint (fun i => ball (v i) (δ / 2)) := by
    intro i _ j _ hij
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    linarith [hsep i j hij]
  have hs : (⋃ i ∈ F, ball (v i) (δ / 2)) ⊆
      ball c (100001 * δ) ∪ ball d (100001 * δ) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    rw [mem_ball] at hpi
    rcases hF i hi with hc | hd
    · exact Or.inl ((dist_triangle p (v i) c).trans_lt (by linarith))
    · exact Or.inr ((dist_triangle p (v i) d).trans_lt (by linarith))
  have hm : volume (⋃ i ∈ F, ball (v i) (δ / 2)) ≤
      volume (ball c (100001 * δ)) + volume (ball d (100001 * δ)) :=
    (measure_mono hs).trans (measure_union_le _ _)
  rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hm
  simp only [EuclideanSpace.volume_ball_fin_three] at hm
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)] at hm
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hm
  simp only [Finset.sum_const, nsmul_eq_mul] at hm
  have hm' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
  have hp : 0 < δ ^ 3 * (Real.pi * 4 / 3) := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  nlinarith only [hm']

/-- A maximal set of widely separated unoriented directions covers every direction. -/
theorem maximal_direction_family {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (v : Fin n → Space) :
    ∃ F : Finset (Fin n),
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
        100000 * δ ≤ ‖v i - v j‖ ∧ 100000 * δ ≤ ‖v i + v j‖) ∧
      ∀ j : Fin n, ∃ i ∈ F, ‖v j - v i‖ < 100000 * δ ∨ ‖v j + v i‖ < 100000 * δ := by
  classical
  let P : Finset (Fin n) → Prop := fun F =>
    ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 100000 * δ ≤ ‖v i - v j‖ ∧ 100000 * δ ≤ ‖v i + v j‖
  let S : Finset (Finset (Fin n)) := Finset.univ.powerset.filter P
  have hS : S.Nonempty := ⟨∅, by simp [S, P]⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image S Finset.card hS
  have hFP : P F := (Finset.mem_filter.mp hF).2
  refine ⟨F, hFP, fun j => ?_⟩
  by_contra hno
  have hj : j ∉ F := by
    intro hj
    apply hno
    refine ⟨j, hj, Or.inl ?_⟩
    simp only [sub_self, norm_zero]
    positivity
  have hsep : ∀ i ∈ F, 100000 * δ ≤ ‖v j - v i‖ ∧ 100000 * δ ≤ ‖v j + v i‖ := by
    intro i hi
    constructor
    · by_contra h
      exact hno ⟨i, hi, Or.inl (lt_of_not_ge h)⟩
    · by_contra h
      exact hno ⟨i, hi, Or.inr (lt_of_not_ge h)⟩
  have hins : P (insert j F) := by
    intro a hain b hbin hab
    rcases Finset.mem_insert.mp hain with haj | haF
    · subst a
      rcases Finset.mem_insert.mp hbin with hbj | hbF
      · exact (hab hbj.symm).elim
      · exact hsep b hbF
    · rcases Finset.mem_insert.mp hbin with hbj | hbF
      · subst b
        simpa [norm_sub_rev, add_comm] using hsep a haF
      · exact hFP a haF b hbF hab
  have hc := hmax (insert j F) (by simp only [S, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]; exact hins)
  rw [Finset.card_insert_of_notMem hj] at hc
  omega

/-- The geometric extraction used in the density transfer. -/
theorem extraction : Extraction := by
  classical
  refine ⟨16 * (100001 : ℝ) ^ 3, by norm_num, ?_⟩
  intro δ hδ _ n x v hn hv hsep _
  obtain ⟨F, hFsep, hcover⟩ := maximal_direction_family hδ v
  let N : Fin n → Finset (Fin n) := fun i => Finset.univ.filter
    (fun j => ‖v j - v i‖ < 100000 * δ ∨ ‖v j + v i‖ < 100000 * δ)
  have hN : ∀ i, ((N i).card : ℝ) ≤ 16 * (100001 : ℝ) ^ 3 := by
    intro i
    apply two_ball_count hδ (fun a b hab => (hsep a b hab).1) (N i) (v i) (-v i)
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simpa only [dist_eq_norm, sub_neg_eq_add] using h.imp le_of_lt le_of_lt
  have hcov : Finset.univ ⊆ F.biUnion N := by
    intro j _
    obtain ⟨i, hi, hji⟩ := hcover j
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji⟩⟩
  have hcard : (n : ℝ) ≤ (16 * (100001 : ℝ) ^ 3) * (F.card : ℝ) := by
    have hnat : n ≤ ∑ i ∈ F, (N i).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    calc
      (n : ℝ) ≤ ∑ i ∈ F, ((N i).card : ℝ) := by exact_mod_cast hnat
      _ ≤ ∑ _i ∈ F, 16 * (100001 : ℝ) ^ 3 := Finset.sum_le_sum (fun i _ => hN i)
      _ = _ := by simp [mul_comm]
  have hFne : F.Nonempty := by
    obtain ⟨i, hi, _⟩ := hcover ⟨0, hn⟩
    exact ⟨i, hi⟩
  let e : Fin (Fintype.card F) → Fin n := fun i => ((Fintype.equivFin F).symm i).val
  have he : Function.Injective e := by
    intro i j hij
    exact (Fintype.equivFin F).symm.injective (Subtype.ext hij)
  refine ⟨Fintype.card F, e, ?_, he, ?_, ?_⟩
  · simpa using Finset.card_pos.mpr hFne
  · simpa using hcard
  · intro i j hij
    have h := hFsep (e i) ((Fintype.equivFin F).symm i).property
      (e j) ((Fintype.equivFin F).symm j).property (he.ne hij)
    exact intersection_le_half hδ (hv (e i)) (hv (e j)) h.1 h.2

end WangZahlLot.Obl.wz_direction_density_transfer
