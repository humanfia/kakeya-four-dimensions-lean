import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellSystem
import Submission.Obl.k4_scalar_initial_true_horizon.InitialGroup
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Count initial cells by their original true mass floors. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Time endpoints carry no mass under an original incidence law. -/
theorem Exact.mu_Icc_eq_Ico {p : Data} (hp : Exact p) (k : ℕ)
    (a : Fin (worlds p k)) (A : Set Trajectory) (s e : ℝ) :
    mu p k a (A ×ˢ Icc s e) = mu p k a (A ×ˢ Ico s e) := by
  apply le_antisymm
  · calc
      _ ≤ mu p k a ((A ×ˢ Ico s e) ∪ (univ ×ˢ {e})) := by
        apply measure_mono
        rintro ⟨l, t⟩ ⟨hl, ht⟩
        by_cases hte : t < e
        · exact Or.inl ⟨hl, ht.1, hte⟩
        · exact Or.inr ⟨mem_univ _, by simpa using le_antisymm ht.2 (le_of_not_gt hte)⟩
      _ ≤ mu p k a (A ×ˢ Ico s e) + mu p k a (univ ×ˢ {e}) := measure_union_le _ _
      _ = _ := by rw [hp.mu_time_null k a e, add_zero]
  · exact measure_mono (prod_mono subset_rfl Ico_subset_Icc_self)

/-- A finite family with original mass floor `eta` has at most `W/eta`
entries, summed over every dyadic block and every original world. -/
theorem initial_cell_count_le {p : Data} (hp : Exact p) {k T n : ℕ}
    (γ : Fin n → Fin (worlds p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Trajectory) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    {η : ℝ} (hη : 0 < η)
    (hfloor : ∀ i, ENNReal.ofReal η ≤ mu p k (γ i) (A i ×ˢ I T (j i))) :
    (n : ℝ) ≤ (worlds p k : ℝ) / η := by
  classical
  let q := 1 / (2 : ℝ) ^ T
  have hq : 0 < q := by dsimp [q]; positivity
  let C : Fin n → Set Incidence := fun i => A i ×ˢ
    Ico (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)
  let F := fun a : Fin (worlds p k) => Finset.univ.filter (fun i => γ i = a)
  have hC : ∀ i, MeasurableSet (C i) := fun i => (hA i).prod measurableSet_Ico
  have hreal (i : Fin n) : η ≤ (mu p k (γ i)).real (C i) := by
    letI := hp.mu_finite k (γ i)
    have hr := ENNReal.toReal_mono (measure_ne_top (mu p k (γ i)) _) (hfloor i)
    rw [ENNReal.toReal_ofReal hη.le] at hr
    have heq : (mu p k (γ i)).real (C i) = (mu p k (γ i)).real (A i ×ˢ I T (j i)) :=
      congrArg ENNReal.toReal (hp.mu_Icc_eq_Ico k (γ i) (A i) _ _).symm
    rw [heq]
    exact hr
  have hbound (a : Fin (worlds p k)) : ((F a).card : ℝ) ≤ 1 / η := by
    letI := hp.mu_finite k a
    have hd : (↑(F a) : Set (Fin n)).PairwiseDisjoint C := by
      intro i hi i' hi' hne
      have hia : γ i = a := (Finset.mem_filter.mp hi).2
      have hi'a : γ i' = a := (Finset.mem_filter.mp hi').2
      apply Set.disjoint_left.mpr
      rintro ⟨l, t⟩ ⟨hli, hti⟩ ⟨hli', hti'⟩
      by_cases hj : j i = j i'
      · exact Set.disjoint_left.mp (hdisj i i' hne (hia.trans hi'a.symm) hj) hli hli'
      · have hjn : (j i : ℕ) ≠ (j i' : ℕ) := fun h => hj (Fin.ext h)
        have ht0 : t ∈ tCell 0 q (j i : ℕ) := by
          simpa only [tCell, q, zero_add, div_eq_mul_inv, one_mul] using hti
        have ht0' : t ∈ tCell 0 q (j i' : ℕ) := by
          simpa only [tCell, q, zero_add, div_eq_mul_inv, one_mul] using hti'
        exact Set.disjoint_left.mp (tCell_disjoint (t₀ := 0) hq hjn) ht0 ht0'
    have hc := Submission.Lib.K4FinitePlankAtlases.old_cell_count (mu p k a) (F a) C hd
      (fun i _ => hC i) hη (by
        intro i hi
        have hia : γ i = a := (Finset.mem_filter.mp hi).2
        simpa only [hia] using hreal i)
    have hm : (mu p k a).real univ ≤ 1 := by
      have hm := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hp.mu_univ_le k a)
      simpa only [measureReal_def, ENNReal.toReal_one] using hm
    exact hc.trans (div_le_div_of_nonneg_right hm hη.le)
  have hcard : (n : ℝ) = ∑ a, ((F a).card : ℝ) := by
    simpa only [F, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using
      (Finset.sum_fiberwise Finset.univ γ (fun _ => (1 : ℝ))).symm
  rw [hcard]
  calc
    _ ≤ ∑ _a : Fin (worlds p k), 1 / η := Finset.sum_le_sum (fun a _ => hbound a)
    _ = _ := by simp [div_eq_mul_inv]

end Submission.Obl.k4_scalar_initial_true_horizon
