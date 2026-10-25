-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BalancedAssignments.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.SlabComposition

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open Set

lemma fiber_card_sum {n N : ℕ} (f : Fin n → Fin N) :
    ∑ k, Set.ncard {i | f i = k} = n := by
  simpa using count_fibers f (fun _ => True)

lemma balanced_assignment_bounds {n N : ℕ} (f : Fin n → Fin N) {D : ℝ}
    (h : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'})
    (k : Fin N) :
    (N : ℝ) * Set.ncard {i | f i = k} ≤ D * n ∧
      (n : ℝ) ≤ D * N * Set.ncard {i | f i = k} := by
  have hsum : ∑ k, (Set.ncard {i | f i = k} : ℝ) = n := by
    exact_mod_cast fiber_card_sum f
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun k' _ => h k k')
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, hsum] using hh
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun k' _ => h k' k)
    rw [hsum] at hh
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_left_comm (N : ℝ) D, mul_assoc] using hh

lemma balanced_assignment_surjective {n N : ℕ} (hn : 0 < n) (f : Fin n → Fin N) {D : ℝ}
    (h : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'}) :
    Function.Surjective f := by
  intro k
  have hc : 0 < Set.ncard {i | f i = k} := by
    by_contra hz
    have he : Set.ncard {i | f i = k} = 0 := Nat.eq_zero_of_not_pos hz
    have hh := (balanced_assignment_bounds f h k).2
    rw [he] at hh
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    norm_num at hh
    linarith
  exact (Set.ncard_pos (Set.toFinite _)).mp hc

lemma composition_fiber_sum {n N L : ℕ} (f : Fin n → Fin N) (g : Fin N → Fin L)
    (j : Fin L) :
    ∑ k, (if g k = j then Set.ncard {i | f i = k} else 0) =
      Set.ncard {i | g (f i) = j} := by
  classical
  have hh := count_fibers f (fun i => g (f i) = j)
  rw [← hh]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : g k = j
  · rw [if_pos hk]
    congr 1
    ext i
    exact ⟨fun hi => ⟨hi, by rw [hi]; exact hk⟩, fun hi => hi.1⟩
  · rw [if_neg hk]
    have he : {i | f i = k ∧ g (f i) = j} = ∅ := by
      ext i
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hi hgi
      exact hk (hi ▸ hgi)
    rw [he, ncard_empty]

lemma composition_fiber_bounds {n N L : ℕ} (f : Fin n → Fin N) (g : Fin N → Fin L)
    {D : ℝ}
    (h : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'})
    (j : Fin L) :
    (N : ℝ) * Set.ncard {i | g (f i) = j} ≤
        D * n * Set.ncard {k | g k = j} ∧
      (n : ℝ) * Set.ncard {k | g k = j} ≤
        D * N * Set.ncard {i | g (f i) = j} := by
  classical
  have hsum : ∑ k, (if g k = j then (Set.ncard {i | f i = k} : ℝ) else 0) =
      Set.ncard {i | g (f i) = j} := by exact_mod_cast composition_fiber_sum f g j
  have hconst (a : ℝ) : (∑ k : Fin N, if g k = j then a else 0) =
      a * Set.ncard {k | g k = j} := by
    simp [← Finset.sum_filter, Set.ncard_eq_toFinset_card', mul_comm]
  constructor
  · have hh : (∑ k, if g k = j then (N : ℝ) * Set.ncard {i | f i = k} else 0) ≤
        ∑ k : Fin N, if g k = j then D * n else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : g k = j
      · simp only [if_pos hk]
        exact (balanced_assignment_bounds f h k).1
      · simp only [if_neg hk, le_refl]
    have he : (∑ k, if g k = j then (N : ℝ) * Set.ncard {i | f i = k} else 0) =
        N * Set.ncard {i | g (f i) = j} := by
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    simpa only [he, hconst] using hh
  · have hh : (∑ k : Fin N, if g k = j then (n : ℝ) else 0) ≤
        ∑ k, if g k = j then D * N * Set.ncard {i | f i = k} else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : g k = j
      · simp only [if_pos hk]
        exact (balanced_assignment_bounds f h k).2
      · simp only [if_neg hk, le_refl]
    have he : (∑ k, if g k = j then D * N * Set.ncard {i | f i = k} else 0) =
        D * N * Set.ncard {i | g (f i) = j} := by
      rw [← hsum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    simpa only [he, hconst] using hh

lemma balanced_composed_assignments {n N L : ℕ} (hN : 0 < N)
    (f : Fin n → Fin N) (g : Fin N → Fin L) {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ D * Set.ncard {i | f i = k'})
    (hg : ∀ j j', (Set.ncard {k | g k = j} : ℝ) ≤ D * Set.ncard {k | g k = j'}) :
    ∀ j j', (Set.ncard {i | g (f i) = j} : ℝ) ≤ D ^ 3 * Set.ncard {i | g (f i) = j'} := by
  intro j j'
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (mul_le_mul_iff_right₀ hN').mp
  have h₁ := (composition_fiber_bounds f g hf j).1
  have h₂ := (composition_fiber_bounds f g hf j').2
  have h₃ := hg j j'
  calc
    _ ≤ D * n * Set.ncard {k | g k = j} := h₁
    _ ≤ D * n * (D * Set.ncard {k | g k = j'}) :=
      mul_le_mul_of_nonneg_left h₃ (by positivity)
    _ = D ^ 2 * ((n : ℝ) * Set.ncard {k | g k = j'}) := by ring
    _ ≤ D ^ 2 * (D * N * Set.ncard {i | g (f i) = j'}) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg D)
    _ = _ := by ring

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
