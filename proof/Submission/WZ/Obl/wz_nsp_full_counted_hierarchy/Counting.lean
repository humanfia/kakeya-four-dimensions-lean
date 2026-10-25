-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Tower

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Partition a fiber of a composite assignment by its intermediate parents. -/
theorem ncard_fiber_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : β → γ) (k : γ) :
    Set.ncard {x | g (f x) = k} =
      ∑ y ∈ Finset.univ.filter (fun y => g y = k), Set.ncard {x | f x = y} := by
  classical
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.mem_univ,
    Finset.mem_filter, true_and] using
    (Finset.sum_card_fiberwise_eq_card_filter Finset.univ
      (Finset.univ.filter fun y => g y = k) f).symm

/-- Lower fullness multiplies under composition of finite assignments. -/
theorem fullness_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : β → γ) {d r s a b : ℝ}
    (ha : 0 ≤ a)
    (hf : ∀ y, a * r ^ 2 ≤ (Set.ncard {x | f x = y} : ℝ) * d ^ 2)
    (hg : ∀ z, b * s ^ 2 ≤ (Set.ncard {y | g y = z} : ℝ) * r ^ 2) :
    ∀ z, (a * b) * s ^ 2 ≤ (Set.ncard {x | g (f x) = z} : ℝ) * d ^ 2 := by
  classical
  intro z
  have hsum := Finset.sum_le_sum (s := Finset.univ.filter fun y => g y = z)
    (fun y _ => hf y)
  have hsum' : (Set.ncard {y | g y = z} : ℝ) * (a * r ^ 2) ≤
      (Set.ncard {x | g (f x) = z} : ℝ) * d ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul,
      ← Nat.cast_sum] at hsum
    rw [← ncard_fiber_comp f g z] at hsum
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using hsum
  have hmul := mul_le_mul_of_nonneg_left (hg z) ha
  nlinarith

/-- A nonzero lower fullness bound ensures that no parent is unused. -/
theorem surjective_of_fullness {α β : Type*} [Finite α]
    (f : α → β) {d r a : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hf : ∀ y, a * r ^ 2 ≤ (Set.ncard {x | f x = y} : ℝ) * d ^ 2) :
    Function.Surjective f := by
  intro y
  have hpos : 0 < (Set.ncard {x | f x = y} : ℝ) := by
    by_contra h
    have he : (Set.ncard {x | f x = y} : ℝ) = 0 :=
      le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    have hh := hf y
    rw [he, zero_mul] at hh
    have : 0 < a * r ^ 2 := by positivity
    linarith
  have hn : 0 < Set.ncard {x | f x = y} := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp hn
  exact ⟨x, hx⟩

/-- The lower ceiling estimate from one copy step gives fullness in every
balanced nonempty parent fiber. -/
theorem copied_fiber_fullness {ρ r M L c : ℝ} {N : ℕ}
    (hL : 0 < L) (hc : M ≤ L * c)
    (hlower : ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2) :
    L⁻¹ * ρ ^ 2 ≤ (N : ℝ) * c * r ^ 2 := by
  have hmul : (N : ℝ) * M * r ^ 2 ≤ L * ((N : ℝ) * c * r ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hc
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg r))]
  exact (inv_mul_le_iff₀ hL).mpr (hlower.trans hmul)

open WangZahlLot.Obl.wz_tower_balanced_refinement in
/-- Iterating the lower bound on immediate children controls all descendants. -/
theorem descendant_fullness (N : ℕ → ℕ)
    (f : ∀ j, Fin (N (j + 1)) → Fin (N j)) (r : ℕ → ℝ)
    (a : ℝ) (ha : 0 ≤ a) (J : ℕ)
    (hstep : ∀ j, j < J → ∀ i : Fin (N j),
      a * (r j) ^ 2 ≤ (Set.ncard {s | f j s = i} : ℝ) * (r (j + 1)) ^ 2)
    {j l : ℕ} (hjl : j ≤ l) (hlJ : l ≤ J) :
    ∀ i : Fin (N j), a ^ (l - j) * (r j) ^ 2 ≤
      (Set.ncard {s | ancestor f hjl s = i} : ℝ) * (r l) ^ 2 := by
  induction l, hjl using Nat.le_induction with
  | base =>
      intro i
      simp [ancestor_self]
  | succ l hjl ih =>
      have hl : l < J := by omega
      have hi := ih (Nat.le_of_lt hl)
      have hc := fullness_comp (f l) (ancestor f hjl)
        ha (hstep l hl) hi
      intro i
      have he : l + 1 - j = (l - j) + 1 := by omega
      have hs : {s | ancestor f (Nat.le_succ_of_le hjl) s = i} =
          {s | ancestor f hjl (f l s) = i} := by
        ext s
        simp only [Set.mem_ofPred_eq]
        rw [ancestor_succ f hjl s]
      rw [hs, he, pow_succ]
      convert hc i using 1
      ring

/-- Sum all finite fibers of an assignment. -/
theorem sum_ncard_fibers {n k : ℕ} (f : Fin n → Fin k) :
    ∑ i : Fin k, Set.ncard {s | f s = i} = n := by
  classical
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin] using
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ f

/-- A common upper fiber count bounds the ratio of consecutive layer sizes. -/
theorem card_le_mul_of_fibers {n k : ℕ} (f : Fin n → Fin k) {M : ℝ}
    (h : ∀ i, (Set.ncard {s | f s = i} : ℝ) ≤ M) : (n : ℝ) ≤ (k : ℝ) * M := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simpa only [← Nat.cast_sum, sum_ncard_fibers, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

/-- A positive numerical lower bound excludes unused parent vertices. -/
theorem surjective_of_fiber_lower {n k : ℕ} (f : Fin n → Fin k) {M : ℝ}
    (hM : 0 < M) (h : ∀ i, M ≤ (Set.ncard {s | f s = i} : ℝ)) :
    Function.Surjective f := by
  intro i
  have hi : 0 < Set.ncard {s | f s = i} := by
    exact_mod_cast hM.trans_le (h i)
  exact (Set.ncard_pos (Set.toFinite _)).mp hi

/-- Surjective parent maps ensure that every intermediate layer has no more
vertices than the fine layer. -/
theorem layer_card_le (n : ℕ → ℕ) (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (J : ℕ) (hsurj : ∀ j, j < J → Function.Surjective (f j))
    {j l : ℕ} (hjl : j ≤ l) (hlJ : l ≤ J) : n j ≤ n l := by
  induction l, hjl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hjl ih =>
      have hstep : n l ≤ n (l + 1) := by
        simpa only [Fintype.card_fin] using
          Fintype.card_le_of_surjective (f l) (hsurj l (by omega))
      exact (ih (by omega)).trans hstep

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
