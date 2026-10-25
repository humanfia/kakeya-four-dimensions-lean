import Submission.Obl.k4_matching_trimmed_grid.Coarse
import Submission.Obl.k4_matching_trimmed_grid.Gaps

noncomputable section

namespace Submission.Obl.k4_matching_trimmed_grid

open Set
open scoped BigOperators

lemma reference_indices (S : Finset ℕ) (m : ℕ → ℕ) :
    ∃ z : ℕ → ℕ, ∀ k ∈ S, z (m k) ∈ S ∧ m (z (m k)) = m k ∧ z (m k) ≤ k := by
  classical
  let T := fun j => S.filter (fun k => m k = j)
  let z := fun j => if h : (T j).Nonempty then (T j).min' h else 0
  refine ⟨z, ?_⟩
  intro k hk
  have hkT : k ∈ T (m k) := by simp [T, hk]
  have hn : (T (m k)).Nonempty := ⟨k, hkT⟩
  have he : z (m k) = (T (m k)).min' hn := by simp [z, hn]
  rw [he]
  have hmem := Finset.min'_mem (T (m k)) hn
  exact ⟨(Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2,
    Finset.min'_le _ _ hkT⟩

def fineBlock (t C s : ℕ) : Finset ℕ :=
  (Finset.range (t - C)).image (fun v => s * t + v)

def fineCells (S : Finset ℕ) (t C : ℕ) : Finset ℕ := S.biUnion (fineBlock t C)

lemma fineBlock_div {t C s k : ℕ} (_ht : 1 ≤ t) (hk : k ∈ fineBlock t C s) : k / t = s := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
  have hv' := Finset.mem_range.mp hv
  apply Nat.div_eq_of_lt_le (by omega)
  simp only [Nat.add_mul, Nat.one_mul]
  omega

lemma fineBlock_disjoint {t C : ℕ} (ht : 1 ≤ t) {s r : ℕ} (hsr : s ≠ r) :
    Disjoint (fineBlock t C s) (fineBlock t C r) := by
  apply Finset.disjoint_left.mpr
  intro k hks hkr
  exact hsr ((fineBlock_div ht hks).symm.trans (fineBlock_div ht hkr))

lemma fineCells_subset {S : Finset ℕ} {n t C : ℕ} (hS : S ⊆ Finset.range n) (_ht : 1 ≤ t) :
    fineCells S t C ⊆ Finset.range (n * t) := by
  intro k hk
  obtain ⟨s, hs, hks⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hks
  have hs' := Finset.mem_range.mp (hS hs)
  have hv' := Finset.mem_range.mp hv
  apply Finset.mem_range.mpr
  have hsn : s + 1 ≤ n := by omega
  have hmul := Nat.mul_le_mul_right t hsn
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  omega

lemma fineBlock_end {t C s k : ℕ} (hCt : C ≤ t) (hk : k ∈ fineBlock t C s) :
    k + C ≤ (s + 1) * t := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hk
  have hv' := Finset.mem_range.mp hv
  simp only [Nat.add_mul, Nat.one_mul]
  omega

lemma sum_fineCells (S : Finset ℕ) (m : ℕ → ℕ) (n t C : ℕ) (ht : 1 ≤ t) :
    (∑ k ∈ fineCells S t C, (1 + 1 / (m (k / t) : ℝ)) / ((n * t : ℕ) : ℝ)) =
      ∑ s ∈ S, ((t - C : ℕ) : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ) := by
  classical
  rw [fineCells, Finset.sum_biUnion (fun _ _ _ _ hsr => fineBlock_disjoint ht hsr)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [fineBlock, Finset.sum_image (by intro v _ w _ he; exact Nat.add_left_cancel he)]
  have he : ∀ v ∈ Finset.range (t - C), (s * t + v) / t = s := by
    intro v hv
    exact fineBlock_div ht (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  calc
    _ = ∑ _v ∈ Finset.range (t - C), (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [he v hv]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

lemma refinement_coverage {S : Finset ℕ} {m : ℕ → ℕ} {n t C : ℕ}
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hCt : C ≤ t) (hS : S ⊆ Finset.range n)
    (hm : ∀ s ∈ S, 1 ≤ m s) :
    (∑ s ∈ S, (1 + 1 / (m s : ℝ)) / n) - 2 * (C : ℝ) / t ≤
      ∑ k ∈ fineCells S t C, (1 + 1 / (m (k / t) : ℝ)) / ((n * t : ℕ) : ℝ) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  rw [sum_fineCells S m n t C ht]
  have hcost : ∀ s ∈ S,
      (1 + 1 / (m s : ℝ)) / n -
        ((t - C : ℕ) : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ) ≤
        2 * (C : ℝ) / ((n * t : ℕ) : ℝ) := by
    intro s hs
    have hmr : (1 : ℝ) ≤ m s := by exact_mod_cast hm s hs
    have hmp : (0 : ℝ) < m s := by linarith
    have hw : 1 + 1 / (m s : ℝ) ≤ 2 := by
      have : 1 / (m s : ℝ) ≤ 1 := (div_le_iff₀ hmp).2 (by linarith)
      linarith
    have he : (1 + 1 / (m s : ℝ)) / n -
        ((t - C : ℕ) : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ) =
        (C : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ) := by
      simp only [Nat.cast_sub hCt, Nat.cast_mul]
      field_simp [hn0, ht0]
      ring
    rw [he]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (n * t))
    nlinarith [mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg C)]
  have hcostSum :
      (∑ s ∈ S, (1 + 1 / (m s : ℝ)) / n) -
        (∑ s ∈ S, ((t - C : ℕ) : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ)) ≤
        2 * (C : ℝ) / t := by
    calc
      _ = ∑ s ∈ S, ((1 + 1 / (m s : ℝ)) / n -
          ((t - C : ℕ) : ℝ) * (1 + 1 / (m s : ℝ)) / ((n * t : ℕ) : ℝ)) :=
        (Finset.sum_sub_distrib _ _).symm
      _ ≤ ∑ _s ∈ S, 2 * (C : ℝ) / ((n * t : ℕ) : ℝ) := Finset.sum_le_sum hcost
      _ = (S.card : ℝ) * (2 * (C : ℝ) / ((n * t : ℕ) : ℝ)) := by simp
      _ ≤ (n : ℝ) * (2 * (C : ℝ) / ((n * t : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card hS).trans_eq (Finset.card_range n)
      _ = 2 * (C : ℝ) / t := by
        push_cast
        field_simp [hn0, ht0]
  linarith

end Submission.Obl.k4_matching_trimmed_grid
