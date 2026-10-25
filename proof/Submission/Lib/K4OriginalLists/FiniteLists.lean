/-
Adapted from: here:o064
Written in this workspace by session x0217, from the supplied paper,
Lemma a03:actual-lists. No external formal code.
-/

import Mathlib

/-!
Finite original-law recovery of lists, the discrete form of the supplied
paper's Lemma `a03:actual-lists`.  The maximizing table uses only the coarse
observed record.  Analytical masks are used solely to witness success.
-/

namespace Submission.Lib.K4OriginalLists

open Finset

variable {ι τ β : Type*} [Fintype ι] [Fintype τ] [Fintype β]

omit [Fintype β] in
/-- Among the allowed labels, a list of bounded size maximizing any given score exists. -/
theorem exists_maximizing_list (allowed : Finset β) (D : ℕ) (w : β → ℝ) :
    ∃ s : Finset β, s ⊆ allowed ∧ s.card ≤ D ∧
      ∀ t : Finset β, t ⊆ allowed → t.card ≤ D → ∑ a ∈ t, w a ≤ ∑ a ∈ s, w a := by
  classical
  let candidates := allowed.powerset.filter (fun s => s.card ≤ D)
  have hempty : (∅ : Finset β) ∈ candidates := by simp [candidates]
  obtain ⟨s, hs, hmax⟩ := candidates.exists_max_image (fun s => ∑ a ∈ s, w a)
    ⟨∅, hempty⟩
  have hs' : s ⊆ allowed ∧ s.card ≤ D := by simpa [candidates] using hs
  refine ⟨s, hs'.1, hs'.2, ?_⟩
  intro t ht hcard
  exact hmax t (by simp [candidates, ht, hcard])

/-- Success mass for a rule allowed to inspect a coarse record and a finer base position. -/
noncomputable def listMass (p : ι → τ → β → ℝ) (L : ι → τ → Finset β) : ℝ :=
  ∑ c, ∑ x, ∑ a ∈ L c x, p c x a

omit [Fintype β] in
/-- Pointwise domination of unnormalized laws preserves the success of every list rule. -/
theorem listMass_mono {p q : ι → τ → β → ℝ} (hpq : ∀ c x a, p c x a ≤ q c x a)
    (L : ι → τ → Finset β) : listMass p L ≤ listMass q L := by
  classical
  exact sum_le_sum fun c _ => sum_le_sum fun x _ => sum_le_sum fun a _ => hpq c x a

/-- Every list event is stable under an `L¹` change of the joint law. -/
theorem abs_listMass_sub_le (p q : ι → τ → β → ℝ) (L : ι → τ → Finset β) :
    |listMass p L - listMass q L| ≤ ∑ c, ∑ x, ∑ a, |p c x a - q c x a| := by
  classical
  simp only [listMass, ← sum_sub_distrib]
  calc
    |∑ c, ∑ x, ∑ a ∈ L c x, (p c x a - q c x a)| ≤
        ∑ c, ∑ x, ∑ a ∈ L c x, |p c x a - q c x a| := by
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun c _ =>
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ c, ∑ x, ∑ a, |p c x a - q c x a| := by
      exact sum_le_sum fun c _ => sum_le_sum fun x _ =>
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => abs_nonneg _)

omit [Fintype β] in
/-- After averaging, the same best list works at every fine position of one record. -/
theorem exists_coarse_list (allowed : Finset β) (D : ℕ)
    (ρ : ι → τ → ℝ) (w : ι → β → ℝ) (hρ : ∀ c x, 0 ≤ ρ c x) :
    ∃ table : ι → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      ∀ L : ι → τ → Finset β,
        (∀ c x, L c x ⊆ allowed ∧ (L c x).card ≤ D) →
        listMass (fun c x a => ρ c x * w c a) L ≤
          listMass (fun c x a => ρ c x * w c a) (fun c _ => table c) := by
  classical
  choose table hsub hcard hmax using fun c => exists_maximizing_list allowed D (w c)
  refine ⟨table, fun c => ⟨hsub c, hcard c⟩, ?_⟩
  intro L hL
  apply sum_le_sum
  intro c _
  apply sum_le_sum
  intro x _
  simp only [← mul_sum]
  exact mul_le_mul_of_nonneg_left (hmax c (L c x) (hL c x).1 (hL c x).2) (hρ c x)

/-- A successful list on an arbitrary sublaw gives a coarse table on the original law.
The averaging error is charged twice, without conditioning or renormalizing the sublaw. -/
theorem recover_original_list (allowed : Finset β) (D : ℕ)
    (p mask : ι → τ → β → ℝ) (ρ : ι → τ → ℝ) (w : ι → β → ℝ)
    (hmask : ∀ c x a, mask c x a ≤ p c x a) (hρ : ∀ c x, 0 ≤ ρ c x)
    (e m : ℝ) (herror : (∑ c, ∑ x, ∑ a, |p c x a - ρ c x * w c a|) ≤ e)
    (L : ι → τ → Finset β)
    (hL : ∀ c x, L c x ⊆ allowed ∧ (L c x).card ≤ D)
    (hsuccess : m ≤ listMass mask L) :
    ∃ table : ι → Finset β,
      (∀ c, table c ⊆ allowed ∧ (table c).card ≤ D) ∧
      m - 2 * e ≤ listMass p (fun c _ => table c) := by
  classical
  obtain ⟨table, htable, hmax⟩ := exists_coarse_list allowed D ρ w hρ
  have hdom := listMass_mono hmask L
  have hfirst := (abs_le.mp ((abs_listMass_sub_le p
    (fun c x a => ρ c x * w c a) L).trans herror)).2
  have hlast := (abs_le.mp ((abs_listMass_sub_le p
    (fun c x a => ρ c x * w c a) (fun c _ => table c)).trans herror)).1
  have havg := hmax L hL
  exact ⟨table, htable, by linarith⟩

end Submission.Lib.K4OriginalLists
