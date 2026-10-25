/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/DecodedPartnerLists.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.RetainedPartnerLists

/-! Return retained partner lists to original labels, including the two native branches. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open Set
open scoped Classical

noncomputable section

theorem lift_finite_partner_lists {n₁ n₂ N₁ N₂ J : ℕ}
    (idx₁ : Fin n₁ → Fin N₁) (idx₂ : Fin n₂ → Fin N₂)
    (hfiber : ∀ i, (Finset.univ.filter fun j => idx₁ j = i).card ≤ J)
    (lists : Fin n₁ → Finset (Fin n₂)) {B : ℝ} (hB : 0 ≤ B)
    (hcount : ∀ i, ((lists i).card : ℝ) ≤ B) :
    ∃ oldLists : Fin N₁ → Finset (Fin N₂),
      (∀ i, ((oldLists i).card : ℝ) ≤ (J : ℝ) * B) ∧
      ∀ i j, j ∈ lists i → idx₂ j ∈ oldLists (idx₁ i) := by
  let fiber (i : Fin N₁) := Finset.univ.filter (fun j => idx₁ j = i)
  let oldLists (i : Fin N₁) := ((fiber i).biUnion lists).image idx₂
  refine ⟨oldLists, ?_, ?_⟩
  · intro i
    have hcard : (oldLists i).card ≤ ∑ j ∈ fiber i, (lists j).card :=
      Finset.card_image_le.trans Finset.card_biUnion_le
    calc
      _ ≤ ∑ j ∈ fiber i, ((lists j).card : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _j ∈ fiber i, B := Finset.sum_le_sum fun j _ => hcount j
      _ = ((fiber i).card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ) * B := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hfiber i)) hB
  · intro i j hj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hj⟩, rfl⟩

theorem injective_fiber_card_le_one {n N : ℕ} (idx : Fin n → Fin N) (hinj : Function.Injective idx) :
    ∀ i, (Finset.univ.filter fun j => idx j = i).card ≤ 1 := by
  intro i
  apply Finset.card_le_one.mpr
  intro j hj k hk
  exact hinj ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm)

theorem native_branch_fiber_card_le_two {n N : ℕ}
    (idx : Fin n → Fin N × Bool) (hinj : Function.Injective idx) :
    ∀ i, (Finset.univ.filter fun j => (idx j).1 = i).card ≤ 2 := by
  intro i
  let S : Finset (Fin n) := Finset.univ.filter (fun j => (idx j).1 = i)
  have hbranch : Function.Injective (fun j : S => (idx j.val).2) := by
    intro j k h
    apply Subtype.ext
    apply hinj
    exact Prod.ext ((Finset.mem_filter.mp j.property).2.trans (Finset.mem_filter.mp k.property).2.symm) h
  have h := Fintype.card_le_of_injective _ hbranch
  simpa only [Fintype.card_coe, Fintype.card_bool] using h

/-- Uniform comparison and original quarter-ball counts produce the actual
forward/reverse lists on original labels. Forgetting the native sign costs at
most the stated fiber multiplicity, which is two for a true parent. -/
theorem decoded_retained_partner_lists {Ω : Type*} {n₁ n₂ N₁ N₂ J₁ J₂ : ℕ}
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) (G : Set Ω)
    (f₁ : Fin n₁ → EuclideanSpace ℝ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℝ (Fin 3) → ℂ) {M B : ℝ} (hB : 0 ≤ B)
    (hagreement : ∀ p ∈ G, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₁ (i₁ p) x - f₂ (i₂ p) x‖ ≤ M)
    (hforward : ∀ i, ((Finset.univ.filter fun j : Fin n₂ =>
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f₂ j x - f₁ i x‖ ≤ M).card : ℝ) ≤ B)
    (hreverse : ∀ j, ((Finset.univ.filter fun i : Fin n₁ =>
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f₁ i x - f₂ j x‖ ≤ M).card : ℝ) ≤ B)
    (idx₁ : Fin n₁ → Fin N₁) (idx₂ : Fin n₂ → Fin N₂)
    (hfiber₁ : ∀ i, (Finset.univ.filter fun j => idx₁ j = i).card ≤ J₁)
    (hfiber₂ : ∀ i, (Finset.univ.filter fun j => idx₂ j = i).card ≤ J₂) :
    ∃ (forward : Fin N₁ → Finset (Fin N₂)) (reverse : Fin N₂ → Finset (Fin N₁)),
      (∀ i, ((forward i).card : ℝ) ≤ (J₁ : ℝ) * B) ∧
      (∀ j, ((reverse j).card : ℝ) ≤ (J₂ : ℝ) * B) ∧
      ∀ p ∈ G, idx₂ (i₂ p) ∈ forward (idx₁ (i₁ p)) ∧ idx₁ (i₁ p) ∈ reverse (idx₂ (i₂ p)) := by
  let F (i : Fin n₁) := Finset.univ.filter (fun j : Fin n₂ => ∃ p ∈ G, i₁ p = i ∧ i₂ p = j)
  let R (j : Fin n₂) := Finset.univ.filter (fun i : Fin n₁ => ∃ p ∈ G, i₁ p = i ∧ i₂ p = j)
  obtain ⟨hF, hR⟩ := retained_partner_list_bounds i₁ i₂ G f₁ f₂ hagreement hforward hreverse
  obtain ⟨forward, hforward', hmemF⟩ := lift_finite_partner_lists idx₁ idx₂ hfiber₁ F hB hF
  obtain ⟨reverse, hreverse', hmemR⟩ := lift_finite_partner_lists idx₂ idx₁ hfiber₂ R hB hR
  refine ⟨forward, reverse, hforward', hreverse', ?_⟩
  intro p hp
  have hpair : ∃ q ∈ G, i₁ q = i₁ p ∧ i₂ q = i₂ p := ⟨p, hp, rfl, rfl⟩
  exact ⟨hmemF _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair⟩),
    hmemR _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair⟩)⟩

theorem QuarterListBound.decoded_lists {Ω : Type*} {n₁ n₂ N₁ N₂ J₁ J₂ : ℕ}
    {a L d Λ : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hΛ : 1 ≤ Λ)
    {f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ}
    {f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ}
    (hcount : QuarterListBound a L d f₁ f₂)
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) (G : Set Ω)
    (hagreement : ∀ p ∈ G, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₁ (i₁ p) (emb x) - f₂ (i₂ p) (emb x)‖ ≤ Λ * a)
    (idx₁ : Fin n₁ → Fin N₁) (idx₂ : Fin n₂ → Fin N₂)
    (hfiber₁ : ∀ i, (Finset.univ.filter fun j => idx₁ j = i).card ≤ J₁)
    (hfiber₂ : ∀ i, (Finset.univ.filter fun j => idx₂ j = i).card ≤ J₂) :
    ∃ (forward : Fin N₁ → Finset (Fin N₂)) (reverse : Fin N₂ → Finset (Fin N₁)),
      (∀ i, ((forward i).card : ℝ) ≤ (J₁ : ℝ) * (L * Λ ^ d)) ∧
      (∀ j, ((reverse j).card : ℝ) ≤ (J₂ : ℝ) * (L * Λ ^ d)) ∧
      ∀ p ∈ G, idx₂ (i₂ p) ∈ forward (idx₁ (i₁ p)) ∧ idx₁ (i₁ p) ∈ reverse (idx₂ (i₂ p)) := by
  have hRa : a ≤ Λ * a := by nlinarith only [hΛ, ha]
  have hcounts := hcount (Λ * a) hRa
  have hratio : Λ * a / a = Λ := mul_div_cancel_right₀ Λ ha.ne'
  rw [hratio] at hcounts
  exact decoded_retained_partner_lists i₁ i₂ G
    (fun i x => f₁ i (emb x)) (fun j x => f₂ j (emb x))
    (mul_nonneg hL (Real.rpow_nonneg (by linarith only [hΛ]) _))
    hagreement hcounts.1 hcounts.2 idx₁ idx₂ hfiber₁ hfiber₂

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
