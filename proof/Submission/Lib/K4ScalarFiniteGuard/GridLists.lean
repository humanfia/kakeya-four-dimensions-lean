/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4QuadraticSublevel

/-!
Finite observation-list transfer between arbitrary positive power meshes.
The diameter-to-bin estimate is imported from the accepted sublevel library.
-/

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open Set MeasureTheory

/-- The fine bins which can meet one interval of the new observation grid
form a finite set, uniformly in the location of that interval. -/
theorem overlapBinEstimate (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (c : ℤ) :
    ((fun x : ℝ => ⌊x / α⌋) '' Ico ((c : ℝ) * β) (((c : ℝ) + 1) * β)).Finite ∧
      (((fun x : ℝ => ⌊x / α⌋) ''
        Ico ((c : ℝ) * β) (((c : ℝ) + 1) * β)).ncard : ℝ) ≤ 2 * β / α + 2 := by
  have hh := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Ico ((c : ℝ) * β) (((c : ℝ) + 1) * β)) hβ.le hα 0 (by
      intro x hx y hy
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  simpa only [sub_zero] using hh

/-- A finite list of all old bins compatible with a new hidden bin. -/
noncomputable def overlapBins (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (c : ℤ) : Finset ℤ :=
  (overlapBinEstimate α β hα hβ c).1.toFinset

theorem overlapBins_card_le (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (c : ℤ) :
    ((overlapBins α β hα hβ c).card : ℝ) ≤ 2 * β / α + 2 := by
  change (((overlapBinEstimate α β hα hβ c).1.toFinset).card : ℝ) ≤ _
  rw [← Set.ncard_eq_toFinset_card _ (overlapBinEstimate α β hα hβ c).1]
  exact (overlapBinEstimate α β hα hβ c).2

/-- Every real hidden coordinate supplies one compatible old bin. -/
theorem floor_mem_overlapBins (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    ⌊x / α⌋ ∈ overlapBins α β hα hβ ⌊x / β⌋ := by
  rw [overlapBins, Set.Finite.mem_toFinset]
  refine ⟨x, ?_, rfl⟩
  constructor
  · exact (le_div_iff₀ hβ).1 (Int.floor_le (x / β))
  · exact (div_lt_iff₀ hβ).1 (Int.lt_floor_add_one (x / β))

/-- Moving a power-grid exponent by `|b-b'|` costs only that power and a
fixed factor four, independently of all observed integer labels. -/
theorem power_overlapBins_card (N b b' : ℝ) (hN : 1 ≤ N) (c : ℤ) :
    ((overlapBins (N ^ (-b)) (N ^ (-b'))
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _) c).card : ℝ) ≤
        4 * N ^ |b - b'| := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hratio : N ^ (-b') / N ^ (-b) = N ^ (b - b') := by
    rw [← Real.rpow_sub hNpos]
    congr 1
    ring
  have hpow : N ^ (b - b') ≤ N ^ |b - b'| :=
    Real.rpow_le_rpow_of_exponent_le hN (le_abs_self _)
  have hone : 1 ≤ N ^ |b - b'| := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hN (abs_nonneg (b - b'))
  have hc := overlapBins_card_le (N ^ (-b)) (N ^ (-b'))
    (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hNpos _) c
  have heq : 2 * N ^ (-b') / N ^ (-b) = 2 * (N ^ (-b') / N ^ (-b)) := by ring
  rw [heq, hratio] at hc
  linarith

/-- Transfer an old observation list by taking the union over compatible
old integer bins; exact base coordinates are retained. -/
noncomputable def transferGridList {X ι : Type*}
    (bins : ℤ → Finset ℤ) (Λ : X × ℤ → Finset ι) (z : X × ℤ) : Finset ι := by
  classical
  exact (bins z.2).biUnion fun c => Λ (z.1, c)

theorem transferGridList_mem {X ι : Type*}
    (bins : ℤ → Finset ℤ) (Λ : X × ℤ → Finset ι) (z : X × ℤ)
    (c : ℤ) (i : ι) (hc : c ∈ bins z.2) (hi : i ∈ Λ (z.1, c)) :
    i ∈ transferGridList bins Λ z := by
  classical
  exact Finset.mem_biUnion.2 ⟨c, hc, hi⟩

/-- The transferred list has measurable label membership even though its
finite compatible-bin set depends on the observed integer label. -/
theorem measurableSet_transferGridList {X ι : Type*} [MeasurableSpace X]
    (bins : ℤ → Finset ℤ) (Λ : X × ℤ → Finset ι)
    (hΛ : ∀ i, MeasurableSet {z | i ∈ Λ z}) (i : ι) :
    MeasurableSet {z | i ∈ transferGridList bins Λ z} := by
  classical
  change MeasurableSet {z : X × ℤ | i ∈ (bins z.2).biUnion fun c => Λ (z.1, c)}
  simp only [Finset.mem_biUnion]
  have hm (c : ℤ) : MeasurableSet {z : X × ℤ | c ∈ bins z.2 ∧ i ∈ Λ (z.1, c)} := by
    exact (((Set.to_countable {a : ℤ | c ∈ bins a}).measurableSet).preimage
      measurable_snd).inter ((hΛ i).preimage (measurable_fst.prodMk measurable_const))
  simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hm

/-- List cardinalities multiply by at most the compatible-bin count. -/
theorem transferGridList_card {X ι : Type*}
    (bins : ℤ → Finset ℤ) (Λ : X × ℤ → Finset ι) (z : X × ℤ) (K : ℝ)
    (hΛ : ∀ c ∈ bins z.2, ((Λ (z.1, c)).card : ℝ) ≤ K) :
    ((transferGridList bins Λ z).card : ℝ) ≤ ((bins z.2).card : ℝ) * K := by
  classical
  calc
    _ ≤ ∑ c ∈ bins z.2, ((Λ (z.1, c)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := bins z.2) (t := fun c => Λ (z.1, c)))
    _ ≤ ∑ _c ∈ bins z.2, K := Finset.sum_le_sum fun c hc => hΛ c hc
    _ = _ := by simp

end Submission.Lib.K4ScalarFiniteGuard
