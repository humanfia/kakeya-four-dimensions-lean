import Submission.Obl.k4_sign_projection.LocalAlgebra
import Submission.Obl.k4_sign_projection.JumpSum

namespace Submission.Obl.k4_sign_projection

open Polynomial Filter
open scoped Topology BigOperators

/-- Twice the local Cauchy index of the rational function `p / q` at `a`. -/
noncomputable def cauchyAt (p q : Polynomial ℝ) (a : ℝ) : ℤ :=
  if p.rootMultiplicity a < q.rootMultiplicity a then
    rightSign (p * q) a - leftSign (p * q) a else 0

/-- Twice the Cauchy index over the real line. -/
noncomputable def cauchyIndex (p q : Polynomial ℝ) : ℤ :=
  ∑ a ∈ q.roots.toFinset, cauchyAt p q a

@[simp] theorem cauchyAt_zero_left (q : Polynomial ℝ) (a : ℝ) : cauchyAt 0 q a = 0 := by
  simp [cauchyAt]
@[simp] theorem cauchyAt_zero_right (p : Polynomial ℝ) (a : ℝ) : cauchyAt p 0 a = 0 := by
  simp [cauchyAt]
@[simp] theorem cauchyIndex_zero_left (q : Polynomial ℝ) : cauchyIndex 0 q = 0 := by
  simp [cauchyIndex]
@[simp] theorem cauchyIndex_zero_right (p : Polynomial ℝ) : cauchyIndex p 0 = 0 := by
  simp [cauchyIndex]

theorem cauchyAt_eq_zero_of_not_root {p q : Polynomial ℝ} {a : ℝ}
    (ha : q.eval a ≠ 0) : cauchyAt p q a = 0 := by
  simp [cauchyAt, rootMultiplicity_eq_zero ha]

theorem sum_poly_jumps (p : Polynomial ℝ) :
    ∑ a ∈ p.roots.toFinset, (rightSign p a - leftSign p a) = topSign p - botSign p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  apply sum_jumps_eq p.roots.toFinset (rightSign p) (leftSign p) (topSign p) (botSign p)
    (eventually_rightSign_right p) (eventually_rightSign_left p) _
    (eventually_rightSign_top p) (eventually_rightSign_bot p)
  intro a ha
  have ha0 : p.eval a ≠ 0 := by
    simpa only [Multiset.mem_toFinset, mem_roots hp, IsRoot] using ha
  rw [rightSign_eq_zsign ha0, leftSign_eq_zsign ha0]

theorem cauchyAt_reciprocity (p q : Polynomial ℝ) (a : ℝ) :
    cauchyAt p q a + cauchyAt q p a = rightSign (p * q) a - leftSign (p * q) a := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rcases lt_trichotomy (p.rootMultiplicity a) (q.rootMultiplicity a) with h | h | h
  · simp [cauchyAt, h, h.not_gt]
  · have he : leftSign (p * q) a = rightSign (p * q) a := by
      rw [leftSign, rootMultiplicity_mul (mul_ne_zero hp hq), h, ← two_mul,
        pow_mul, neg_one_sq, one_pow, one_mul]
    simp [cauchyAt, h, he]
  · simp [cauchyAt, h, h.not_gt, mul_comm q p]

/-- Inversion exchanges the contributions of zeros and poles. -/
theorem cauchyIndex_reciprocity (p q : Polynomial ℝ) :
    cauchyIndex p q + cauchyIndex q p = topSign (p * q) - botSign (p * q) := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  let s := (p * q).roots.toFinset
  have hs : s = p.roots.toFinset ∪ q.roots.toFinset := by
    simp only [s, roots_mul (mul_ne_zero hp hq), Multiset.toFinset_add]
  have hsp : (∑ a ∈ p.roots.toFinset, cauchyAt q p a) = ∑ a ∈ s, cauchyAt q p a := by
    apply Finset.sum_subset
    · rw [hs]
      exact Finset.subset_union_left
    · intro a _ ha
      apply cauchyAt_eq_zero_of_not_root
      simpa only [Multiset.mem_toFinset, mem_roots hp, IsRoot] using ha
  have hsq : (∑ a ∈ q.roots.toFinset, cauchyAt p q a) = ∑ a ∈ s, cauchyAt p q a := by
    apply Finset.sum_subset
    · rw [hs]
      exact Finset.subset_union_right
    · intro a _ ha
      apply cauchyAt_eq_zero_of_not_root
      simpa only [Multiset.mem_toFinset, mem_roots hq, IsRoot] using ha
  calc
    cauchyIndex p q + cauchyIndex q p =
        ∑ a ∈ s, (cauchyAt p q a + cauchyAt q p a) := by
      rw [Finset.sum_add_distrib, ← hsp, ← hsq]
      rfl
    _ = ∑ a ∈ s, (rightSign (p * q) a - leftSign (p * q) a) :=
      Finset.sum_congr rfl (fun _ _ => cauchyAt_reciprocity p q _)
    _ = topSign (p * q) - botSign (p * q) := sum_poly_jumps (p * q)

theorem cauchyAt_eq_zero_of_order_dvd (p q : Polynomial ℝ) (a : ℝ)
    (h : (X - C a) ^ q.rootMultiplicity a ∣ p) : cauchyAt p q a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  have hm := (le_rootMultiplicity_iff hp).mpr h
  simp [cauchyAt, not_lt_of_ge hm]

/-- A polynomial added to a rational function does not change its local index. -/
theorem cauchyAt_add_mul (p q r : Polynomial ℝ) (a : ℝ) :
    cauchyAt (p + q * r) q a = cauchyAt p q a := by
  classical
  have hqr : (X - C a) ^ q.rootMultiplicity a ∣ q * r :=
    dvd_mul_of_dvd_left (pow_rootMultiplicity_dvd q a) r
  by_cases hp : p = 0
  · simpa only [hp, zero_add, cauchyAt_zero_left] using
      cauchyAt_eq_zero_of_order_dvd (q * r) q a hqr
  by_cases h : p.rootMultiplicity a < q.rootMultiplicity a
  · have hv : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q * r :=
      (pow_dvd_pow (X - C a) (Nat.succ_le_of_lt h)).trans hqr
    obtain ⟨hm, hr, hl⟩ := local_signs_add_high hp a hv
    simp only [cauchyAt, hm, h, ite_true, rightSign_mul, leftSign_mul, hr, hl]
  · have hmp : q.rootMultiplicity a ≤ p.rootMultiplicity a := Nat.le_of_not_gt h
    have hpd : (X - C a) ^ q.rootMultiplicity a ∣ p :=
      (pow_dvd_pow (X - C a) hmp).trans (pow_rootMultiplicity_dvd p a)
    rw [cauchyAt_eq_zero_of_order_dvd _ _ _ (dvd_add hpd hqr),
      cauchyAt_eq_zero_of_order_dvd _ _ _ hpd]

theorem cauchyIndex_add_mul (p q r : Polynomial ℝ) :
    cauchyIndex (p + q * r) q = cauchyIndex p q := by
  classical
  exact Finset.sum_congr rfl (fun a _ => cauchyAt_add_mul p q r a)

theorem cauchyIndex_mod (p q : Polynomial ℝ) :
    cauchyIndex (p % q) q = cauchyIndex p q := by
  have h := cauchyIndex_add_mul (p % q) q (p / q)
  rw [EuclideanDomain.mod_add_div] at h
  exact h.symm

theorem rootMultiplicity_neg_eq (p : Polynomial ℝ) (a : ℝ) :
    (-p).rootMultiplicity a = p.rootMultiplicity a := by
  by_cases hp : p = 0
  · simp [hp]
  have hp' : C (-1 : ℝ) * p ≠ 0 := mul_ne_zero (by simp) hp
  have h : -p = C (-1 : ℝ) * p := by simp
  rw [h, rootMultiplicity_mul hp', rootMultiplicity_C, zero_add]

theorem cauchyAt_neg (p q : Polynomial ℝ) (a : ℝ) :
    cauchyAt (-p) q a = -cauchyAt p q a := by
  simp only [cauchyAt, rootMultiplicity_neg_eq, neg_mul, rightSign_neg, leftSign_neg]
  split_ifs <;> ring

theorem cauchyIndex_neg (p q : Polynomial ℝ) :
    cauchyIndex (-p) q = -cauchyIndex p q := by
  classical
  simp only [cauchyIndex, cauchyAt_neg, Finset.sum_neg_distrib]

/-- Euclidean recursion for the doubled Cauchy index. -/
theorem cauchyIndex_rec (p q : Polynomial ℝ) :
    cauchyIndex q p = topSign (p * q) - botSign (p * q) + cauchyIndex ((-p) % q) q := by
  rw [cauchyIndex_mod, cauchyIndex_neg]
  have h := cauchyIndex_reciprocity p q
  omega

end Submission.Obl.k4_sign_projection
