/- From o050 session x0161, commit 6416281. -/
import Mathlib

/-!
# Sampling every sign vector at the roots of one polynomial

If every member of a finite family of real polynomials is zero or divides `q`, and `q ≠ 0`
vanishes at `0`, then every sign vector the family realizes on `ℝ` is realized at a root of
`q * q' * q(X - 1) * q(X + 1)`: at a root of `q`, at a critical point of `q` between two
consecutive roots (Rolle), or one unit beyond the extreme roots.
-/

namespace Submission.Obl.k4_sign_projection

open Polynomial

/-- A real polynomial without roots in an order-connected set has constant sign on it. -/
theorem sign_eval_eq_of_no_roots {f : ℝ[X]} {S : Set ℝ} (hS : S.OrdConnected)
    (hf : ∀ z ∈ S, f.eval z ≠ 0) {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) :
    SignType.sign (f.eval u) = SignType.sign (f.eval v) := by
  have key : ∀ a b, a ∈ S → b ∈ S → a ≤ b →
      SignType.sign (f.eval a) = SignType.sign (f.eval b) := by
    intro a b ha hb hab
    have hfa := hf a ha
    have hfb := hf b hb
    rcases lt_or_gt_of_ne hfa with ha' | ha' <;> rcases lt_or_gt_of_ne hfb with hb' | hb'
    · rw [sign_neg ha', sign_neg hb']
    · exfalso
      obtain ⟨c, hc, hc0⟩ : (0 : ℝ) ∈ (fun x => f.eval x) '' Set.Icc a b :=
        intermediate_value_Icc hab f.continuous.continuousOn ⟨ha'.le, hb'.le⟩
      exact hf c (hS.out ha hb hc) hc0
    · exfalso
      obtain ⟨c, hc, hc0⟩ : (0 : ℝ) ∈ (fun x => f.eval x) '' Set.Icc a b :=
        intermediate_value_Icc' hab f.continuous.continuousOn ⟨hb'.le, ha'.le⟩
      exact hf c (hS.out ha hb hc) hc0
    · rw [sign_pos ha', sign_pos hb']
  rcases le_total u v with h | h
  · exact key u v hu hv h
  · exact (key v u hv hu h).symm

/-- A nonzero polynomial composed with `X + C c` is nonzero. -/
theorem comp_X_add_C_ne_zero {q : ℝ[X]} (hq : q ≠ 0) (c : ℝ) : q.comp (X + C c) ≠ 0 := by
  intro h
  have h1 : (q.comp (X + C c)).comp (X - C c) = q := by
    rw [comp_assoc]
    simp
  rw [h, zero_comp] at h1
  exact hq h1.symm

/-- Every sign vector of a family whose nonzero members divide `q` is realized at a root of
`q * q' * q(X - 1) * q(X + 1)`, provided `q ≠ 0` and `q(0) = 0`. -/
theorem root_sampling (η : Type) [Fintype η] (p : η → ℝ[X]) (q : ℝ[X])
    (hq : q ≠ 0) (hq0 : q.eval 0 = 0) (hp : ∀ i, p i = 0 ∨ p i ∣ q) (t : ℝ) :
    ∃ u ∈ (q * derivative q * q.comp (X - C 1) * q.comp (X + C 1)).roots,
      ∀ i, SignType.sign ((p i).eval u) = SignType.sign ((p i).eval t) := by
  classical
  have hdeg : 0 < q.natDegree := by
    by_contra h
    replace h : q.natDegree ≤ 0 := not_lt.mp h
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero h
    have h0 : q.coeff 0 = 0 := by
      have h' := hq0
      rw [hqC, eval_C] at h'
      exact h'
    exact hq (by rw [hqC, h0, C_0])
  have hder : derivative q ≠ 0 := by
    intro h
    have := derivative_eq_zero.mp h
    omega
  have hcomp1 : q.comp (X - C 1) ≠ 0 := by
    have := comp_X_add_C_ne_zero hq (-1)
    simpa [sub_eq_add_neg] using this
  have hcomp2 : q.comp (X + C 1) ≠ 0 := comp_X_add_C_ne_zero hq 1
  have hH : q * derivative q * q.comp (X - C 1) * q.comp (X + C 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq hder) hcomp1) hcomp2
  have hmem : ∀ u, (q.eval u = 0 ∨ (derivative q).eval u = 0 ∨ q.eval (u - 1) = 0 ∨
      q.eval (u + 1) = 0) →
      u ∈ (q * derivative q * q.comp (X - C 1) * q.comp (X + C 1)).roots := by
    intro u hu
    rw [mem_roots hH, IsRoot.def]
    simp only [eval_mul, eval_comp, eval_sub, eval_add, eval_X, eval_C]
    rcases hu with h | h | h | h <;> simp [h]
  have hsign : ∀ S : Set ℝ, S.OrdConnected → (∀ z ∈ S, q.eval z ≠ 0) →
      ∀ u ∈ S, ∀ v ∈ S, ∀ i, SignType.sign ((p i).eval u) = SignType.sign ((p i).eval v) := by
    intro S hS hqS u hu v hv i
    rcases hp i with h | h
    · simp [h]
    · apply sign_eval_eq_of_no_roots hS _ hu hv
      intro z hz hpz
      apply hqS z hz
      obtain ⟨r, hr⟩ := h
      rw [hr, eval_mul, hpz, zero_mul]
  by_cases ht : q.eval t = 0
  · exact ⟨t, hmem t (Or.inl ht), fun i => rfl⟩
  set Z := q.roots.toFinset with hZ
  have hmemZ : ∀ z, z ∈ Z ↔ q.eval z = 0 := by
    intro z
    rw [hZ, Multiset.mem_toFinset, mem_roots hq, IsRoot.def]
  set L := Z.filter (· < t) with hLdef
  set U := Z.filter (t < ·) with hUdef
  have hLmem : ∀ z, q.eval z = 0 → z < t → z ∈ L := fun z hz hzt =>
    Finset.mem_filter.mpr ⟨(hmemZ z).mpr hz, hzt⟩
  have hUmem : ∀ z, q.eval z = 0 → t < z → z ∈ U := fun z hz hzt =>
    Finset.mem_filter.mpr ⟨(hmemZ z).mpr hz, hzt⟩
  by_cases hL : L.Nonempty <;> by_cases hU : U.Nonempty
  · -- Rolle between the two roots of `q` around `t`
    set a := L.max' hL
    set b := U.min' hU
    have haL : a ∈ L := L.max'_mem hL
    have hbU : b ∈ U := U.min'_mem hU
    have hat : a < t := (Finset.mem_filter.mp haL).2
    have htb : t < b := (Finset.mem_filter.mp hbU).2
    have hqa : q.eval a = 0 := (hmemZ a).mp (Finset.mem_filter.mp haL).1
    have hqb : q.eval b = 0 := (hmemZ b).mp (Finset.mem_filter.mp hbU).1
    have hfree : ∀ z ∈ Set.Ioo a b, q.eval z ≠ 0 := by
      intro z hz hqz
      rcases lt_trichotomy z t with h | h | h
      · have := L.le_max' z (hLmem z hqz h)
        linarith [hz.1]
      · exact ht (h ▸ hqz)
      · have := U.min'_le z (hUmem z hqz h)
        linarith [hz.2]
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (lt_trans hat htb)
      q.continuous.continuousOn (hqa.trans hqb.symm)
    rw [Polynomial.deriv] at hc0
    exact ⟨c, hmem c (Or.inr (Or.inl hc0)),
      hsign (Set.Ioo a b) Set.ordConnected_Ioo hfree c hc t ⟨hat, htb⟩⟩
  · -- `t` lies beyond the largest root `a`: sample at `a + 1`
    set a := L.max' hL
    have haL : a ∈ L := L.max'_mem hL
    have hat : a < t := (Finset.mem_filter.mp haL).2
    have hqa : q.eval a = 0 := (hmemZ a).mp (Finset.mem_filter.mp haL).1
    have hfree : ∀ z ∈ Set.Ioi a, q.eval z ≠ 0 := by
      intro z hz hqz
      rcases lt_trichotomy z t with h | h | h
      · have := L.le_max' z (hLmem z hqz h)
        exact absurd hz (not_lt.mpr this)
      · exact ht (h ▸ hqz)
      · exact hU ⟨z, hUmem z hqz h⟩
    refine ⟨a + 1, hmem (a + 1) (Or.inr (Or.inr (Or.inl (by simpa using hqa)))), ?_⟩
    exact hsign (Set.Ioi a) Set.ordConnected_Ioi hfree (a + 1)
      (show a < a + 1 by linarith) t hat
  · -- `t` lies before the smallest root `b`: sample at `b - 1`
    set b := U.min' hU
    have hbU : b ∈ U := U.min'_mem hU
    have htb : t < b := (Finset.mem_filter.mp hbU).2
    have hqb : q.eval b = 0 := (hmemZ b).mp (Finset.mem_filter.mp hbU).1
    have hfree : ∀ z ∈ Set.Iio b, q.eval z ≠ 0 := by
      intro z hz hqz
      rcases lt_trichotomy z t with h | h | h
      · exact hL ⟨z, hLmem z hqz h⟩
      · exact ht (h ▸ hqz)
      · have := U.min'_le z (hUmem z hqz h)
        exact absurd hz (not_lt.mpr this)
    refine ⟨b - 1, hmem (b - 1) (Or.inr (Or.inr (Or.inr (by simpa using hqb)))), ?_⟩
    exact hsign (Set.Iio b) Set.ordConnected_Iio hfree (b - 1)
      (show b - 1 < b by linarith) t htb
  · -- no roots on either side of `t`: impossible, since `q(0) = 0`
    exfalso
    rcases lt_trichotomy 0 t with h | h | h
    · exact hL ⟨0, hLmem 0 hq0 h⟩
    · exact ht (h ▸ hq0)
    · exact hU ⟨0, hUmem 0 hq0 h⟩

end Submission.Obl.k4_sign_projection
