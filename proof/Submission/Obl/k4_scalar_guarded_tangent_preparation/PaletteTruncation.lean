/-
Adapted from this LOT tree, o134, session x0438, branch x0438,
file Submission/Obl/k4_scalar_guarded_tangent_obstruction/PaletteTruncation.lean.
The reference-law and palette constructions retain their original denominators.
-/

import Submission.Obl.k4_matching_palette_likelihood.Window

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

namespace PaletteTruncation

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

variable {α : Type*} [Fintype α]

/-- The parent reference law is fixed. Only the successful joint atoms are
deleted; neither the parent weights nor its velocity palette is updated. -/
def retained (p : α → ℝ) (E Z : α → ℕ) (R : ℝ) (x : α) : ℝ := by
  classical
  exact if colorMass p E Z (E x) (Z x) ≤
    R * fiberMass p E (E x) * colorMass p (fun _ => 0) Z 0 (Z x) then p x else 0

theorem retained_nonneg (p : α → ℝ) (E Z : α → ℕ) (R : ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : α) : 0 ≤ retained p E Z R x := by
  classical
  unfold retained
  split_ifs
  · exact hp x
  · exact le_rfl

theorem retained_le (p : α → ℝ) (E Z : α → ℕ) (R : ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : α) : retained p E Z R x ≤ p x := by
  classical
  unfold retained
  split_ifs <;> simp_all

theorem retained_joint_le (p : α → ℝ) (E Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hR : 0 ≤ R) (e z : ℕ) :
    colorMass (retained p E Z R) E Z e z ≤
      R * fiberMass p E e * colorMass p (fun _ => 0) Z 0 z := by
  classical
  by_cases h : colorMass p E Z e z ≤
      R * fiberMass p E e * colorMass p (fun _ => 0) Z 0 z
  · exact (Finset.sum_le_sum (fun x _ => retained_le p E Z R hp x)).trans h
  · have hzero : colorMass (retained p E Z R) E Z e z = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨_, hEx, hZx⟩ := Finset.mem_filter.mp hx
      simp only [retained, hEx, hZx, ite_eq_right h]
    rw [hzero]
    exact mul_nonneg (mul_nonneg hR (fiberMass_nonneg p E hp e))
      (colorMass_nonneg p (fun _ => 0) Z hp 0 z)

theorem constant_posterior (p : α → ℝ) (Z : α → ℕ) (hp1 : ∑ x, p x = 1) (x : α) :
    posterior p (fun _ => 0) Z x = colorMass p (fun _ => 0) Z 0 (Z x) := by
  classical
  simp [posterior, fiberMass, hp1]

/-- Positive atoms removed by the joint-ceiling truncation have a large
posterior likelihood ratio in the unchanged reference probability law. -/
theorem removed_log_gain (p : α → ℝ) (E Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hR : 0 < R)
    (x : α) (hx : retained p E Z R x < p x) :
    Real.log R < max 0 (Real.log (posterior p E Z x / posterior p (fun _ => 0) Z x)) := by
  classical
  have hpx : 0 < p x := lt_of_le_of_lt (retained_nonneg p E Z R hp x) hx
  have hbad : R * fiberMass p E (E x) * colorMass p (fun _ => 0) Z 0 (Z x) <
      colorMass p E Z (E x) (Z x) := by
    by_contra! hgood
    have hself : p x < p x := by simpa only [retained, ite_eq_left hgood] using hx
    exact lt_irrefl _ hself
  have hf : 0 < fiberMass p E (E x) := hpx.trans_le
    ((self_le_colorMass p E Z hp x).trans (colorMass_le_fiberMass p E Z hp _ _))
  have hq := posterior_pos p (fun _ => 0) Z hp x hpx
  have hmul : R * posterior p (fun _ => 0) Z x < posterior p E Z x := by
    rw [constant_posterior p Z hp1 x]
    apply (lt_div_iff₀ hf).2
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hbad
  have hratio : R < posterior p E Z x / posterior p (fun _ => 0) Z x :=
    (lt_div_iff₀ hq).2 hmul
  exact (Real.log_lt_log hR hratio).trans_le (le_max_right _ _)

/-- Finite reference-law likelihood truncation. The loss is charged to
the entropy increment with the original parent probabilities. -/
theorem removed_mass_le (p : α → ℝ) (E Z : α → ℕ) {R : ℝ}
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hR : 1 < R) :
    (∑ x, (p x - retained p E Z R x)) ≤
      (entropy p (fun _ => 0) Z - entropy p E Z + 1) / Real.log R := by
  classical
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hpoint (x : α) :
      (p x - retained p E Z R x) * Real.log R ≤
        p x * max 0 (Real.log (posterior p E Z x / posterior p (fun _ => 0) Z x)) := by
    by_cases hx : retained p E Z R x = p x
    · rw [hx, sub_self, zero_mul]
      exact mul_nonneg (hp x) (le_max_left _ _)
    · have hlt := lt_of_le_of_ne (retained_le p E Z R hp x) hx
      have hzero : retained p E Z R x = 0 := by
        by_cases h : colorMass p E Z (E x) (Z x) ≤
            R * fiberMass p E (E x) * colorMass p (fun _ => 0) Z 0 (Z x)
        · exact False.elim (hx (by simp only [retained, ite_eq_left h]))
        · simp only [retained, ite_eq_right h]
      rw [hzero, sub_zero]
      exact mul_le_mul_of_nonneg_left (removed_log_gain p E Z hp hp1 (by linarith) x hlt).le (hp x)
  apply (le_div_iff₀ hlog).2
  calc
    (∑ x, (p x - retained p E Z R x)) * Real.log R =
        ∑ x, (p x - retained p E Z R x) * Real.log R := by rw [Finset.sum_mul]
    _ ≤ ∑ x, p x * max 0
        (Real.log (posterior p E Z x / posterior p (fun _ => 0) Z x)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ ≤ entropy p (fun _ => 0) Z - entropy p E Z + 1 :=
      positive_log_window_le p (fun _ => 0) E Z hp hp1 (fun _ _ _ => rfl)

/-- Sum the truncation losses against the unchanged parent mixture. -/
theorem mixture_removed_mass_le {β : Type*} [Fintype β]
    (weight : β → ℝ) (p : β → α → ℝ) (E Z : β → α → ℕ) {R : ℝ}
    (hweight : ∀ a, 0 ≤ weight a) (hweight1 : ∑ a, weight a = 1)
    (hp : ∀ a x, 0 ≤ p a x) (hp1 : ∀ a, ∑ x, p a x = 1) (hR : 1 < R) :
    (∑ a, weight a * (∑ x, (p a x - retained (p a) (E a) (Z a) R x))) ≤
      ((∑ a, weight a * (entropy (p a) (fun _ => 0) (Z a) -
        entropy (p a) (E a) (Z a))) + 1) / Real.log R := by
  calc
    _ ≤ ∑ a, weight a * ((entropy (p a) (fun _ => 0) (Z a) -
        entropy (p a) (E a) (Z a) + 1) / Real.log R) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (removed_mass_le (p a) (E a) (Z a) (hp a) (hp1 a) hR) (hweight a))
    _ = _ := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hweight1]

/-- Conditioning a later restriction uses a lower bound relative to the
predeletion state mass, and keeps the palette of the reference law. -/
theorem conditional_palette_le {joint reference palette current K L : ℝ}
    (hcurrent : 0 < current) (hK : 0 ≤ K) (hL : 0 < L) (hpalette : 0 ≤ palette)
    (hjoint : joint ≤ K * reference * palette) (hfloor : reference / L ≤ current) :
    joint / current ≤ K * L * palette := by
  apply (div_le_iff₀ hcurrent).2
  have href : reference ≤ current * L := (div_le_iff₀ hL).1 hfloor
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left href hK) hpalette
  nlinarith only [hjoint, hmul]

/-- Light current states are deleted against the fixed old state masses.
Their budget is independent of how the later restriction was chosen. -/
theorem light_state_mass_le (reference current : α → ℝ)
    (href : ∀ x, 0 ≤ reference x)
    (href1 : ∑ x, reference x ≤ 1) {L : ℝ} (hL : 0 < L) :
    (∑ x, if current x < reference x / L then current x else 0) ≤ 1 / L := by
  classical
  calc
    _ ≤ ∑ x, reference x / L := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · exact hx.le
      · exact div_nonneg (href x) hL.le
    _ = (∑ x, reference x) / L := (Finset.sum_div _ _ _).symm
    _ ≤ 1 / L := div_le_div_of_nonneg_right href1 hL.le

/-- Appending at most `card β` possibilities to an old state multiplies
the light-denominator deletion budget by only that finite ambiguity. -/
theorem appended_state_light_mass_le {β : Type*} [Fintype β]
    (reference : α → ℝ) (current : α → β → ℝ)
    (href : ∀ x, 0 ≤ reference x) (href1 : ∑ x, reference x ≤ 1)
    {L : ℝ} (hL : 0 < L) :
    (∑ x, ∑ y, if current x y < reference x / L then current x y else 0) ≤
      (Fintype.card β : ℝ) / L := by
  classical
  calc
    _ ≤ ∑ x : α, ∑ _y : β, reference x / L := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hxy
      · exact hxy.le
      · exact div_nonneg (href x) hL.le
    _ = (Fintype.card β : ℝ) * (∑ x, reference x) / L := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_div, mul_div_assoc]
    _ ≤ (Fintype.card β : ℝ) / L := by
      have hc : (0 : ℝ) ≤ Fintype.card β := Nat.cast_nonneg _
      have hm := mul_le_mul_of_nonneg_left href1 hc
      simpa only [mul_one] using div_le_div_of_nonneg_right hm hL.le

/-- A logarithmically negligible information budget admits a subpower
likelihood cutoff whose deleted-mass bound tends to zero. -/
theorem exists_subpower_cutoff (N cost : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hcost : ∀ k, 0 < cost k)
    (hratio : Filter.Tendsto (fun k => cost k / Real.log (N k))
      Filter.atTop (nhds 0)) :
    ∃ R : ℕ → ℝ, (∀ k, 1 < R k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, R k ≤ N k ^ ε) ∧
      Filter.Tendsto (fun k => cost k / Real.log (R k)) Filter.atTop (nhds 0) := by
  let q := fun k => cost k / Real.log (N k)
  let t := fun k => Real.sqrt (q k)
  let R := fun k => N k ^ t k
  have hN1 (k : ℕ) : 1 < N k := by linarith [hN k]
  have hlog (k : ℕ) : 0 < Real.log (N k) := Real.log_pos (hN1 k)
  have hq (k : ℕ) : 0 < q k := div_pos (hcost k) (hlog k)
  have ht (k : ℕ) : 0 < t k := Real.sqrt_pos.2 (hq k)
  have htlim : Filter.Tendsto t Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  refine ⟨R, fun k => Real.one_lt_rpow (hN1 k) (ht k), ?_, ?_⟩
  · intro ε hε
    filter_upwards [htlim.eventually (Iio_mem_nhds hε)] with k hk
    exact Real.rpow_le_rpow_of_exponent_le (hN1 k).le hk.le
  · apply htlim.congr
    intro k
    have hlogR : Real.log (R k) = t k * Real.log (N k) :=
      Real.log_rpow (by linarith [hN k]) _
    rw [hlogR]
    symm
    apply (div_eq_iff (mul_ne_zero (ht k).ne' (hlog k).ne')).2
    have hsquare : t k ^ 2 = q k := Real.sq_sqrt (hq k).le
    calc
      cost k = q k * Real.log (N k) := by
        dsimp [q]
        exact (div_mul_cancel₀ _ (hlog k).ne').symm
      _ = t k * (t k * Real.log (N k)) := by rw [← hsquare]; ring

end

end PaletteTruncation

end Submission.Obl.k4_scalar_guarded_tangent_preparation
