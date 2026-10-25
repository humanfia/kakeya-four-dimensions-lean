/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/WeightedInformation.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.ConditionalLikelihood

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Submission.Obl.k4_matching_palette_likelihood

noncomputable section

/-- A common reference path with its original weighted world marginals
has exactly the same information cost as the original unnormalized laws.
Zero-weight worlds contribute zero; no parent is reweighted after a mask. -/
theorem weighted_original_score_eq {α : Type*} [Fintype α] {w : ℕ}
    (p : α → ℝ) (F : α → Fin w) (E V : α → ℕ)
    (r : Fin w → α → ℝ) (ω : Fin w → ℝ) (mass : ℝ)
    (hp : ∀ x, 0 ≤ p x) (_hr : ∀ g x, 0 ≤ r g x) (hω : ∀ g, 0 ≤ ω g)
    (hmass : 0 < mass)
    (hnest : ∀ x y, E x = E y → F x = F y)
    (hworld : ∀ g x, ω g * r g x = if F x = g then mass * p x else 0) :
    (∑ g, ω g * ∑ x, r g x * max 0 (Real.log (originalLikelihood (r g) E V x))) =
      mass * positiveScore p (fun x => (F x).val) E V := by
  classical
  unfold positiveScore
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x = 0
  · rw [hx, zero_mul, mul_zero]
    apply Finset.sum_eq_zero
    intro g _
    have hz : ω g * r g x = 0 := by simpa only [hx, mul_zero, ite_self] using hworld g x
    calc
      _ = (ω g * r g x) * max 0 (Real.log (originalLikelihood (r g) E V x)) := by ring
      _ = 0 := by rw [hz, zero_mul]
  · rw [Finset.sum_eq_single (F x)]
    · have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
      have hprod : ω (F x) * r (F x) x = mass * p x := by
        simpa using hworld (F x) x
      have hωpos : 0 < ω (F x) := by
        by_contra! h
        have hz : ω (F x) = 0 := le_antisymm h (hω _)
        rw [hz, zero_mul] at hprod
        have := mul_pos hmass hpx
        linarith
      let F₀ := fun y => (F y).val
      let c := mass / ω (F x)
      have hc : 0 < c := div_pos hmass hωpos
      have hs : r (F x) = fun y => c * parentSlice p F₀ (F₀ x) y := by
        funext y
        have h := hworld (F x) y
        by_cases hF : F y = F x
        · have hval : F₀ y = F₀ x := congrArg Fin.val hF
          rw [ite_eq_left hF] at h
          rw [parentSlice, ite_eq_left hval]
          have hdiv : r (F x) y = (mass * p y) / ω (F x) :=
            (eq_div_iff hωpos.ne').2 (by simpa only [mul_comm] using h)
          rw [hdiv]
          dsimp only [c]
          ring
        · have hval : F₀ y ≠ F₀ x := fun h => hF (Fin.ext h)
          rw [ite_eq_right hF] at h
          have hz : r (F x) y = 0 := (mul_eq_zero.mp h).resolve_left hωpos.ne'
          rw [parentSlice, ite_eq_right hval, mul_zero, hz]
      have hslice : ∀ y, 0 ≤ parentSlice p F₀ (F₀ x) y := by
        intro y
        unfold parentSlice
        split_ifs
        · exact hp y
        · exact le_rfl
      have hslicepos : 0 < parentSlice p F₀ (F₀ x) x := by simpa [parentSlice] using hpx
      have hratio : originalLikelihood (r (F x)) E V x =
          posterior p E V x / posterior p F₀ V x := by
        rw [hs, originalLikelihood_const_mul (parentSlice p F₀ (F₀ x)) E V hslice hslicepos hc.ne']
        exact originalLikelihood_parentSlice p F₀ E V hp
          (fun y z h => congrArg Fin.val (hnest y z h)) hpx
      rw [hratio]
      calc
        _ = (ω (F x) * r (F x) x) * max 0 (Real.log (posterior p E V x / posterior p F₀ V x)) := by ring
        _ = _ := by rw [hprod]; ring
    · intro g _ hg
      have hz : ω g * r g x = 0 := by
        simpa only [ite_eq_right (Ne.symm hg)] using hworld g x
      calc
        _ = (ω g * r g x) * max 0 (Real.log (originalLikelihood (r g) E V x)) := by ring
        _ = 0 := by rw [hz, zero_mul]
    · intro h
      exact False.elim (h (Finset.mem_univ _))

/-- The global normalization is the unchanged original weighted mass. -/
theorem weighted_original_mass_eq {α : Type*} [Fintype α] {w : ℕ}
    (p : α → ℝ) (F : α → Fin w) (r : Fin w → α → ℝ) (ω : Fin w → ℝ) (mass : ℝ)
    (hp1 : ∑ x, p x = 1)
    (hworld : ∀ g x, ω g * r g x = if F x = g then mass * p x else 0) :
    (∑ g, ω g * ∑ x, r g x) = mass := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, mass * p x := by
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [hworld]
      simp
    _ = mass := by rw [← Finset.mul_sum, hp1, mul_one]

/-- The one common original probability chooses an actual parent whose
ORIGINAL weighted unnormalized likelihood budget has the same bound. -/
theorem exists_weighted_original_information_window
    (n L C M Kv Ks : ℕ) (p : Fin n → ℝ) (W : ℕ → ℕ)
    (F : (a : ℕ) → Fin n → Fin (W a)) (Z : Fin n → ℕ)
    (V A : ℕ → Fin n → ℕ)
    (r : (a : ℕ) → Fin (W a) → Fin n → ℝ)
    (ω : (a : ℕ) → Fin (W a) → ℝ) (mass : ℕ → ℝ)
    (hL : 0 < L) (hC : 1 ≤ C) (hM : 1 ≤ M) (hKv : 1 ≤ Kv) (hKs : 1 ≤ Ks)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hr : ∀ a < L, ∀ g x, 0 ≤ r a g x) (hω : ∀ a < L, ∀ g, 0 ≤ ω a g)
    (hmass : ∀ a < L, 0 < mass a)
    (hworld : ∀ a < L, ∀ g x, ω a g * r a g x =
      if F a x = g then mass a * p x else 0)
    (hnest : ∀ a x y, F (a + 1) x = F (a + 1) y → F a x = F a y)
    (hsupp : ∀ x, ((Finset.univ.filter (fun y =>
      0 < p y ∧ (F 0 y).val = (F 0 x).val)).image Z).card ≤ M)
    (hv : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      pairedRecord (fun z => (F a z).val) Z y =
        pairedRecord (fun z => (F a z).val) Z x)).image (V a)).card ≤ Kv)
    (hs : ∀ a < L, ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧
      (F (a + C) y).val = (F (a + C) x).val)).image (A a)).card ≤ Ks) :
    ∃ a : ℕ, a < L ∧
      (∑ g, ω a g * ∑ x, r a g x * max 0 (Real.log
        (originalLikelihood (r a g) (pairedRecord (fun z => (F (a + C) z).val) (A a)) (V a) x))) ≤
      ((∑ g, ω a g * ∑ x, r a g x) *
        ((C : ℝ) * Real.log (M : ℝ) / (L : ℝ) + Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 3)) := by
  let H := fun a x => (F a x).val
  have hn : ∀ a x y, H (a + 1) x = H (a + 1) y → H a x = H a y :=
    fun a x y h => congrArg Fin.val (hnest a x y (Fin.ext h))
  obtain ⟨a, ha, hscore⟩ := exists_low_information_extended_window
    n L C M Kv Ks p H Z V A hL hC hM hKv hKs hp hp1 hn hsupp hv hs
  have hnestA : ∀ x y, pairedRecord (H (a + C)) (A a) x =
      pairedRecord (H (a + C)) (A a) y → F a x = F a y := by
    intro x y h
    apply Fin.ext
    exact nested_record H hn a (a + C) (Nat.le_add_right a C) x y (Nat.pair_eq_pair.mp h).1
  refine ⟨a, ha, ?_⟩
  rw [weighted_original_mass_eq p (F a) (r a) (ω a) (mass a) hp1 (hworld a ha),
    weighted_original_score_eq p (F a) (pairedRecord (H (a + C)) (A a)) (V a)
      (r a) (ω a) (mass a) hp (hr a ha) (hω a ha) (hmass a ha) hnestA (hworld a ha)]
  exact mul_le_mul_of_nonneg_left hscore (hmass a ha).le

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
