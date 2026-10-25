import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Finset Finite
open Classical

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- The total mass of light atoms is bounded by their threshold times the
number of intervals and the total arm prior. -/
theorem sum_light_le [Fintype Ar] [Fintype Iv]
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (π : Bool → Ar → ℝ) (hπ : ∀ c a, 0 ≤ π c a)
    (lam : ℝ) (hlam : 0 ≤ lam) (c : Bool) :
    ∑ e, X.P e * (if X.heavy π lam e c then (0 : ℝ) else 1) ≤
      (Fintype.card Iv : ℝ) * lam * ∑ a, π c a := by
  have hgroup : ∑ e, X.P e * (if X.heavy π lam e c then (0 : ℝ) else 1) =
      ∑ k : Ar × Iv, fiberMass X.P (X.armKey c) k *
        (if π c k.1 * lam ≤ fiberMass X.P (X.armKey c) k then (0 : ℝ) else 1) := by
    rw [← sum_fiberwise (s := univ) (g := X.armKey c)]
    refine sum_congr rfl fun k _ => ?_
    unfold fiberMass
    rw [sum_mul]
    refine sum_congr rfl fun e he => ?_
    have hk := (mem_filter.mp he).2
    simp only [SwitchData.heavy, atomMass, hk]
    have ha : X.arm e c = k.1 := congrArg Prod.fst hk
    rw [ha]
    rfl
  rw [hgroup]
  calc
    ∑ k : Ar × Iv, fiberMass X.P (X.armKey c) k *
        (if π c k.1 * lam ≤ fiberMass X.P (X.armKey c) k then (0 : ℝ) else 1)
      ≤ ∑ k : Ar × Iv, π c k.1 * lam := by
        refine sum_le_sum fun k _ => ?_
        split_ifs with hk
        · simpa using mul_nonneg (hπ c k.1) hlam
        · simpa using (le_of_lt (lt_of_not_ge hk))
    _ = (Fintype.card Iv : ℝ) * lam * ∑ a, π c a := by
      rw [Fintype.sum_prod_type]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      rw [← mul_sum, ← sum_mul]
      ring

/-- A probability average bounded above has a positive-mass point with the
same upper bound. -/
theorem exists_pos_weight_le {α : Type*} [Fintype α] (P f : α → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hP1 : ∑ a, P a = 1) {t : ℝ}
    (havg : ∑ a, P a * f a ≤ t) : ∃ a, 0 < P a ∧ f a ≤ t := by
  by_contra! h
  have hex : ∃ a, 0 < P a := by
    by_contra! hzero
    have := sum_nonpos (s := (univ : Finset α)) (fun a _ => hzero a)
    linarith [hP1]
  obtain ⟨a, ha⟩ := hex
  have hstrict : ∑ a, P a * t < ∑ a, P a * f a := by
    refine sum_lt_sum (fun a _ => ?_) ⟨a, mem_univ a, ?_⟩
    · rcases (hP a).eq_or_lt with ha | ha
      · simp [← ha]
      · exact mul_le_mul_of_nonneg_left (h a ha).le ha.le
    · exact mul_lt_mul_of_pos_left (h a ha) ha
  rw [← sum_mul, hP1, one_mul] at hstrict
  linarith


/-- A finite positive combination of time counts has a single term realizing
its bound with the total available control mass. -/
theorem exists_large_term {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hf : ∀ a, 0 ≤ f a) {p C M : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hweight : ∑ a, w a ≤ M) (hlow : p ≤ C * ∑ a, w a * f a) :
    ∃ a, 0 < f a ∧ p ≤ C * M * f a := by
  haveI : Nonempty α := by
    by_contra h
    haveI : IsEmpty α := not_nonempty_iff.mp h
    simp at hlow
    linarith
  obtain ⟨a, ha, hmax⟩ := exists_max_image univ f univ_nonempty
  have hbound : ∑ b, w b * f b ≤ M * f a := by
    calc
      ∑ b, w b * f b ≤ ∑ b, w b * f a :=
        sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hmax b hb) (hw b)
      _ = (∑ b, w b) * f a := (sum_mul _ _ _).symm
      _ ≤ M * f a := mul_le_mul_of_nonneg_right hweight (hf a)
  have hlarge : p ≤ C * M * f a := by
    calc p ≤ C * ∑ b, w b * f b := hlow
      _ ≤ C * (M * f a) := mul_le_mul_of_nonneg_left hbound hC
      _ = C * M * f a := (mul_assoc _ _ _).symm
  refine ⟨a, ?_, hlarge⟩
  by_contra! hzero
  have : C * M * f a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC hM) hzero
  linarith

/-- Changing the controls leaves the failure bound unchanged. -/
theorem failBound_with_controls (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (ψ : Pal → Sc → Bool → ℝ) (π : Bool → Ar → ℝ) (lam s : ℝ) (n : ℕ) (e : Ω) :
    ({ X with Ψ := ψ } : SwitchData Ω Sf Sc Ar Iv Pal Tc).failBound π lam s n e =
      X.failBound π lam s n e := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
    simp only [SwitchData.failBound, ih]
    rfl

/-- One of two controls separated by `2 r` is at distance at least `r`
from any preceding control. -/
theorem exists_separated_color (u : Bool → ℝ) (v r : ℝ)
    (hsep : 2 * r ≤ |u true - u false|) : ∃ c, r ≤ |u c - v| := by
  by_cases h : r ≤ |u true - v|
  · exact ⟨true, h⟩
  · refine ⟨false, ?_⟩
    have ht : |u true - u false| ≤ |u true - v| + |u false - v| :=
      abs_sub_le (u true) v (u false) |>.trans_eq (by rw [abs_sub_comm v (u false)])
    linarith

end Submission.Obl.k4_matching_abstract_switching_mixture
