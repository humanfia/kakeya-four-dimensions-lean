import Submission.Obl.k4_sign_projection.CauchyIndex

namespace Submission.Obl.k4_sign_projection

open Polynomial
open scoped BigOperators

/-- Variations of the signs at positive infinity. -/
noncomputable def sturmPlus (l : List (Polynomial ℝ)) : ℤ :=
  (l.map Polynomial.leadingCoeff).signVariations

/-- Variations of the signs at negative infinity. -/
noncomputable def sturmMinus (l : List (Polynomial ℝ)) : ℤ :=
  (l.map (fun p => (-1 : ℝ) ^ p.natDegree * p.leadingCoeff)).signVariations

private theorem two_change (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    2 * (if SignType.sign a = SignType.sign b then (0 : ℤ) else 1) =
      1 - zsign a * zsign b := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb <;>
    simp [sign_neg, sign_pos, zsign_of_neg, zsign_of_pos, *]

private theorem sturmPlus_cons (p q : Polynomial ℝ) (l : List (Polynomial ℝ))
    (hp : p ≠ 0) (hq : q ≠ 0) :
    sturmPlus (p :: q :: l) = sturmPlus (q :: l) +
      if SignType.sign p.leadingCoeff = SignType.sign q.leadingCoeff then 0 else 1 := by
  unfold sturmPlus
  simp only [List.map_cons]
  rw [List.signVariations_cons_cons_of_ne_zero _ (leadingCoeff_ne_zero.mpr hp)
    (leadingCoeff_ne_zero.mpr hq), Nat.cast_add]
  split_ifs <;> simp

private theorem sturmMinus_cons (p q : Polynomial ℝ) (l : List (Polynomial ℝ))
    (hp : p ≠ 0) (hq : q ≠ 0) :
    sturmMinus (p :: q :: l) = sturmMinus (q :: l) +
      if SignType.sign ((-1 : ℝ) ^ p.natDegree * p.leadingCoeff) =
        SignType.sign ((-1 : ℝ) ^ q.natDegree * q.leadingCoeff) then 0 else 1 := by
  unfold sturmMinus
  simp only [List.map_cons]
  rw [List.signVariations_cons_cons_of_ne_zero _
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hp))
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hq)), Nat.cast_add]
  split_ifs <;> simp

/-- The Sturm sequence computes twice the Cauchy index. -/
theorem cauchyIndex_sturm (p q : Polynomial ℝ) :
    cauchyIndex q p = 2 * (sturmMinus (sturmSeq p q) - sturmPlus (sturmSeq p q)) := by
  classical
  induction p, q using sturmSeq.induct
  next q => simp [sturmPlus, sturmMinus]
  next p q hp ih =>
    by_cases hq : q = 0
    · subst q
      simp [sturmSeq_zero_right, hp, sturmPlus, sturmMinus]
    have hc := cauchyIndex_rec p q
    have ht := two_change p.leadingCoeff q.leadingCoeff
      (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
    have hb := two_change ((-1 : ℝ) ^ p.natDegree * p.leadingCoeff)
      ((-1 : ℝ) ^ q.natDegree * q.leadingCoeff)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hp))
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hq))
    have hb' (r : Polynomial ℝ) :
        zsign ((-1 : ℝ) ^ r.natDegree * r.leadingCoeff) = botSign r := by
      rw [botSign_eq, zsign_mul, zsign_pow]
      simp [topSign]
    simp only [hb'] at hb
    change 2 * _ = 1 - topSign p * topSign q at ht
    rw [← topSign_mul] at ht
    rw [← botSign_mul] at hb
    have hplus := sturmPlus_cons p q (sturmSeq ((-p) % q) ((-q) % ((-p) % q))) hp hq
    have hminus := sturmMinus_cons p q (sturmSeq ((-p) % q) ((-q) % ((-p) % q))) hp hq
    rw [sturmSeq_cons hp]
    rw [sturmSeq_cons hq] at ih
    rw [sturmSeq_cons hq]
    omega

end Submission.Obl.k4_sign_projection
