-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.SmallProjectionScalars.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.ScalarCollisionCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Collision

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Few separated scalars can simultaneously have small projections `A+tA`.
The near-coordinate contribution is absorbed using Frostman control of `A`;
all remaining collisions determine the scalar to accuracy `δ/q`. -/
theorem small_projection_scalar_count (A T : Finset ℝ) {δ q C σ K : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (hK : 0 < K)
    (hAne : A.Nonempty) (hAF : RealFiniteFrostman δ C σ A)
    (hAsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b)
    (hTsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ dist a b)
    (hbudget : 12 * K * C * q ^ σ ≤ 1)
    (hsmall : ∀ t ∈ T, ∃ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(A ×ˢ A) : Set (ℝ × ℝ))) cc ∧
        (m : ℝ) ≤ K * (A.card : ℝ)) :
    q * (T.card : ℝ) ≤ 12 * K * (A.card : ℝ) := by
  classical
  have hq : 0 < q := hδ.trans_le hδq
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hAne
  let R (t : T) (p : (A × A) × (A × A)) : Prop :=
    |(p.1.1 : ℝ) - p.2.1 + (t : ℝ) * ((p.1.2 : ℝ) - p.2.2)| ≤ 2 * δ
  let Near (p : (A × A) × (A × A)) : Prop := dist (p.1.2 : ℝ) p.2.2 ≤ q
  let E (t : T) : ℝ := (Finset.univ.filter (R t)).card
  have hrow (t : T) : (A.card : ℝ) ^ 3 ≤ K * E t := by
    obtain ⟨m, cc, hc, hm⟩ := hsmall t t.2
    let f (p : A × A) : ℝ := (p.1 : ℝ) + (t : ℝ) * (p.2 : ℝ)
    have hcov : Covers δ (Set.range f) cc := by
      rintro x ⟨p, rfl⟩
      exact hc ⟨((p.1 : ℝ), (p.2 : ℝ)), Finset.mem_product.mpr ⟨p.1.2, p.2.2⟩, rfl⟩
    have hcs := card_sq_le_cover_mul_closePairs f δ hcov
    have heq : closePairs f (2 * δ) = Finset.univ.filter (R t) := by
      ext p
      simp only [closePairs, Finset.mem_filter, Finset.mem_univ, true_and, R, f, Real.dist_eq]
      congr 2
      ring
    rw [heq, Fintype.card_prod, Fintype.card_coe] at hcs
    push_cast at hcs
    have hbound : ((A.card : ℝ) * (A.card : ℝ)) ^ 2 ≤ K * (A.card : ℝ) * E t :=
      hcs.trans (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))
    apply (mul_le_mul_iff_right₀ hAp).mp
    convert hbound using 1 <;> ring
  have hnear (t : T) : ((Finset.univ.filter (fun p => R t p ∧ Near p)).card : ℝ) ≤
      6 * C * q ^ σ * (A.card : ℝ) ^ 3 :=
    near_scalar_collision_count A hδ hδq hC hAF hAsep
  have hfar (p : (A × A) × (A × A)) (hp : ¬Near p) :
      ((Finset.univ.filter (fun t : T => R t p)).card : ℝ) ≤ 6 / q := by
    have hh := far_scalar_collision_count T hδ hq hq1 (le_of_not_ge hp) hTsep
      (a := (p.1.1 : ℝ)) (a' := (p.2.1 : ℝ))
    apply (le_div_iff₀ hq).mpr
    dsimp only [R]
    rw [finset_subtype_filter_card T (fun t : ℝ =>
      |(p.1.1 : ℝ) - p.2.1 + t * ((p.1.2 : ℝ) - p.2.2)| ≤ 2 * δ)]
    simpa only [mul_comm] using hh
  have htotal := relation_count_near_far R Near (by positivity : 0 ≤ 6 / q) hnear hfar
  simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul] at htotal
  have hlow : (T.card : ℝ) * (A.card : ℝ) ^ 3 ≤ K * ∑ t : T, E t := by
    calc
      (T.card : ℝ) * (A.card : ℝ) ^ 3 = ∑ _t : T, (A.card : ℝ) ^ 3 := by simp
      _ ≤ ∑ t : T, K * E t := Finset.sum_le_sum (fun t _ => hrow t)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hmix : (T.card : ℝ) * (A.card : ℝ) ^ 3 ≤
      (6 * K * C * q ^ σ) * ((T.card : ℝ) * (A.card : ℝ) ^ 3) +
        (6 * K / q) * (A.card : ℝ) ^ 4 := by
    apply hlow.trans
    have hh := mul_le_mul_of_nonneg_left htotal hK.le
    convert hh using 1 <;> ring
  have hsave : (6 * K * C * q ^ σ) * ((T.card : ℝ) * (A.card : ℝ) ^ 3) ≤
      ((T.card : ℝ) * (A.card : ℝ) ^ 3) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hbudget
      (by positivity : 0 ≤ (T.card : ℝ) * (A.card : ℝ) ^ 3)
    nlinarith only [hh]
  have hhalf : (T.card : ℝ) * (A.card : ℝ) ^ 3 ≤
      2 * ((6 * K / q) * (A.card : ℝ) ^ 4) := by linarith
  have hm := mul_le_mul_of_nonneg_right hhalf hq.le
  have hid : (2 * ((6 * K / q) * (A.card : ℝ) ^ 4)) * q = 12 * K * (A.card : ℝ) ^ 4 := by
    field_simp
    ring
  rw [hid] at hm
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < (A.card : ℝ) ^ 3)).mp
  convert hm using 1 <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
