-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarCollisionCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealSeparatedCounts
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.NearFarCounting
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RatioGapFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem collision_card_by_second_coordinates {I : Type*} [Fintype I]
    (R : I → I → I → I → Prop) :
    ((Finset.univ.filter (fun p : (I × I) × (I × I) => R p.1.1 p.1.2 p.2.1 p.2.2)).card : ℝ) =
      ∑ b : I, ∑ b' : I, ∑ a : I, ((Finset.univ.filter (fun a' => R a b a' b')).card : ℝ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑ a : I, ∑ a' : I, ∑ b' : I, if R a b a' b' then (1 : ℝ) else 0) =
        ∑ a : I, ∑ b' : I, ∑ a' : I, if R a b a' b' then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- Collisions with nearby second coordinates contribute only a small
fraction of the cubic energy. -/
theorem near_scalar_collision_count (A : Finset ℝ) {δ C σ q t : ℝ}
    (hδ : 0 < δ) (hδq : δ ≤ q) (hC : 0 ≤ C)
    (hAF : RealFiniteFrostman δ C σ A)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ dist a b) :
    ((Finset.univ.filter (fun p : (A × A) × (A × A) =>
      |(p.1.1 : ℝ) - p.2.1 + t * ((p.1.2 : ℝ) - p.2.2)| ≤ 2 * δ ∧
        dist (p.1.2 : ℝ) p.2.2 ≤ q)).card : ℝ) ≤
      6 * C * q ^ σ * (A.card : ℝ) ^ 3 := by
  classical
  have hq : 0 < q := hδ.trans_le hδq
  have hlocal (b b' a : A) :
      ((Finset.univ.filter (fun a' : A =>
        |(a : ℝ) - a' + t * ((b : ℝ) - b')| ≤ 2 * δ ∧ dist (b : ℝ) b' ≤ q)).card : ℝ) ≤
      if dist (b : ℝ) b' ≤ q then 6 else 0 := by
    by_cases hn : dist (b : ℝ) b' ≤ q
    · simp only [hn, and_true, ite_true]
      rw [finset_subtype_filter_card A (fun x : ℝ => |(a : ℝ) - x + t * ((b : ℝ) - b')| ≤ 2 * δ)]
      apply real_separated_two_radius_card hδ _
        (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2
      have hid : dist x ((a : ℝ) + t * ((b : ℝ) - b')) =
          |(a : ℝ) - x + t * ((b : ℝ) - b')| := by
        rw [Real.dist_eq, abs_sub_comm]
        congr 1
        ring
      rw [hid]
      exact hh
    · simp only [hn, and_false, ite_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero, le_refl]
  have hrow (b : A) : (∑ b' : A, ∑ a : A,
      ((Finset.univ.filter (fun a' : A =>
        |(a : ℝ) - a' + t * ((b : ℝ) - b')| ≤ 2 * δ ∧ dist (b : ℝ) b' ≤ q)).card : ℝ)) ≤
      6 * C * q ^ σ * (A.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ b' : A, ∑ _a : A, if dist (b : ℝ) b' ≤ q then (6 : ℝ) else 0 :=
        Finset.sum_le_sum (fun b' _ => Finset.sum_le_sum (fun a _ => hlocal b b' a))
      _ = ((Finset.univ.filter (fun b' : A => dist (b : ℝ) b' ≤ q)).card : ℝ) * (6 * (A.card : ℝ)) := by
        simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (C * q ^ σ * (A.card : ℝ)) * (6 * (A.card : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [finset_subtype_filter_card A (fun x : ℝ => dist (b : ℝ) x ≤ q)]
        simpa only [dist_comm] using hAF (b : ℝ) q hδq
      _ = _ := by ring
  calc
    _ = ∑ b : A, ∑ b' : A, ∑ a : A,
        ((Finset.univ.filter (fun a' : A =>
          |(a : ℝ) - a' + t * ((b : ℝ) - b')| ≤ 2 * δ ∧ dist (b : ℝ) b' ≤ q)).card : ℝ) := by
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
        (collision_card_by_second_coordinates (fun a b a' b' : A =>
          |(a : ℝ) - a' + t * ((b : ℝ) - b')| ≤ 2 * δ ∧ dist (b : ℝ) b' ≤ q))
    _ ≤ ∑ _b : A, 6 * C * q ^ σ * (A.card : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun b _ => hrow b)
    _ = _ := by simp; ring

/-- Far-coordinate collisions determine the scalar up to a short interval. -/
theorem far_scalar_collision_count (T : Finset ℝ) {δ q a b a' b' : ℝ}
    (hδ : 0 < δ) (hq : 0 < q) (hq1 : q ≤ 1) (hfar : q ≤ dist b b')
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y) :
    q * ((T.filter (fun t => |a - a' + t * (b - b')| ≤ 2 * δ)).card : ℝ) ≤ 6 := by
  apply real_separated_affine_window hδ hq hq1
    (a := b - b') (b := a - a') (by simpa only [Real.dist_eq] using hfar) _
    (fun x hx y hy hne => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne)
  intro x hx
  simpa only [mul_comm, add_comm] using (Finset.mem_filter.mp hx).2

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
