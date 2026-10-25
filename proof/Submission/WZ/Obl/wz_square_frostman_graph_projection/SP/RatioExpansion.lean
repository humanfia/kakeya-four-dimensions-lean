-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RatioExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CommonNeighbors

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem ratio_gap_forces_small_difference {a a' b b' t ρ q : ℝ}
    (hρ : 0 ≤ ρ) (hq : 0 < q)
    (hgap : q ≤ |b - b'| → 2 * ρ / q < |t - (a - a') / (b' - b)|)
    (hclose : |(a + t * b) - (a' + t * b')| ≤ 2 * ρ) : |b - b'| < q := by
  by_contra h
  have hb : q ≤ |b - b'| := le_of_not_gt h
  have hbb : 0 < |b - b'| := hq.trans_le hb
  have hne : b - b' ≠ 0 := abs_pos.mp hbb
  have heq : t - (a - a') / (b' - b) = ((a + t * b) - (a' + t * b')) / (b - b') := by
    rw [show b' - b = -(b - b') by ring, div_neg]
    field_simp
    <;> ring
  have hh : |t - (a - a') / (b' - b)| ≤ 2 * ρ / q := by
    rw [heq, abs_div]
    exact div_le_div₀ (by positivity) hclose hq hb
  exact (not_lt_of_ge hh) (hgap hb)

theorem relation_card_le_supported_columns {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (D : Finset J) {A : ℝ}
    (hA : 0 ≤ A) (hsupport : ∀ i j, R i j → j ∈ D)
    (hrows : ∀ j, ((Finset.univ.filter (fun i => R i j)).card : ℝ) ≤ A) :
    ((Finset.univ.filter (fun p : I × J => R p.1 p.2)).card : ℝ) ≤ A * (D.card : ℝ) := by
  classical
  rw [← sum_relation_degree R]
  calc (∑ j : J, ((Finset.univ.filter (fun i => R i j)).card : ℝ)) ≤
      ∑ j : J, if j ∈ D then A else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hD : j ∈ D
        · simpa only [if_pos hD] using hrows j
        · rw [if_neg hD]
          have he : Finset.univ.filter (fun i => R i j) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro i hi
            exact hD (hsupport i j (Finset.mem_filter.mp hi).2)
          simp only [he, Finset.card_empty, Nat.cast_zero, le_refl]
    _ = A * (D.card : ℝ) := by simp [← Finset.sum_filter, mul_comm]

/-- A slope separated from all ratios with a large denominator expands a
Cartesian product. The bound records the local counting losses explicitly. -/
theorem ratio_gap_cover_bound {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ℝ) (g : J → ℝ) {t ρ q A B : ℝ}
    (hρ : 0 ≤ ρ) (hq : 0 < q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ z : ℝ, ((Finset.univ.filter (fun i => |f i - z| ≤ ρ)).card : ℝ) ≤ A)
    (hsecond : ∀ z : ℝ, ((Finset.univ.filter (fun j => |g j - z| ≤ q)).card : ℝ) ≤ B)
    (hgap : ∀ i i' j j', q ≤ |g j - g j'| →
      2 * ρ / q < |t - (f i - f i') / (g j' - g j)|) :
    ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers ρ (Set.range (fun p : I × J => f p.1 + t * g p.2)) cc →
        (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤ (m : ℝ) * (A * B) := by
  classical
  intro m cc hcover
  have hcover' : Covers ρ ((fun p : I × J => f p.1 + t * g p.2) ''
      (↑(Finset.univ : Finset (I × J)) : Set (I × J))) cc := by
    simpa only [Finset.coe_univ, Set.image_univ] using hcover
  have hbound (k : Fin m) : ((Finset.univ.filter (fun p : I × J =>
      dist (f p.1 + t * g p.2) (cc k) ≤ ρ)).card : ℝ) ≤ A * B := by
    let R (i : I) (j : J) : Prop := dist (f i + t * g j) (cc k) ≤ ρ
    let E := Finset.univ.filter (fun p : I × J => R p.1 p.2)
    change (E.card : ℝ) ≤ A * B
    by_cases hE : E.Nonempty
    · obtain ⟨p, hp⟩ := hE
      have hp' := (Finset.mem_filter.mp hp).2
      let D := Finset.univ.filter (fun j => |g j - g p.2| ≤ q)
      have hs (i : I) (j : J) (hij : R i j) : j ∈ D := by
        have hd : |(f i + t * g j) - (f p.1 + t * g p.2)| ≤ 2 * ρ := by
          have ht := dist_triangle (f i + t * g j) (cc k) (f p.1 + t * g p.2)
          rw [dist_comm (cc k) (f p.1 + t * g p.2)] at ht
          rw [Real.dist_eq] at ht
          linarith
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (ratio_gap_forces_small_difference hρ hq (hgap i p.1 j p.2) hd).le⟩
      have hr (j : J) : ((Finset.univ.filter (fun i => R i j)).card : ℝ) ≤ A := by
        have he : Finset.univ.filter (fun i => R i j) =
            Finset.univ.filter (fun i => |f i - (cc k - t * g j)| ≤ ρ) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, Real.dist_eq]
          congr 2
          ring
        rw [he]
        exact hfirst _
      have hc := relation_card_le_supported_columns R D hA hs hr
      exact hc.trans (mul_le_mul_of_nonneg_left (hsecond (g p.2)) hA)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hE, Finset.card_empty, Nat.cast_zero]
      positivity
  have hc := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound (Finset.univ : Finset (I × J))
    (fun p => f p.1 + t * g p.2) hcover' hbound
  simpa only [Finset.card_univ, Fintype.card_prod, Nat.cast_mul] using hc

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
