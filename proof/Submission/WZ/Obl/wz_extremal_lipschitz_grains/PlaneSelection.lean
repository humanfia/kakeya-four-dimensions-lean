-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.PlaneSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open scoped Matrix Classical

noncomputable def cross (u v : Space) : Space :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

theorem inner_cross_left (u v : Space) : inner ℝ u (cross u v) = 0 := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]
  rw [dotProduct_comm]
  exact dot_self_cross _ _

theorem inner_cross_right (u v : Space) : inner ℝ v (cross u v) = 0 := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]
  rw [dotProduct_comm]
  exact dot_cross_self _ _

theorem cross_norm_sq (u v : Space) :
    ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 := by
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), cross,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, RCLike.re_to_real]
  rw [cross_dot_cross, dotProduct_comm (WithLp.ofLp u) (WithLp.ofLp v)]
  ring

/-- Separation of unoriented unit directions gives a lower bound for their cross product. -/
theorem cross_norm_lower {u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {b : ℝ} (hb : 0 ≤ b) (hsep : b ≤ min ‖u - v‖ ‖u + v‖) :
    b / 2 ≤ ‖cross u v‖ := by
  have hsub := (sq_le_sq₀ hb (norm_nonneg (u - v))).mpr (hsep.trans (min_le_left _ _))
  have hadd := (sq_le_sq₀ hb (norm_nonneg (u + v))).mpr (hsep.trans (min_le_right _ _))
  rw [norm_sub_sq_real, hu, hv] at hsub
  rw [norm_add_sq_real, hu, hv] at hadd
  have hc := cross_norm_sq u v
  rw [hu, hv] at hc
  have hip := abs_real_inner_le_norm u v
  rw [hu, hv, one_mul, abs_le] at hip
  have hsquare : b ^ 2 ≤ 2 * ‖cross u v‖ ^ 2 := by
    rcases le_total 0 (inner ℝ u v) with ht | ht
    · nlinarith [mul_nonneg ht (sub_nonneg.mpr hip.2)]
    · nlinarith [mul_nonneg (neg_nonneg.mpr ht) (by linarith : 0 ≤ 1 + inner ℝ u v)]
  nlinarith [norm_nonneg (cross u v), sq_nonneg (‖cross u v‖ - b / 2)]

/-- The usual unoriented angular nonconcentration condition supplies many transverse pairs. -/
theorem transverse_pair_count {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → Space) (hv : ∀ i ∈ s, ‖v i‖ = 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hcap : ∀ i ∈ s,
      ((s.filter fun j => min ‖v i - v j‖ ‖v i + v j‖ < b).card : ℝ) ≤ (s.card : ℝ) / 2) :
    (s.card : ℝ) ^ 2 ≤
      2 * (((s.product s).filter fun ij => b / 2 ≤ ‖cross (v ij.1) (v ij.2)‖).card : ℝ) := by
  let R : ι → ι → Prop := fun i j => b / 2 ≤ ‖cross (v i) (v j)‖
  have hrow : ∀ i ∈ s, (s.card : ℝ) / 2 ≤ ((s.filter (R i)).card : ℝ) := by
    intro i hi
    have hsub : (s.filter fun j => ¬ R i j) ⊆
        (s.filter fun j => min ‖v i - v j‖ ‖v i + v j‖ < b) := by
      intro j hj
      obtain ⟨hjs, hij⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hjs, ?_⟩
      by_contra hn
      exact hij (cross_norm_lower (hv i hi) (hv j hjs) hb (le_of_not_gt hn))
    have hcard : ((s.filter fun j => ¬ R i j).card : ℝ) ≤ (s.card : ℝ) / 2 := by
      apply le_trans _ (hcap i hi)
      exact_mod_cast Finset.card_le_card hsub
    have hsplit : ((s.filter (R i)).card : ℝ) +
        ((s.filter fun j => ¬ R i j).card : ℝ) = (s.card : ℝ) := by
      exact_mod_cast s.card_filter_add_card_filter_not (R i)
    linarith
  have heq : (((s.product s).filter fun ij => R ij.1 ij.2).card : ℝ) =
      ∑ i ∈ s, ((s.filter (R i)).card : ℝ) := by
    have heqNat : ((s.product s).filter fun ij => R ij.1 ij.2).card =
        ∑ i ∈ s, (s.filter (R i)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
        Finset.product_eq_sprod, Finset.sum_product]
    exact_mod_cast heqNat
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_const, nsmul_eq_mul, ← heq] at hsum
  change (s.card : ℝ) ^ 2 ≤ 2 * (((s.product s).filter fun ij => R ij.1 ij.2).card : ℝ)
  nlinarith

/-- Quantitative conversion of a scalar triple product estimate to a plane estimate. -/
theorem normalized_cross_bound {u v w : Space} {b τ : ℝ}
    (hb : 0 < b) (hbuv : b ≤ ‖cross u v‖)
    (hdet : |inner ℝ w (cross u v)| ≤ τ) :
    |inner ℝ w (‖cross u v‖⁻¹ • cross u v)| ≤ τ / b := by
  have hc : 0 < ‖cross u v‖ := hb.trans_le hbuv
  rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hc), ← div_eq_inv_mul]
  apply (div_le_div_of_nonneg_right hdet hc.le).trans
  exact div_le_div_of_nonneg_left ((abs_nonneg _).trans hdet) hb hbuv

/-- A finite collection with many transverse pairs and few large scalar triple products
has a half-sized subcollection near one plane. This is the finite selection step after
a multilinear estimate; the triple-product counting assumption is an explicit input. -/
theorem narrow_plane_selection {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → Space) (hs : s.Nonempty) {b τ : ℝ} (hb : 0 < b)
    (hpairs : (s.card : ℝ) ^ 2 ≤
      2 * (((s.product s).filter fun ij => b ≤ ‖cross (v ij.1) (v ij.2)‖).card : ℝ))
    (htriples : (∑ i ∈ s, ∑ j ∈ s,
      ((s.filter fun k => τ < |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ)) ≤
        (s.card : ℝ) ^ 3 / 4) :
    ∃ (F : Finset ι) (N : Space), F ⊆ s ∧ (s.card : ℝ) / 2 ≤ (F.card : ℝ) ∧
      ‖N‖ = 1 ∧ ∀ k ∈ F, |inner ℝ (v k) N| ≤ τ / b := by
  let G := (s.product s).filter fun ij => b ≤ ‖cross (v ij.1) (v ij.2)‖
  let bad : ι × ι → ℝ := fun ij =>
    ((s.filter fun k => τ < |inner ℝ (v k) (cross (v ij.1) (v ij.2))|).card : ℝ)
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hG : G.Nonempty := by
    by_contra hnG
    have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnG
    change (s.card : ℝ) ^ 2 ≤ 2 * (G.card : ℝ) at hpairs
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero] at hpairs
    nlinarith
  have hbad : ∑ ij ∈ G, bad ij ≤ (s.card : ℝ) ^ 3 / 4 := by
    calc
      ∑ ij ∈ G, bad ij ≤ ∑ ij ∈ s.product s, bad ij :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
      _ = ∑ i ∈ s, ∑ j ∈ s,
          ((s.filter fun k => τ < |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ) := by
        rw [Finset.product_eq_sprod, Finset.sum_product]
      _ ≤ _ := htriples
  have havg : ∑ ij ∈ G, bad ij ≤ ∑ _ ∈ G, (s.card : ℝ) / 2 := by
    apply hbad.trans
    rw [Finset.sum_const, nsmul_eq_mul]
    change (s.card : ℝ) ^ 2 ≤ 2 * (G.card : ℝ) at hpairs
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hpairs)]
  obtain ⟨⟨i, j⟩, hij, hgood⟩ := Finset.exists_le_of_sum_le hG havg
  have hnorm : b ≤ ‖cross (v i) (v j)‖ := (Finset.mem_filter.mp hij).2
  let F := s.filter fun k => |inner ℝ (v k) (cross (v i) (v j))| ≤ τ
  let N : Space := ‖cross (v i) (v j)‖⁻¹ • cross (v i) (v j)
  have hcard : (s.card : ℝ) / 2 ≤ (F.card : ℝ) := by
    have heq := s.card_filter_add_card_filter_not
      (fun k => τ < |inner ℝ (v k) (cross (v i) (v j))|)
    have heq' : bad (i, j) + (F.card : ℝ) = (s.card : ℝ) := by
      dsimp [bad, F]
      exact_mod_cast (by simpa only [not_lt] using heq)
    linarith
  refine ⟨F, N, Finset.filter_subset _ _, hcard, ?_, ?_⟩
  · exact norm_smul_inv_norm (norm_pos_iff.mp (hb.trans_le hnorm))
  · intro k hk
    exact normalized_cross_bound hb hnorm (Finset.mem_filter.mp hk).2

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
