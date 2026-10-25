-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.GridCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/GridCounts.lean (758215d).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Profiles
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.UniformFibers

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
open WangZahlLot.Obl.wz_tower_balanced_refinement
open scoped BigOperators Classical

/-- A Euclidean ball meets only a bounded number of grid squares. -/
theorem cell_count_ball (Q : Finset E2) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (x : E2) (hQ : ∀ q ∈ Q, dist q x ≤ θ) :
    ((Q.image (cellOf σ)).card : ℝ) ≤ (2 * θ / σ + 2) ^ 2 := by
  let I (i : Fin 2) := Finset.Icc ⌊(x i - θ) / σ⌋ ⌊(x i - θ + 2 * θ) / σ⌋
  have hsub : Q.image (cellOf σ) ⊆ I 0 ×ˢ I 1 := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    have hcoord (i : Fin 2) : |q i - x i| ≤ θ := by
      have hh := PiLp.norm_apply_le (q - x) i
      change |q i - x i| ≤ ‖q - x‖ at hh
      exact hh.trans (by simpa only [dist_eq_norm] using hQ q hq)
    have hi (i : Fin 2) : ⌊q i / σ⌋ ∈ I i := by
      apply Finset.mem_Icc.mpr
      constructor
      · apply Int.floor_le_floor
        apply div_le_div_of_nonneg_right _ hσ.le
        linarith [(abs_le.mp (hcoord i)).1]
      · apply Int.floor_le_floor
        apply div_le_div_of_nonneg_right _ hσ.le
        linarith [(abs_le.mp (hcoord i)).2]
    exact Finset.mem_product.mpr ⟨hi 0, hi 1⟩
  have hi (i : Fin 2) : ((I i).card : ℝ) ≤ 2 * θ / σ + 2 :=
    floor_range_card hσ (by positivity : 0 < 2 * θ)
  calc
    ((Q.image (cellOf σ)).card : ℝ) ≤ ((I 0 ×ˢ I 1).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ((I 0).card : ℝ) * (I 1).card := by rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (2 * θ / σ + 2) * (2 * θ / σ + 2) :=
      mul_le_mul (hi 0) (hi 1) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- A subset of a balanced family is controlled by the number of partition
fibers it meets. It need not itself be a union of those fibers. -/
theorem subset_mass_mul_image_le {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P Q : Finset X) (hQP : Q ⊆ P) (f : X → Y) {K : ℝ} (hK : 0 ≤ K)
    (hbal : Balanced P f K) :
    (Q.card : ℝ) * (P.image f).card ≤ K * P.card * (Q.image f).card := by
  have hsum : (Q.card : ℝ) = ∑ y ∈ Q.image f, ((Q.filter fun q => f q = y).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f Q
  rw [hsum, Finset.sum_mul]
  calc
    _ ≤ ∑ _y ∈ Q.image f, K * (P.card : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      have hc : ((Q.filter fun a => f a = f q).card : ℝ) ≤ (leafFiber P f q).card := by
        exact_mod_cast Finset.card_le_card (show (Q.filter fun a => f a = f q) ⊆ leafFiber P f q from
          fun a ha => mem_leafFiber'.mpr ⟨hQP (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩)
      have hb := (WangZahlLot.Obl.wz_normalized_projection_coarse_fine.balanced_fiber_card_bounds
        P f hbal (hQP hq)).1
      exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans (by nlinarith only [hb])
    _ = _ := by simp [mul_comm, mul_left_comm]

/-- Balance of spatial grid fibers turns ball-grid counting into normalized
point counts. The same theorem applies to the grid of unit normals. -/
theorem balanced_grid_ball_count (P : Finset E2) {σ θ K : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hK : 0 ≤ K)
    (hbal : Balanced P (cellOf σ) K) (x : E2) :
    (((P.filter fun q => dist q x ≤ θ).card : ℝ)) * (P.image (cellOf σ)).card ≤
      K * P.card * (2 * θ / σ + 2) ^ 2 := by
  let Q := P.filter fun q => dist q x ≤ θ
  have hmass := subset_mass_mul_image_le P Q (Finset.filter_subset _ _) (cellOf σ) hK hbal
  have hgrid := cell_count_ball Q hσ hθ x (fun q hq => (Finset.mem_filter.mp hq).2)
  exact hmass.trans (mul_le_mul_of_nonneg_left hgrid (mul_nonneg hK (Nat.cast_nonneg _)))

/-- Radius at most one grid step costs at most sixteen occupied cells. -/
theorem balanced_grid_cap (P : Finset E2) {σ θ K : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hθσ : θ ≤ σ) (hK : 0 ≤ K)
    (hbal : Balanced P (cellOf σ) K) (x : E2) :
    (((P.filter fun q => dist q x ≤ θ).card : ℝ)) * (P.image (cellOf σ)).card ≤
      16 * K * P.card := by
  have hratio : 2 * θ / σ ≤ 2 := by rw [div_le_iff₀ hσ]; linarith
  have hratio0 : 0 ≤ 2 * θ / σ := by positivity
  have hsquare : (2 * θ / σ + 2) ^ 2 ≤ 16 := by nlinarith
  have hh := balanced_grid_ball_count P hσ hθ hK hbal x
  calc
    _ ≤ K * P.card * (2 * θ / σ + 2) ^ 2 := hh
    _ ≤ K * P.card * 16 := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hK (Nat.cast_nonneg _))
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
