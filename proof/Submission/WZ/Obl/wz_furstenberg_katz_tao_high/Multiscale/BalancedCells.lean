-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.BalancedCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.BalancedQuotients
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Geometry

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open WangZahlLot.Obl.wz_tower_balanced_refinement
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance] Classical.propDecidable

/-- A subset of a balanced family is bounded by the number of fibers it
meets, with the normalized original mass as its unit. -/
theorem balanced_subset_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S U : Finset α) (q : α → β) {K : ℝ}
    (hUS : U ⊆ S) (hbal : Balanced S q K) :
    ((S.image q).card : ℝ) * U.card ≤ K * S.card * (U.image q).card := by
  classical
  have hsub : U ⊆ S.filter (fun a => q a ∈ U.image q) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨hUS ha, Finset.mem_image_of_mem q ha⟩
  have heq : (S.image q).filter (fun b => b ∈ U.image q) = U.image q := by
    ext b
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hb => Finset.image_subset_image hUS hb)
  have hh := (balanced_image_filter_counts S q hbal (fun b => b ∈ U.image q)).2
  rw [heq] at hh
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
    (Nat.cast_nonneg _)).trans hh

/-- The square cell map used by the regularized configuration. -/
noncomputable def gridCell (Δ : ℝ) (p : E2) : ℤ × ℤ := (⌊p 0 / Δ⌋, ⌊p 1 / Δ⌋)

-- Adapted from workspace o157/x0675 High/Profiles.lean, floor_range_card.
/-- Floor labels of an interval cost at most its length plus two. -/
theorem floor_interval_card {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc ⌊a⌋ ⌊b⌋).card : ℝ) ≤ b - a + 2 := by
  have hmono : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  rw [Int.card_Icc]
  have hnn : (0 : ℤ) ≤ ⌊b⌋ + 1 - ⌊a⌋ := by omega
  have heq : (((⌊b⌋ + 1 - ⌊a⌋).toNat : ℕ) : ℝ) =
      ((⌊b⌋ + 1 - ⌊a⌋ : ℤ) : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnn
  rw [heq]
  push_cast
  linarith [Int.floor_le b, Int.lt_floor_add_one a]

/-- A Euclidean ball meets only the expected number of square-grid cells. -/
theorem gridCell_ball_card (P : Finset E2) (x : E2) {Δ ρ : ℝ}
    (hΔ : 0 < Δ) (hρ : 0 ≤ ρ) :
    (((P.filter (fun p => dist p x ≤ ρ)).image (gridCell Δ)).card : ℝ) ≤
      (2 * ρ / Δ + 2) ^ 2 := by
  classical
  let I (i : Fin 2) := Finset.Icc ⌊(x i - ρ) / Δ⌋ ⌊(x i + ρ) / Δ⌋
  have hsub : (P.filter (fun p => dist p x ≤ ρ)).image (gridCell Δ) ⊆ I 0 ×ˢ I 1 := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    have hpρ := (Finset.mem_filter.mp hp).2
    have hcoord : ∀ i : Fin 2, x i - ρ ≤ p i ∧ p i ≤ x i + ρ := by
      intro i
      have hh := PiLp.norm_apply_le (p - x) i
      simp only [PiLp.sub_apply, Real.norm_eq_abs] at hh
      have hdist : ‖p - x‖ ≤ ρ := by simpa only [dist_eq_norm] using hpρ
      have habs : |p i - x i| ≤ ρ := hh.trans hdist
      constructor <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr
    · exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (hcoord 0).1 hΔ.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (hcoord 0).2 hΔ.le)⟩
    · exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right (hcoord 1).1 hΔ.le),
        Int.floor_le_floor (div_le_div_of_nonneg_right (hcoord 1).2 hΔ.le)⟩
  have hI : ∀ i : Fin 2, ((I i).card : ℝ) ≤ 2 * ρ / Δ + 2 := by
    intro i
    have hh := floor_interval_card (show (x i - ρ) / Δ ≤ (x i + ρ) / Δ by gcongr; linarith)
    convert hh using 1 <;> dsimp [I] <;> ring
  calc
    _ ≤ ((I 0 ×ˢ I 1).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = ((I 0).card : ℝ) * (I 1).card := by rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (2 * ρ / Δ + 2) * (2 * ρ / Δ + 2) :=
      mul_le_mul (hI 0) (hI 1) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Balance converts the number of occupied grid cells into an upper
bound on every point-ball count. This is the point-profile energy input. -/
theorem balanced_grid_ball_count (P : Finset E2) (hP : P.Nonempty) (x : E2)
    {Δ ρ K : ℝ} (hΔ : 0 < Δ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (hbal : Balanced P (gridCell Δ) K) :
    ((P.filter (fun p => dist p x ≤ ρ)).card : ℝ) ≤
      K * (2 * ρ / Δ + 2) ^ 2 * P.card / (P.image (gridCell Δ)).card := by
  have hpos : (0 : ℝ) < (P.image (gridCell Δ)).card :=
    Nat.cast_pos.mpr (hP.image _).card_pos
  rw [le_div_iff₀ hpos, mul_comm]
  have hh := balanced_subset_card_le P (P.filter (fun p => dist p x ≤ ρ)) (gridCell Δ)
    (Finset.filter_subset _ _) hbal
  calc
    _ ≤ K * P.card * ((P.filter (fun p => dist p x ≤ ρ)).image (gridCell Δ)).card := hh
    _ ≤ K * P.card * (2 * ρ / Δ + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (gridCell_ball_card P x hΔ hρ) (by positivity)
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
