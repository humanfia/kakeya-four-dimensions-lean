-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_packet_counting_transfer.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_direction_density_transfer

namespace WangZahlLot.Obl.wz_affine_packet_counting_transfer

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

abbrev Ball : Set Space := ball (0 : Space) 1

abbrev ConvexCount (δ m : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ Q : Set Space, Convex ℝ Q →
    ENNReal.ofReal (({i | Tube δ (x i) (v i) ⊆ Q}.ncard : ℝ) * δ ^ 2) ≤
      ENNReal.ofReal m * volume Q

abbrev SlabCount (δ l : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ (u : Space) (a r : ℝ), ‖u‖ = 1 → 0 < r →
    ENNReal.ofReal ({i | Tube δ (x i) (v i) ⊆
      (Ball ∩ {p | |inner ℝ u p - a| ≤ r})}.ncard : ℝ) ≤
    ENNReal.ofReal (l * (n : ℝ)) * volume (Ball ∩ {p | |inner ℝ u p - a| ≤ r})

abbrev SlabCover : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : ℝ) (W : Set Space), 0 < s → Convex ℝ W → W ⊆ Ball →
    volume W ≤ ENNReal.ofReal s →
    (∃ x v : Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W) →
    ∃ (u : Space) (a r : ℝ), ‖u‖ = 1 ∧ 0 < r ∧
      W ⊆ (Ball ∩ {p | |inner ℝ u p - a| ≤ r}) ∧
      volume (Ball ∩ {p | |inner ℝ u p - a| ≤ r}) ≤ ENNReal.ofReal (C * s ^ (1/2 : ℝ))

abbrev Packing : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (W : Set Space), Convex ℝ W → W ⊆ Ball →
    (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ W) →
    (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1/2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) →
    ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (volume W) ^ 2

/-- Disjoint fibers count indices with their multiplicities. -/
theorem fiber_count {n N q : ℕ} (F : Fin N → Finset (Fin n))
    (hcard : ∀ a, (F a).card = q)
    (hdisj : ∀ a b, a ≠ b → Disjoint (F a) (F b))
    (S : Set (Fin N)) (A : Set (Fin n))
    (hsub : ∀ a ∈ S, ∀ i ∈ F a, i ∈ A) : S.ncard * q ≤ A.ncard := by
  classical
  let U := (Set.toFinite S).toFinset.biUnion F
  have hc : U.card = S.ncard * q := by
    rw [Finset.card_biUnion]
    · simp only [hcard, Finset.sum_const, nsmul_eq_mul]
      rw [Set.ncard_eq_toFinset_card S]
      simp
    · intro a ha b hb hab
      exact hdisj a b hab
  rw [← hc, ← Set.ncard_coe_finset U]
  apply Set.ncard_le_ncard _ (Set.toFinite A)
  intro i hi
  obtain ⟨a, ha, hi⟩ := Finset.mem_biUnion.mp hi
  exact hsub a (by simpa using ha) i hi

theorem convex_pullback (f : AffineEquiv ℝ Space Space) {Q : Set Space}
    (hQ : Convex ℝ Q) : Convex ℝ (f '' Q ∩ Ball) :=
  (hQ.affine_image f.toAffineMap).inter (convex_ball _ _)

theorem convex_tube (δ : ℝ) (x v : Space) : Convex ℝ (Tube δ x v) :=
  (convex_segment x (x + v)).thickening δ

/-- A fixed, deliberately loose upper bound for unit tubes. -/
theorem tube_volume_upper {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (z w : Space) (hw : ‖w‖ = 1) :
    volume (Tube ρ z w) ≤ ENNReal.ofReal (384 * ρ ^ 2) := by
  have hv := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    z w hw (T := Icc 0 1) Subset.rfl hρ (by norm_num : (0 : ℝ) ≤ 1)
    (fun s hs t ht => by rw [Real.dist_eq]; exact abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩)
  have he : (fun t : ℝ => z + t • w) '' Icc 0 1 = segment ℝ z (z + w) := by
    rw [segment_eq_image']
    simp
  rw [he] at hv
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [sq_nonneg ρ, mul_nonneg (sub_nonneg.mpr hρ1) (sq_nonneg ρ)]

theorem ball_volume_upper : volume Ball ≤ ENNReal.ofReal 16 := by
  rw [EuclideanSpace.volume_ball_fin_three]
  norm_num
  linarith [Real.pi_lt_four]

end WangZahlLot.Obl.wz_affine_packet_counting_transfer
