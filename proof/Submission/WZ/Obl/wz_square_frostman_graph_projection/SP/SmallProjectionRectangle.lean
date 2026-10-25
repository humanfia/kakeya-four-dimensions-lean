-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.SmallProjectionRectangle.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit 7d51ba0; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphRealTransfer
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RobustProjectionNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise
attribute [local instance] Classical.propDecidable

/-- A small projection of a dense relation yields a large rectangle with
small full projection, with explicit power losses. -/
theorem small_projection_rectangle_of_ratio (A B : Finset ℝ) (R : A → B → Prop)
    {δ κ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hratio : (A.card : ℝ) ≤ δ ^ (-2 * κ) * (B.card : ℝ))
    (hR : δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤
      ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ))
    (ht : δ ^ (100 * κ) ≤ t) (ht1 : t ≤ 1)
    (hconst : 603979776 ≤ δ ^ (-κ))
    {m : ℕ} (cc : Fin m → ℝ)
    (hcover : Covers δ ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
      (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) cc)
    (hm : (m : ℝ) ≤ δ ^ (-κ) * (A.card : ℝ)) :
    ∃ X Y : Finset ℝ, X ⊆ A ∧ Y ⊆ B ∧ X.Nonempty ∧ Y.Nonempty ∧
      ((δ ^ κ) ^ 2 / 16) * (A.card : ℝ) ≤ (X.card : ℝ) ∧
      ((δ ^ κ) ^ 2 / 16) * (B.card : ℝ) ≤ (Y.card : ℝ) ∧
      RealCoverBound δ (X + realScalarImage t Y) (δ ^ (-114 * κ) * (A.card : ℝ)) := by
  have hd : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ _
  have hd1 : δ ^ κ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hκ.le
  obtain ⟨X, Y, hXA, hYB, hX, hY, hXsize, hYsize, htransfer⟩ :=
    graph_real_projection_transfer A B R hδ hd hd1 hA hB hAsep hBsep hR
  have hXsize' : ((δ ^ κ) ^ 2 / 16) * (A.card : ℝ) ≤ (X.card : ℝ) := by
    apply le_trans _ hXsize
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith [mul_self_le_mul_self hd.le hd1]
  have hc : 0 < δ ^ (100 * κ) := Real.rpow_pos_of_pos hδ _
  obtain ⟨n, centers, hcov, hcount⟩ := htransfer (δ ^ (100 * κ)) t hc ht ht1 m cc hcover
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  have hupper := graph_projection_bound hc hd hAp hBp (Nat.cast_nonneg X.card)
    (Real.rpow_pos_of_pos hδ (-κ)).le (Real.rpow_pos_of_pos hδ (-2 * κ)).le
    (Nat.cast_nonneg m) hXsize hratio hm hcount
  have hupper' : (n : ℝ) ≤ δ ^ (-114 * κ) * (X.card : ℝ) :=
    hupper.trans (mul_le_mul_of_nonneg_right (robust_projection_power_budget hδ hconst)
      (Nat.cast_nonneg _))
  refine ⟨X, Y, hXA, hYB, hX, hY, hXsize', hYsize, n, centers, ?_, ?_⟩
  · rwa [rectangular_projection_image] at hcov
  · exact hupper'.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card hXA) (Real.rpow_nonneg hδ.le _))

theorem small_projection_rectangle (A B : Finset ℝ) (R : A → B → Prop)
    {δ κ σ C t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ)
    (hCb : C ≤ δ ^ (-κ)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hBF : RealFiniteFrostman δ C σ B)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ dist x y)
    (hAc : (A.card : ℝ) ≤ δ ^ (-σ - κ))
    (hR : δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤
      ((Finset.univ.filter (fun p : A × B => R p.1 p.2)).card : ℝ))
    (ht : δ ^ (100 * κ) ≤ t) (ht1 : t ≤ 1)
    (hconst : 603979776 ≤ δ ^ (-κ))
    {m : ℕ} (cc : Fin m → ℝ)
    (hcover : Covers δ ((fun q : A × B => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
      (↑(Finset.univ.filter (fun q : A × B => R q.1 q.2)) : Set (A × B))) cc)
    (hm : (m : ℝ) ≤ δ ^ (-κ) * (A.card : ℝ)) :
    ∃ X Y : Finset ℝ, X ⊆ A ∧ Y ⊆ B ∧ X.Nonempty ∧ Y.Nonempty ∧
      ((δ ^ κ) ^ 2 / 16) * (A.card : ℝ) ≤ (X.card : ℝ) ∧
      ((δ ^ κ) ^ 2 / 16) * (B.card : ℝ) ≤ (Y.card : ℝ) ∧
      RealCoverBound δ (X + realScalarImage t Y) (δ ^ (-114 * κ) * (A.card : ℝ)) := by
  exact small_projection_rectangle_of_ratio A B R hδ hδ1 hκ hA hB hAsep hBsep
    (rectangular_card_ratio hδ hAc (hBF.card_power_lower hδ hB hCb)) hR ht ht1 hconst cc hcover hm

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
