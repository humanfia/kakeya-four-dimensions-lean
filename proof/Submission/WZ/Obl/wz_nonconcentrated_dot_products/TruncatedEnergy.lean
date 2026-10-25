-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.TruncatedEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.DiscreteEnergy
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SeparatedCore

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable def truncatedDistance (δ : ℝ) (x y : Plane) : ℝ := max δ (min 1 (dist x y))

theorem truncatedDistance_bounds {δ : ℝ} (hδ1 : δ ≤ 1) (x y : Plane) :
    δ ≤ truncatedDistance δ x y ∧ truncatedDistance δ x y ≤ 1 :=
  ⟨le_max_left _ _, max_le hδ1 (min_le_left _ _)⟩

theorem ClosedFiniteFrostman.filter_closedBall {δ C : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (x : Plane) (r : ℝ) (hr : δ ≤ r) :
    ((S.filter (fun y => dist y x ≤ r)).card : ℝ) ≤ C * r * (S.card : ℝ) := by
  have heq : (↑(S.filter (fun y => dist y x ≤ r)) : Set Plane) =
      (↑S : Set Plane) ∩ closedBall x r := by
    ext y
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, Metric.mem_closedBall]
  have h := hF x r hr
  rw [← heq, Set.ncard_coe_finset] at h
  exact h

theorem ClosedFiniteFrostman.truncated_count {δ C : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (hC : 1 ≤ C) (x : Plane)
    (r : ℝ) (hr : 0 < r) :
    ((Finset.univ.filter (fun y : S => truncatedDistance δ x y ≤ r)).card : ℝ) ≤
      C * (S.card : ℝ) * r := by
  classical
  let B : Finset S := Finset.univ.filter (fun y => truncatedDistance δ x y ≤ r)
  by_cases hδr : δ ≤ r
  · by_cases hr1 : r < 1
    · have hsub : B.image Subtype.val ⊆ S.filter (fun y => dist y x ≤ r) := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        have hz' : max δ (min 1 (dist x z)) ≤ r := (Finset.mem_filter.mp hz).2
        have hmin := (max_le_iff.mp hz').2
        have hd : dist x z ≤ r := (min_le_iff.mp hmin).resolve_left (not_le.mpr hr1)
        exact Finset.mem_filter.mpr ⟨z.property, by rwa [dist_comm]⟩
      have hcard : (B.card : ℝ) ≤ ((S.filter (fun y => dist y x ≤ r)).card : ℝ) := by
        have hc := Finset.card_le_card hsub
        rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
        exact_mod_cast hc
      exact hcard.trans ((hF.filter_closedBall x r hδr).trans_eq (by ring))
    · have hcard : (B.card : ℝ) ≤ (S.card : ℝ) := by
        have hc := Finset.card_le_card (Finset.filter_subset (fun y : S => truncatedDistance δ x y ≤ r) Finset.univ)
        simpa only [Finset.card_univ, Fintype.card_coe] using (show (B.card : ℝ) ≤ (Fintype.card S : ℝ) by exact_mod_cast hc)
      have hCr : 1 ≤ C * r := by
        nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hr1) (zero_le_one.trans hC)]
      calc (B.card : ℝ) ≤ (S.card : ℝ) := hcard
        _ ≤ C * (S.card : ℝ) * r := by nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  · have hB : B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh := (Finset.mem_filter.mp hy).2
      exact hδr ((le_max_left δ (min 1 (dist x y))).trans hh)
    change (B.card : ℝ) ≤ _
    rw [hB, Finset.card_empty, Nat.cast_zero]
    positivity

noncomputable def energyConstant (γ : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ (-γ) / (1 - (1 / 2 : ℝ) ^ (1 - γ))

theorem energyConstant_pos {γ : ℝ} (hγ : γ < 1) : 0 < energyConstant γ := by
  have hq : (1 / 2 : ℝ) ^ (1 - γ) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  exact div_pos (by positivity) (sub_pos.mpr hq)

/-- The truncated energy bound applies even to finite sets that are neither
separated nor contained in a fixed ball. -/
theorem ClosedFiniteFrostman.truncated_energy {δ C γ : ℝ} {S : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (x : Plane) :
    ∑ y : S, (truncatedDistance δ x y) ^ (-γ) ≤
      C * (S.card : ℝ) * energyConstant γ := by
  have h := sum_rpow_neg_le_of_count (fun y : S => truncatedDistance δ x y)
    (A := C * (S.card : ℝ)) (R := 1) (by positivity) (by norm_num) hγ hγ1
    (fun y => ⟨hδ.trans_le (truncatedDistance_bounds hδ1 x y).1,
      (truncatedDistance_bounds hδ1 x y).2⟩)
    (hF.truncated_count hC x)
  simpa only [mul_one, energyConstant, mul_div_assoc] using h

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
