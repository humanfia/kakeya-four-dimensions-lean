-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PowerFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PowerCountingEnergy

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- Finite normalized Frostman counting at an arbitrary positive exponent. -/
def ClosedFinitePowerFrostman (δ C s : ℝ) (S : Finset Plane) : Prop :=
  ∀ (x : Plane) (r : ℝ), δ ≤ r →
    ((S.filter (fun y => dist y x ≤ r)).card : ℝ) ≤ C * r ^ s * (S.card : ℝ)

theorem ClosedFinitePowerFrostman.truncated_count {δ C s : ℝ} {S : Finset Plane}
    (hF : ClosedFinitePowerFrostman δ C s S) (hC : 1 ≤ C) (hs : 0 ≤ s) (x : Plane)
    (r : ℝ) (hr : 0 < r) :
    ((Finset.univ.filter (fun y : S => truncatedDistance δ x y ≤ r)).card : ℝ) ≤
      C * (S.card : ℝ) * r ^ s := by
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
      exact hcard.trans ((hF x r hδr).trans_eq (by ring))
    · have hcard : (B.card : ℝ) ≤ (S.card : ℝ) := by
        have hc := Finset.card_le_card (Finset.filter_subset (fun y : S => truncatedDistance δ x y ≤ r) Finset.univ)
        simpa only [Finset.card_univ, Fintype.card_coe] using (show (B.card : ℝ) ≤ (Fintype.card S : ℝ) by exact_mod_cast hc)
      have hCr : 1 ≤ C * r ^ s := by
        have hh : 1 ≤ r ^ s := Real.one_le_rpow (le_of_not_gt hr1) hs
        nlinarith
      calc (B.card : ℝ) ≤ (S.card : ℝ) := hcard
        _ ≤ C * (S.card : ℝ) * r ^ s := by nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  · have hB : B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh := (Finset.mem_filter.mp hy).2
      exact hδr ((le_max_left δ (min 1 (dist x y))).trans hh)
    change (B.card : ℝ) ≤ _
    rw [hB, Finset.card_empty, Nat.cast_zero]
    positivity

theorem ClosedFinitePowerFrostman.truncated_energy {δ C s γ : ℝ} {S : Finset Plane}
    (hF : ClosedFinitePowerFrostman δ C s S) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hs : 0 < s) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (x : Plane) :
    ∑ y : S, (truncatedDistance δ x y) ^ (-(s * γ)) ≤
      C * (S.card : ℝ) * energyConstant γ := by
  exact sum_rpow_neg_mul_le_of_power_count (fun y : S => truncatedDistance δ x y)
    (by positivity) hs hγ hγ1
    (fun y => ⟨hδ.trans_le (truncatedDistance_bounds hδ1 x y).1,
      (truncatedDistance_bounds hδ1 x y).2⟩)
    (hF.truncated_count hC hs.le x)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
