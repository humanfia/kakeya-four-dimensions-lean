-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Strips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Counting line nonconcentration relative to a strip of width `w`. -/
def StripFrostman (δ K ζ w : ℝ) (S : Finset Plane) : Prop := by
  classical
  exact ∀ (n : Plane) (c r : ℝ), ‖n‖ = 1 → δ ≤ r →
    ((S.filter (fun x => |inner ℝ x n - c| < r)).card : ℝ) ≤ K * (r / w) ^ ζ * (S.card : ℝ)

theorem ClosedFiniteFrostman.subset {δ C θ : ℝ} {S T : Finset Plane}
    (h : ClosedFiniteFrostman δ C S) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hTS : T ⊆ S) (hcard : θ * (S.card : ℝ) ≤ (T.card : ℝ)) :
    ClosedFiniteFrostman δ (C / θ) T := by
  intro x r hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have hcount : (((↑T : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤
      (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ hTS) (S.finite_toSet.inter_of_left _)
  calc (((↑T : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤
        (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) := hcount
    _ ≤ C * r * (S.card : ℝ) := h x r hδr
    _ = (C / θ) * r * (θ * (S.card : ℝ)) := by field_simp
    _ ≤ (C / θ) * r * (T.card : ℝ) := mul_le_mul_of_nonneg_left hcard (by positivity)

theorem StripFrostman.subset {δ K ζ w θ : ℝ} {S T : Finset Plane}
    (h : StripFrostman δ K ζ w S) (hδ : 0 ≤ δ) (hw : 0 < w) (hK : 0 ≤ K) (hθ : 0 < θ)
    (hTS : T ⊆ S) (hcard : θ * (S.card : ℝ) ≤ (T.card : ℝ)) :
    StripFrostman δ (K / θ) ζ w T := by
  classical
  intro n c r hn hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have hcount : ((T.filter (fun x => |inner ℝ x n - c| < r)).card : ℝ) ≤
      ((S.filter (fun x => |inner ℝ x n - c| < r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hTS)
  calc ((T.filter (fun x => |inner ℝ x n - c| < r)).card : ℝ) ≤
        K * (r / w) ^ ζ * (S.card : ℝ) := hcount.trans (h n c r hn hδr)
    _ = (K / θ) * (r / w) ^ ζ * (θ * (S.card : ℝ)) := by field_simp
    _ ≤ (K / θ) * (r / w) ^ ζ * (T.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)

theorem StripFrostman.indexed {δ K ζ w : ℝ} {S : Finset Plane}
    (h : StripFrostman δ K ζ w S) :
    ∀ (n : Plane) (c r : ℝ), ‖n‖ = 1 → δ ≤ r →
      ((Finset.univ.filter (fun x : S => |inner ℝ (x : Plane) n - c| < r)).card : ℝ) ≤
        K * (r / w) ^ ζ * (Fintype.card S : ℝ) := by
  classical
  intro n c r hn hδr
  have heq : (Finset.univ.filter (fun x : S => |inner ℝ (x : Plane) n - c| < r)).card =
      (S.filter (fun x => |inner ℝ x n - c| < r)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun x => if |inner ℝ x n - c| < r then (1 : ℕ) else 0)
  rw [heq, Fintype.card_coe]
  exact h n c r hn hδr

theorem StripFrostman.mono_constant {δ K K' ζ w : ℝ} {S : Finset Plane}
    (h : StripFrostman δ K ζ w S) (hδ : 0 ≤ δ) (hw : 0 < w) (hKK' : K ≤ K') :
    StripFrostman δ K' ζ w S := by
  intro n c r hn hδr
  apply (h n c r hn hδr).trans
  have hr : 0 ≤ r := hδ.trans hδr
  gcongr

end WangZahlLot.Obl.wz_separated_projection_dichotomy
