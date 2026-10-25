-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.SetCountBridges.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.LineCounting

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

attribute [local instance] Classical.propDecidable

theorem indexed_filter_card_eq_ncard {X : Type*} (S : Finset X) (P : X → Prop) :
    (Finset.univ.filter (fun x : S => P (x : X))).card = {x ∈ (↑S : Set X) | P x}.ncard := by
  classical
  have hs : {x ∈ (↑S : Set X) | P x} = ↑(S.filter P) := by ext x; simp
  rw [hs, Set.ncard_coe_finset]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_coe_sort S (fun x => if P x then (1 : ℕ) else 0)

theorem indexedLineFrostman_iff_ncard {δ C ζ : ℝ} {S : Finset Plane} :
    IndexedLineFrostman δ C ζ (fun x : S => (x : Plane)) ↔
      ∀ (u : Plane) (a r : ℝ), ‖u‖ = 1 → δ ≤ r →
        ({x ∈ (↑S : Set Plane) | |inner ℝ x u - a| < r}.ncard : ℝ) ≤
          (C * r) ^ ζ * (↑S : Set Plane).ncard := by
  constructor
  · intro h u a r hu hr
    have hc := h u a r hu hr
    rw [indexed_filter_card_eq_ncard S (fun x => |inner ℝ x u - a| < r)] at hc
    simpa only [Fintype.card_coe, Set.ncard_coe_finset] using hc
  · intro h u a r hu hr
    rw [indexed_filter_card_eq_ncard S (fun x => |inner ℝ x u - a| < r)]
    simpa only [Fintype.card_coe, Set.ncard_coe_finset] using h u a r hu hr

/-- The frozen finite-set Frostman predicate used throughout the split. -/
def BoundedSetFrostman (δ C : ℝ) (X : Set Plane) : Prop :=
  X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧
    ∀ (x : Plane) (r : ℝ), δ ≤ r →
      ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard

theorem boundedSetFrostman_coe {δ C : ℝ} {S : Finset Plane}
    (hnorm : ∀ x ∈ S, ‖x‖ ≤ 4)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hfr : ClosedFiniteFrostman δ C S) : BoundedSetFrostman δ C (↑S : Set Plane) := by
  refine ⟨S.finite_toSet, fun x hx => ⟨hnorm x hx, fun y hy hxy => hsep x hx y hy hxy⟩, ?_⟩
  simpa only [ClosedFiniteFrostman, Set.ncard_coe_finset] using hfr

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
