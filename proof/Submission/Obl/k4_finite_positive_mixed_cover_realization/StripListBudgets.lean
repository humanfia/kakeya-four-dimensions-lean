/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit dc469a9986212957c1fb8d5b5640cd5f3d67bbae, Submission/Obl/k4_finite_path_candidate_conversion/StripListBudgets.lean. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.UnitStripCodes
import Submission.Obl.k4_finite_positive_mixed_cover_realization.RecoveredLists

/-!
With one neighboring unit-normal code in each direction, the actual path
slack bounds the midpoint-list radius. All final strip-list losses are at
most a fixed multiple of the square of that path slack.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

theorem unitStripCodeList_path_card {κ : ℝ} (hκ : 1 ≤ κ)
    (h : ℝ) (m : Plane) (γ r : ℝ)
    (normal : (Fin 3 → ℤ) → Plane) (bias : (Fin 3 → ℤ) → ℝ)
    (t : ℝ) (Y : Plane) :
    ((unitStripCodeList 1 ⌈4 + 6 * κ⌉₊ h m γ r normal bias t Y).card : ℝ) ≤ 1242 * κ := by
  have hceil : (⌈4 + 6 * κ⌉₊ : ℝ) < 5 + 6 * κ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ 4 + 6 * κ)
    linarith
  have hcard := card_unitStripCodeList_le 1 ⌈4 + 6 * κ⌉₊ h m γ r normal bias t Y
  have hcard' : ((unitStripCodeList 1 ⌈4 + 6 * κ⌉₊ h m γ r normal bias t Y).card : ℝ) ≤
      54 * (2 * (⌈4 + 6 * κ⌉₊ : ℝ) + 1) := by
    exact_mod_cast hcard
  exact hcard'.trans (by linarith)

/-- Recover the whole output list from the deeper original list. The bound
contains no actual candidate multiplicity or candidate power slack. -/
theorem recovered_unitStripCodeList_path_card {β P D : Type*} [Fintype β]
    (key : β → P × UnitStripCode) (hkey : Function.Injective key)
    (ancestor : D → P) (S : Finset D) {κ : ℝ} (hκ : 1 ≤ κ) (hS : (S.card : ℝ) ≤ κ)
    (h r : D → ℝ) (m : D → Plane) (γ : D → ℝ)
    (normal : D → (Fin 3 → ℤ) → Plane) (bias : D → (Fin 3 → ℤ) → ℝ)
    (t : D → ℝ) (Y : D → Plane) :
    ((recoveredCodeList key ancestor S
      (fun d => unitStripCodeList 1 ⌈4 + 6 * κ⌉₊ (h d) (m d) (γ d) (r d)
        (normal d) (bias d) (t d) (Y d))).card : ℝ) ≤ 1242 * κ ^ 2 := by
  have hcard := card_recoveredCodeList_le key hkey ancestor S
    (fun d => unitStripCodeList 1 ⌈4 + 6 * κ⌉₊ (h d) (m d) (γ d) (r d)
      (normal d) (bias d) (t d) (Y d)) hS (show 0 ≤ 1242 * κ by positivity)
    (fun d _ => unitStripCodeList_path_card hκ _ _ _ _ _ _ _ _)
  exact hcard.trans_eq (by ring)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
