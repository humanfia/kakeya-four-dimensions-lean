-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FiniteLineMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LineCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.MapFrostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

attribute [local instance] Classical.propDecidable

theorem indexed_image_filter_card (S : Finset Plane) (φ : Plane → Plane)
    (hφ : Function.Injective φ) (P : Plane → Prop) :
    (Finset.univ.filter (fun y : S.image φ => P (y : Plane))).card =
      (Finset.univ.filter (fun x : S => P (φ x))).card := by
  classical
  have hleft : (Finset.univ.filter (fun y : S.image φ => P (y : Plane))).card =
      ((S.image φ).filter P).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort (S.image φ) (fun y => if P y then (1 : ℕ) else 0)
  have hright : (Finset.univ.filter (fun x : S => P (φ x))).card =
      (S.filter (fun x => P (φ x))).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun x => if P (φ x) then (1 : ℕ) else 0)
  rw [hleft, hright, Finset.filter_image, Finset.card_image_of_injective _ hφ]

theorem indexedLineFrostman_image {S : Finset Plane} {φ : Plane → Plane}
    (hφ : Function.Injective φ) {δ C ζ : ℝ}
    (h : IndexedLineFrostman δ C ζ (fun x : S => φ x)) :
    IndexedLineFrostman δ C ζ (fun y : S.image φ => (y : Plane)) := by
  intro n c r hn hδr
  have heq := indexed_image_filter_card S φ hφ (fun y => |inner ℝ y n - c| < r)
  rw [heq, Fintype.card_coe, Finset.card_image_of_injective _ hφ]
  simpa only [Fintype.card_coe] using h n c r hn hδr

theorem indexedLineFrostman_of_scaled_count {I : Type*} [Fintype I] {f : I → Plane}
    {δ C K q ζ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hq : 0 < q)
    (hbudget : K / q ^ ζ ≤ C ^ ζ)
    (h : ∀ (n : Plane) (c r : ℝ), ‖n‖ = 1 → δ ≤ r →
      ((Finset.univ.filter (fun i => |inner ℝ (f i) n - c| < r)).card : ℝ) ≤
        K * (r / q) ^ ζ * (Fintype.card I : ℝ)) :
    IndexedLineFrostman δ C ζ f := by
  intro n c r hn hδr
  have hr : 0 ≤ r := hδ.le.trans hδr
  apply (h n c r hn hδr).trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Real.div_rpow hr hq.le, Real.mul_rpow hC hr]
  calc K * (r ^ ζ / q ^ ζ) = (K / q ^ ζ) * r ^ ζ := by ring
    _ ≤ C ^ ζ * r ^ ζ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hr ζ)

theorem ClosedFiniteFrostman.mono_scale {δ δ' C : ℝ} {S : Finset Plane}
    (h : ClosedFiniteFrostman δ C S) (hδδ' : δ ≤ δ') : ClosedFiniteFrostman δ' C S :=
  fun x r hr => h x r (hδδ'.trans hr)

theorem StripFrostman.change_width {δ K ζ w W : ℝ} {S : Finset Plane}
    (h : StripFrostman δ K ζ w S) (hδ : 0 ≤ δ) (hw : 0 < w) (hW : 0 < W) :
    StripFrostman δ (K * (W / w) ^ ζ) ζ W S := by
  intro n c r hn hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have heq : K * (r / w) ^ ζ = K * (W / w) ^ ζ * (r / W) ^ ζ := by
    rw [mul_assoc, ← Real.mul_rpow (by positivity : 0 ≤ W / w) (by positivity : 0 ≤ r / W)]
    congr 2
    field_simp
  rw [← heq]
  exact h n c r hn hδr

theorem StripFrostman.smaller_width {δ K ζ w W : ℝ} {S : Finset Plane}
    (h : StripFrostman δ K ζ W S) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hζ : 0 ≤ ζ)
    (hw : 0 < w) (hwW : w ≤ W) : StripFrostman δ K ζ w S := by
  intro n c r hn hδr
  have hr : 0 ≤ r := hδ.trans hδr
  have hW : 0 < W := hw.trans_le hwW
  apply (h n c r hn hδr).trans
  gcongr

end WangZahlLot.Obl.wz_separated_projection_dichotomy
