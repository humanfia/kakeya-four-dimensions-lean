-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PrismSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.EnlargedPrism
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SlopeClasses
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Extraction

/-! The finite pigeonhole selecting the initial enlarged prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory

/-- The enlarged prism selection retains a `1/(30000(L/c)^2)` fraction of any
nonnegative weights attached to the crossing tubes. -/
theorem enlarged_prism_selection {d a b c L : ℝ} {n : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc1 : c ≤ 1) (hdc : d ≤ c/100) (hL : 100000000*c ≤ L)
    (x v : Fin n → V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hv : ∀ i, ‖v i‖ = 1) (hcross : ∀ i, Crosses d a b c (x i) (v i) z e)
    (hmeet : ∀ i, ∃ p ∈ T d (x i) (v i) ∩ P a b c z e,
      4*L ≤ dist p (x i) ∧ 4*L ≤ dist p (x i+v i))
    (weight : Fin n → ℝ) (hw : ∀ i, 0 ≤ weight i) (hsum : 0 < ∑ i, weight i) :
    ∃ (S : Finset (Fin n)) (g : V ≃ₗᵢ[ℝ] V), S.Nonempty ∧
      (∑ i, weight i) ≤ 30000*(L/c)^2 * ∑ i ∈ S, weight i ∧
      d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope b c*L ∧
      10000*enlargedSlope b c*L ≤ L ∧
      P a b c z e ⊆ P (10000*a/10) (10000*enlargedSlope b c*L/10) (L/10) z g ∧
      ∀ i ∈ S, Crosses d (10000*a) (10000*enlargedSlope b c*L) L (x i) (v i) z g ∧
        T d (x i) (v i) ∩ ball z (L/2) ⊆ P (10000*a) (10000*enlargedSlope b c*L) L z g := by
  classical
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hcL : c ≤ L := by linarith
  have hLpos : 0 < L := hc.trans_le hcL
  obtain ⟨K, hK, hKsize, ref, href⟩ := crossing_slope_representatives hn hd hda hab hbc hc1 hdc hcL
    x v z e hv hcross
  choose label hlabel using href
  obtain ⟨k, hk⟩ := weighted_scale_selection hK Finset.univ label weight
  let S := Finset.univ.filter (fun i => label i = k)
  have hSnon : S.Nonempty := by
    by_contra hnot
    have hzero : ∑ i ∈ S, weight i = 0 := by rw [Finset.not_nonempty_iff_eq_empty.mp hnot]; simp
    change (∑ i, weight i) ≤ K * ∑ i ∈ S, weight i at hk
    rw [hzero, mul_zero] at hk
    linarith
  have hret : (∑ i, weight i) ≤ 30000*(L/c)^2 * ∑ i ∈ S, weight i := by
    refine hk.trans (mul_le_mul_of_nonneg_right hKsize (Finset.sum_nonneg (fun i _ => hw i)))
  obtain ⟨hdA, hAB, hBL, g, hcore, hgood⟩ := enlarged_prism_for_slope_class e hd hda hab hbc hc1
    hdc hL (hv (ref k)) (hcross (ref k))
  refine ⟨S, g, hSnon, hret, hdA, hAB, hBL, hcore, ?_⟩
  intro i hi
  have hik : label i = k := (Finset.mem_filter.mp hi).2
  have hslopes := hlabel i
  rw [hik] at hslopes
  have hwb : b/L ≤ enlargedSlope b c := by
    apply (div_le_iff₀ hLpos).mpr
    have hh := enlargedSlope_large_length hb.le hc hbc hL
    have hpos := enlargedSlope_pos hb hc
    nlinarith
  exact hgood (x i) (v i) (hv i)
    ((hcross i).slope_bounds hd hda hab hbc hc1 hdc (hv i)).1
    hslopes.1.le (hslopes.2.le.trans hwb) (hmeet i)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
