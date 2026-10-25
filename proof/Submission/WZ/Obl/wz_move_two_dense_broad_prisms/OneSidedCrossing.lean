-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.OneSidedCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingSlab
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.AxialGeometry

/-! One of the two short axial sides of a shaded crossing point stays in its grain. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory

private lemma move_towards_center {d c A B D Q : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hdc : d ≤ c/100)
    (hA : -c/2 ≤ A) (hA0 : A ≤ 0) (hB : 1/4 ≤ B) (hB1 : B ≤ 1)
    (hD : 32*d ≤ D) (hDc : D ≤ c/10)
    (herr : |Q-A-B*D| < 4*d) : |Q| < c/2 := by
  have hlo : 8*d ≤ B*D := by
    have hh := mul_le_mul hB hD (by positivity : 0 ≤ 32*d) (by linarith : 0 ≤ B)
    nlinarith
  have hhi : B*D ≤ c/10 := by
    have hh := mul_le_mul hB1 hDc (by linarith : 0 ≤ D) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  rw [abs_lt] at herr ⊢
  constructor <;> linarith

/-- Excluding a short central interval avoids the tube-radius error. Every
point on one axial side of a crossing point belongs to the same prism. -/
theorem Crosses.one_sided_subset {d a b c : ℝ} {x v z p : V} {e : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < d) (hc : 0 < c) (hdc : d ≤ c/100) (hab : a ≤ b) (hbc : b ≤ c)
    (hv : ‖v‖ = 1) (h : Crosses d a b c x v z e)
    (hpT : p ∈ T d x v) (hpP : p ∈ P a b c z e) :
    (∀ q ∈ T d x v, 32*d ≤ inner ℝ v (q-p) → inner ℝ v (q-p) ≤ c/10 →
      q ∈ P a b c z e) ∨
    (∀ q ∈ T d x v, 32*d ≤ -inner ℝ v (q-p) → -inner ℝ v (q-p) ≤ c/10 →
      q ∈ P a b c z e) := by
  have hlong := h.long_direction hc hdc hab hbc hv
  have hlong1 : |e v 2| ≤ 1 := by
    simpa only [e.norm_map, hv] using wz_move_two_long_grains_gain.abs_coord_le_norm (e v) 2
  have hpcoord : |e (p-z) 2| ≤ c/2 := hpP.2.2
  have herror (q : V) (hq : q ∈ T d x v) :
      |e (q-z) 2 - e (p-z) 2 - e v 2 * inner ℝ v (q-p)| < 4*d := by
    have hh := tube_projected_coordinate_error hv e hpT hq 2
    have he : e (q-p) 2 = e (q-z) 2 - e (p-z) 2 := by
      have ht : q-p = (q-z)-(p-z) := by abel
      rw [ht, map_sub]
      rfl
    simpa only [he, mul_comm] using hh
  have hmem (q : V) (hq : q ∈ T d x v) (hlt : |e (q-z) 2| < c/2) :
      q ∈ P a b c z e := interior_subset (h.slab_subset hc ⟨hq, hlt⟩)
  rcases le_total (e (p-z) 2) 0 with hpneg | hppos
  · rcases le_total 0 (e v 2) with hvpos | hvneg
    · left
      intro q hq hqlo hqhi
      apply hmem q hq
      apply move_towards_center hd hc hdc (by linarith [(abs_le.mp hpcoord).1]) hpneg
        (by simpa only [abs_of_nonneg hvpos] using hlong)
        (by simpa only [abs_of_nonneg hvpos] using hlong1) hqlo hqhi
      exact herror q hq
    · right
      intro q hq hqlo hqhi
      apply hmem q hq
      apply move_towards_center hd hc hdc (by linarith [(abs_le.mp hpcoord).1]) hpneg
        (by simpa only [abs_of_nonpos hvneg] using hlong)
        (by simpa only [abs_of_nonpos hvneg] using hlong1) hqlo hqhi
      convert herror q hq using 1 <;> congr 1 <;> ring
  · rcases le_total 0 (e v 2) with hvpos | hvneg
    · right
      intro q hq hqlo hqhi
      apply hmem q hq
      have hh := move_towards_center (A := -e (p-z) 2) (B := e v 2)
        (D := -inner ℝ v (q-p)) (Q := -e (q-z) 2) hd hc hdc
        (by linarith [(abs_le.mp hpcoord).2]) (by linarith)
        (by simpa only [abs_of_nonneg hvpos] using hlong)
        (by simpa only [abs_of_nonneg hvpos] using hlong1) hqlo hqhi
      apply (by simpa only [abs_neg] using hh :
        |(-e (q-z) 2)-(-e (p-z) 2)-(e v 2)*(-inner ℝ v (q-p))| < 4*d →
          |e (q-z) 2| < c/2)
      have he : (-e (q-z) 2)-(-e (p-z) 2)-(e v 2)*(-inner ℝ v (q-p)) =
          -(e (q-z) 2-e (p-z) 2-e v 2*inner ℝ v (q-p)) := by ring
      rw [he, abs_neg]
      exact herror q hq
    · left
      intro q hq hqlo hqhi
      apply hmem q hq
      have hh := move_towards_center (A := -e (p-z) 2) (B := -e v 2)
        (D := inner ℝ v (q-p)) (Q := -e (q-z) 2) hd hc hdc
        (by linarith [(abs_le.mp hpcoord).2]) (by linarith)
        (by simpa only [abs_of_nonpos hvneg] using hlong)
        (by simpa only [abs_of_nonpos hvneg] using hlong1) hqlo hqhi
      apply (by simpa only [abs_neg] using hh :
        |(-e (q-z) 2)-(-e (p-z) 2)-(-e v 2)*(inner ℝ v (q-p))| < 4*d →
          |e (q-z) 2| < c/2)
      have he : (-e (q-z) 2)-(-e (p-z) 2)-(-e v 2)*(inner ℝ v (q-p)) =
          -(e (q-z) 2-e (p-z) 2-e v 2*inner ℝ v (q-p)) := by ring
      rw [he, abs_neg]
      exact herror q hq

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
