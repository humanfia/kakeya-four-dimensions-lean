-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.SlopeClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RectangleGrid
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingDirections

/-! Quantitative finite selection of the enlarged-prism orientations. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- Crossing directions fit in at most a constant times `(L/c)^2` slope cells.
Each cell has an actual crossing direction as representative. -/
theorem crossing_slope_representatives {d a b c L : ℝ} {n : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc1 : c ≤ 1) (hdc : d ≤ c/100) (hcL : c ≤ L)
    (x v : Fin n → V) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (hv : ∀ i, ‖v i‖ = 1) (hcross : ∀ i, Crosses d a b c (x i) (v i) z e) :
    ∃ K : ℕ, 0 < K ∧ (K : ℝ) ≤ 30000*(L/c)^2 ∧
      ∃ ref : Fin K → Fin n, ∀ i, ∃ k,
        |e (v i) 0 / e (v i) 2 - e (v (ref k)) 0 / e (v (ref k)) 2| < a/L ∧
        |e (v i) 1 / e (v i) 2 - e (v (ref k)) 1 / e (v (ref k)) 2| < b/L := by
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hL : 0 < L := hc.trans_le hcL
  let s : ℝ := c/(72*L)
  have hs : 0 < s := by dsimp [s]; positivity
  let A : Fin 2 → ℝ := ![72*a/c, 72*b/c]
  have hA : ∀ j, 0 < A j := by intro j; fin_cases j <;> simp [A] <;> positivity
  let p : Fin n → Fin 2 → ℝ := fun i =>
    ![e (v i) 0 / e (v i) 2, e (v i) 1 / e (v i) 2]
  have hp : ∀ i j, |p i j| ≤ A j := by
    intro i j
    have hh := (hcross i).slope_bounds hd hda hab hbc hc1 hdc (hv i)
    fin_cases j
    · exact hh.2.1
    · exact hh.2.2
  obtain ⟨hM, hsize⟩ := rectangle_grid_size hs
  obtain ⟨ref, href⟩ := rectangle_grid_representatives hn p A hA hp hs hM
  refine ⟨(2*⌈s⁻¹⌉₊+1)^2, by positivity, ?_, ref, ?_⟩
  · have hratio : 1 ≤ L/c := (one_le_div hc).mpr hcL
    have he : 2/s+3 = 144*(L/c)+3 := by dsimp [s]; field_simp <;> ring
    rw [he] at hsize
    have hbound : (144*(L/c)+3)^2 ≤ 30000*(L/c)^2 := by nlinarith
    exact hsize.trans hbound
  · intro i
    obtain ⟨k, hk⟩ := href i
    refine ⟨k, ?_, ?_⟩
    · have hh := hk 0
      change |e (v i) 0 / e (v i) 2 - e (v (ref k)) 0 / e (v (ref k)) 2| < s*(72*a/c) at hh
      have he : s*(72*a/c) = a/L := by dsimp [s]; field_simp <;> ring
      rwa [he] at hh
    · have hh := hk 1
      change |e (v i) 1 / e (v i) 2 - e (v (ref k)) 1 / e (v (ref k)) 2| < s*(72*b/c) at hh
      have he : s*(72*b/c) = b/L := by dsimp [s]; field_simp <;> ring
      rwa [he] at hh

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
