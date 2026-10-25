-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.HeavyRelation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.HeavyCaps
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CapFamilies
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SparseCommonNeighbors

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

noncomputable def HeavyRelation {I J : Type*} [Fintype J]
    (f : I → Plane) (g : J → Plane) (r w : ℝ) (i : I) (j : J) : Prop :=
  w * (Fintype.card J : ℝ) ≤ ((Finset.univ.filter
    (fun k => dist (radialDirection (f i) (g k)) (radialDirection (f i) (g j)) ≤ r)).card : ℝ)

/-- A quantitative one-scale seed estimate: many heavy radial caps force
either nearby pins, line concentration, or a large transverse intersection. -/
theorem heavy_relation_density_bound {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (f : I → Plane) (g : J → Plane)
    {δ C q s r w B d : ℝ}
    (hF : IndexedFrostman δ C f) (hG : IndexedFrostman δ C g)
    (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s) (hr : 0 < r) (hw : 0 < w)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hδq : δ ≤ q)
    (hsmall : r ≤ q * s / 256) (hδrad : δ ≤ 4096 * r / (q * s))
    (hpoints : ∀ i j, 1 / 4 ≤ ‖f i - g j‖ ∧ ‖f i - g j‖ ≤ 8)
    (hline : ∀ i i', f i ≠ f i' →
      ((Finset.univ.filter (fun j => |area (g j - f i) (f i' - f i)| < s * ‖f i' - f i‖)).card : ℝ) ≤
        B * (Fintype.card J : ℝ))
    (hdensity : d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ≤
      ((Finset.univ.filter (fun p : I × J => HeavyRelation f g r w p.1 p.2)).card : ℝ)) :
    d ^ 2 ≤ C * q + B + (25 / w) ^ 2 * C * (4096 * r / (q * s)) := by
  classical
  have hneq (i : I) (j : J) : f i ≠ g j := by
    intro h
    have hh := (hpoints i j).1
    rw [h, sub_self, norm_zero] at hh
    norm_num at hh
  have hex (i : I) := exists_heavy_cap_cover (fun j => radialDirection (f i) (g j)) hr hw
  choose D hD using hex
  let Near (i i' : I) : Prop := dist (f i') (f i) ≤ q
  have hb : 0 ≤ B + (25 / w) ^ 2 * C * (4096 * r / (q * s)) := by positivity
  have hnear (i : I) : ((Finset.univ.filter (fun i' => Near i i')).card : ℝ) ≤
      (C * q) * (Fintype.card I : ℝ) := hF (f i) q hδq
  have hfar (i i' : I) (hn : ¬Near i i') :
      ((Finset.univ.filter (fun j => HeavyRelation f g r w i j ∧ HeavyRelation f g r w i' j)).card : ℝ) ≤
        (B + (25 / w) ^ 2 * C * (4096 * r / (q * s))) * (Fintype.card J : ℝ) := by
    have hsep : q ≤ ‖f i' - f i‖ := by simpa only [dist_eq_norm] using (le_of_not_ge hn)
    have hii : f i ≠ f i' := by
      intro heq
      rw [← heq, sub_self, norm_zero] at hsep
      linarith
    exact radial_cap_families_count (HeavyRelation f g r w i) (HeavyRelation f g r w i')
      (D i) (D i') hG hC hq hs hr.le hsmall hδrad hsep
      (fun j => ⟨hneq i j, hneq i' j, (hpoints i j).2, (hpoints i' j).2⟩)
      (by intro u hu; obtain ⟨j, rfl⟩ := (hD i).1 u hu; exact radialDirection_norm (hneq i j))
      (by intro v hv; obtain ⟨j, rfl⟩ := (hD i').1 v hv; exact radialDirection_norm (hneq i' j))
      (hD i).2.1 (hD i').2.1 (hD i).2.2.2 (hD i').2.2.2 (hline i i' hii)
  have h := relation_density_sq_bound (HeavyRelation f g r w) Near hb hd hnear hfar hdensity
  convert h using 1 <;> ring

theorem heavy_relation_card_lt {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (f : I → Plane) (g : J → Plane)
    {δ C q s r w B d : ℝ}
    (hF : IndexedFrostman δ C f) (hG : IndexedFrostman δ C g)
    (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s) (hr : 0 < r) (hw : 0 < w)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (hδq : δ ≤ q)
    (hsmall : r ≤ q * s / 256) (hδrad : δ ≤ 4096 * r / (q * s))
    (hpoints : ∀ i j, 1 / 4 ≤ ‖f i - g j‖ ∧ ‖f i - g j‖ ≤ 8)
    (hline : ∀ i i', f i ≠ f i' →
      ((Finset.univ.filter (fun j => |area (g j - f i) (f i' - f i)| < s * ‖f i' - f i‖)).card : ℝ) ≤
        B * (Fintype.card J : ℝ))
    (hbudget : C * q + B + (25 / w) ^ 2 * C * (4096 * r / (q * s)) < d ^ 2) :
    ((Finset.univ.filter (fun p : I × J => HeavyRelation f g r w p.1 p.2)).card : ℝ) <
      d * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by
  by_contra h
  exact (not_le.mpr hbudget) (heavy_relation_density_bound f g hF hG hC hq hs hr hw hB hd
    hδq hsmall hδrad hpoints hline (le_of_not_gt h))

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
