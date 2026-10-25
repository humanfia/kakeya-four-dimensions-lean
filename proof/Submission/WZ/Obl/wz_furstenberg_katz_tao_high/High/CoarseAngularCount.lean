-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CoarseAngularCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/CoarseAngularCount.lean (c61cafd).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseCount
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.AngularClasses

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Composing fine class and coarse tube assignments retains controlled
incidence and normal errors at the coarse scale. -/
theorem composed_class_geometry {r R s ε₀ η : ℝ} {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hrR : r ≤ R)
    {cls tb : E2 × E2 → E2 × E2} {J₀ J₁ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hJ₁ : J₁ ⊆ J₀) (htbJ : ∀ j ∈ J₀, tb j ∈ J₁)
    (htbgeo : ∀ j ∈ J₀, |inner ℝ (j.1 - (tb j).1) (tb j).2| < 9 * R ∧
      (dist j.2 (tb j).2 < R ∨ dist j.2 (-(tb j).2) < R)) :
    ∀ q ∈ D, |inner ℝ (q.1 - (tb (cls q)).1) (tb (cls q)).2| < 32 * R ∧
      (dist q.2 (tb (cls q)).2 < 2 * R ∨ dist q.2 (-(tb (cls q)).2) < 2 * R) := by
  intro q hq
  have hR := h.r_pos.trans_le hrR
  have hclsD := hJ₀D (hclsJ q hq)
  have htbD := hJ₀D (hJ₁ (htbJ _ (hclsJ q hq)))
  have hinner := pin_near_tube (h.P_norm _ (h.D_mem q hq).1)
    (h.P_norm _ (h.D_mem _ hclsD).1) (h.D_mem _ hclsD).2 (h.D_mem _ htbD).2
    (hgeo q hq).1 (htbgeo _ (hclsJ q hq)).1 (htbgeo _ (hclsJ q hq)).2
  have hdir := normal_close_trans (hgeo q hq).2 (htbgeo _ (hclsJ q hq)).2
  refine ⟨by linarith, ?_⟩
  rcases hdir with hd | hd
  · exact Or.inl (hd.trans_le (by linarith))
  · exact Or.inr (hd.trans_le (by linarith))

/-- The tubes at a pin are the coarse class images of its bush. -/
theorem pinTubes_eq_bush_image (S : Finset (E2 × E2)) (cls tb : E2 × E2 → E2 × E2) (p : E2) :
    pinTubes S cls tb p = (bushOf S p).image (fun e => tb (cls (p, e))) := by
  classical
  ext j
  simp only [pinTubes, Finset.mem_image, Finset.mem_filter, mem_bushOf]
  constructor
  · rintro ⟨q, ⟨hq, hqp⟩, rfl⟩
    exact ⟨q.2, by simpa only [← hqp, Prod.mk.eta] using hq, by rw [← hqp]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨(p, e), ⟨he, rfl⟩, rfl⟩

/-- The actual occupied coarse representatives are bounded by the square of
the angular grid count in one retained reference bush. -/
theorem coarse_tube_count_le_arcs {r R s ε₀ η η' c K : ℝ}
    {P : Finset E2} {D : Finset (E2 × E2)}
    (h : FailData r s ε₀ η P D) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 0 < c) (hK : 0 < K)
    (hrR : r ≤ R) (hRsmall : R ≤ 1 / 8)
    {cls tb : E2 × E2 → E2 × E2} {J₀ J₁ : Finset (E2 × E2)}
    (hclsJ : ∀ q ∈ D, cls q ∈ J₀) (hJ₀D : J₀ ⊆ D)
    (hJcard : (J₀.card : ℝ) ≤ r ^ (-(2 * s) - ε₀))
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (hJ₁ : J₁ ⊆ J₀) (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep R x y)
    (htbJ : ∀ j ∈ J₀, tb j ∈ J₁)
    (htbgeo : ∀ j ∈ J₀, |inner ℝ (j.1 - (tb j).1) (tb j).2| < 9 * R ∧
      (dist j.2 (tb j).2 < R ∨ dist j.2 (-(tb j).2) < R))
    {S : Finset (E2 × E2)} (hSD : S ⊆ D)
    (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    (hbcls : Balanced S cls K) (hbpt : Balanced S (fun q => (q.1, tb (cls q))) K)
    (hfar : ∀ q ∈ S, 2 * ((((S.filter (fun q' => cls q' = cls q)).filter
        (fun q' => dist q'.1 q.1 < c)).card : ℝ)) ≤ (S.filter (fun q' => cls q' = cls q)).card)
    {q : E2 × E2} (hq : q ∈ S) :
    ((S.image (fun a => tb (cls a))).card : ℝ) ≤
      67080 ^ (2 : ℕ) * K ^ 4 * tubeConst r s η c K * r ^ (-ε₀ - 2 * η') *
        (((bushOf S q.1).image (arcOf R)).card : ℝ) ^ 2 := by
  classical
  have hr := h.r_pos
  have hR := hr.trans_le hrR
  have hJprop : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    have hjD := hJ₀D (hJ₁ hj)
    exact ⟨h.P_norm _ (h.D_mem _ hjD).1, (h.D_mem _ hjD).2⟩
  have hcoarse := composed_class_geometry h hrR hclsJ hJ₀D hgeo hJ₁ htbJ htbgeo
  have hstar := Columns.coarse_star_le_arc_count hR hRsmall hJprop hJ₁sep
    (fun a ha => htbJ _ (hclsJ a (hSD ha))) (fun a ha => (h.D_mem a (hSD ha)).2)
    (fun a ha => hcoarse a (hSD ha)) (h.P_norm _ (h.D_mem q (hSD hq)).1)
  rw [← pinTubes_eq_bush_image] at hstar
  have hcount := coarse_tube_count_le h hs0 hs1 hc hK hclsJ hJ₀D hJcard hgeo hSD hS hbcls hbpt hfar hq
  have hC : 0 ≤ tubeConst r s η c K := tubeConst_nonneg hr hc hK.le
  calc
    _ ≤ K ^ 4 * tubeConst r s η c K * r ^ (-ε₀ - 2 * η') *
        ((pinTubes S cls tb q.1).card : ℝ) ^ 2 := hcount
    _ ≤ K ^ 4 * tubeConst r s η c K * r ^ (-ε₀ - 2 * η') *
        (67080 * (((bushOf S q.1).image (arcOf R)).card : ℝ)) ^ 2 := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
