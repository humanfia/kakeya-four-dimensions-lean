-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.QuadCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.QuadGeometry
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Overlap
-- Copied from session x0338 (o070 branch, commit ec01e52, file QuadCount.lean), namespace renamed.

/-!
# The quadratic prism count for parent-structured covers

`quad_count_of_parents`: let `δ`-tubes `A i` sit in unit `ρ`-tubes `R l` (parents) whose axes
form a `NetSeparated` net, and let sets `P j` (labelled by parents) be saturated in their parents
(`κ s₀ ≤ H #{i | A i ⊆ R (label j) ∩ P j} δ²`), with tube degree at most `D` and parentwise
Katz–Tao `#{i | A i ⊆ R l ∩ U} δ² ≤ κ |U|`.  Then for every convex `U`
`#{j | P j ⊆ U} s₀² ≤ 27³ (H D)² |U|²`.

Proof: the parent count gives `n_l(U) s₀ ≤ H D |V_l|` for `V_l = cl U ∩ Cyl_l` (the short
cylinder around the parent), so `n_l s₀² ≤ (H D)² |V_l|²`; `V_l` has extent `≥ 9/10` along the
parent direction, so its two end pieces carry `|V_l|/27` each; a pair of points lies in the end
products of at most `27` parents (directions within `27 ρ`, then `NetSeparated` and packing), so
`∑ |V_l|² ≤ 27³ |cl U|² = 27³ |U|²`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory Metric
open scoped RealInnerProductSpace

lemma ncard_setOf_eq_card {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ncard {a | p a} = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- The perpendicular part of `e` with respect to a unit `w` is no longer than `e`. -/
lemma norm_perp_le {w : Space} (hw : ‖w‖ = 1) (e : Space) : ‖e - ⟪w, e⟫ • w‖ ≤ ‖e‖ := by
  have h : ‖e - ⟪w, e⟫ • w‖ ^ 2 = ‖e‖ ^ 2 - ⟪w, e⟫ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hw, mul_one,
      sq_abs, real_inner_comm]
    ring
  have h0 := norm_nonneg (e - ⟪w, e⟫ • w)
  have h1 := norm_nonneg e
  nlinarith [sq_nonneg ⟪w, e⟫]

/-- A unit `ρ`-tube lies in the short cylinder of radius `ρ` and half-length `1/2 + ρ` about its
centre. -/
lemma tube_subset_cyl {z w : Space} (hw : ‖w‖ = 1) {ρ : ℝ} :
    Tube ρ z w ⊆ Cyl (z + (1 / 2 : ℝ) • w) w ρ (1 / 2 + ρ) := by
  intro y hy
  rw [Tube, Metric.mem_thickening_iff] at hy
  obtain ⟨a, ha, hya⟩ := hy
  rw [segment_eq_image'] at ha
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := ha
  set e := y - (z + θ • (z + w - z)) with he
  have hen : ‖e‖ < ρ := by rw [he, ← dist_eq_norm]; exact hya
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hy' : y - (z + (1 / 2 : ℝ) • w) = (θ - 1 / 2) • w + e := by rw [he]; module
  have hin : ⟪w, y - (z + (1 / 2 : ℝ) • w)⟫ = (θ - 1 / 2) + ⟪w, e⟫ := by
    rw [hy', inner_add_right, real_inner_smul_right, hww, mul_one]
  refine ⟨?_, ?_⟩
  · have hperp : (y - (z + (1 / 2 : ℝ) • w)) - ⟪w, y - (z + (1 / 2 : ℝ) • w)⟫ • w =
        e - ⟪w, e⟫ • w := by
      rw [hin, hy']; module
    rw [hperp]
    exact (norm_perp_le hw e).trans hen.le
  · rw [hin]
    have h1 : |⟪w, e⟫| ≤ ‖e‖ := by
      have := abs_real_inner_le_norm w e
      rwa [hw, one_mul] at this
    have h2 : |θ - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc |(θ - 1 / 2) + ⟪w, e⟫| ≤ |θ - 1 / 2| + |⟪w, e⟫| := abs_add_le _ _
      _ ≤ 1 / 2 + ρ := by linarith

/-- A point of the short cylinder is within `2ρ` of the parent segment. -/
lemma exists_seg_near_of_mem_cyl {z w p : Space} (hw : ‖w‖ = 1) {ρ : ℝ}
    (hp : p ∈ Cyl (z + (1 / 2 : ℝ) • w) w ρ (1 / 2 + ρ)) :
    ∃ a ∈ segment ℝ z (z + w), dist a p ≤ 2 * ρ := by
  obtain ⟨h1, h2⟩ := hp
  set m := z + (1 / 2 : ℝ) • w with hm
  set s := ⟪w, p - m⟫ with hs
  set t := max (-(1 / 2 : ℝ)) (min (1 / 2) s) with ht
  obtain ⟨hs1, hs2⟩ := abs_le.mp h2
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans h1
  have hts1 : t ≤ s + ρ := max_le (by linarith) ((min_le_right _ _).trans (by linarith))
  have hts2 : s - ρ ≤ t := (le_min (by linarith) (by linarith)).trans (le_max_right _ _)
  have ht0 : -(1 / 2 : ℝ) ≤ t := le_max_left _ _
  have ht1 : t ≤ 1 / 2 := max_le (by norm_num) (min_le_left _ _)
  refine ⟨z + (t + 1 / 2) • w, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨t + 1 / 2, ⟨by linarith, by linarith⟩, by module⟩
  · rw [dist_eq_norm]
    have e : z + (t + 1 / 2) • w - p = -((p - m) - s • w) + (t - s) • w := by rw [hm]; module
    rw [e]
    calc ‖-((p - m) - s • w) + (t - s) • w‖ ≤ ‖-((p - m) - s • w)‖ + ‖(t - s) • w‖ :=
          norm_add_le _ _
      _ = ‖(p - m) - s • w‖ + |t - s| := by
          rw [norm_neg, norm_smul, hw, mul_one, Real.norm_eq_abs]
      _ ≤ ρ + ρ := add_le_add h1 (abs_le.mpr ⟨by linarith, by linarith⟩)
      _ = 2 * ρ := by ring

/-- For a unit `w` and `⟪w, d⟫ ≥ 0`: `‖d - ‖d‖ w‖ ≤ 2 ‖d - ⟪w, d⟫ w‖`. -/
lemma norm_sub_dir_le {w d : Space} (hw : ‖w‖ = 1) (hl : 0 ≤ ⟪w, d⟫) :
    ‖d - ‖d‖ • w‖ ≤ 2 * ‖d - ⟪w, d⟫ • w‖ := by
  have h2 : ‖d‖ ≤ ‖d - ⟪w, d⟫ • w‖ + ⟪w, d⟫ := by
    calc ‖d‖ = ‖(d - ⟪w, d⟫ • w) + ⟪w, d⟫ • w‖ := by rw [sub_add_cancel]
      _ ≤ ‖d - ⟪w, d⟫ • w‖ + ‖⟪w, d⟫ • w‖ := norm_add_le _ _
      _ = ‖d - ⟪w, d⟫ • w‖ + ⟪w, d⟫ := by
          rw [norm_smul, hw, mul_one, Real.norm_of_nonneg hl]
  have h1 : ⟪w, d⟫ ≤ ‖d‖ := by
    have := real_inner_le_norm w d
    rwa [hw, one_mul] at this
  have e : d - ‖d‖ • w = (d - ⟪w, d⟫ • w) - (‖d‖ - ⟪w, d⟫) • w := by module
  calc ‖d - ‖d‖ • w‖ = ‖(d - ⟪w, d⟫ • w) - (‖d‖ - ⟪w, d⟫) • w‖ := by rw [← e]
    _ ≤ ‖d - ⟪w, d⟫ • w‖ + ‖(‖d‖ - ⟪w, d⟫) • w‖ := norm_sub_le _ _
    _ = ‖d - ⟪w, d⟫ • w‖ + (‖d‖ - ⟪w, d⟫) := by
        rw [norm_smul, hw, mul_one, Real.norm_of_nonneg (by linarith)]
    _ ≤ 2 * ‖d - ⟪w, d⟫ • w‖ := by linarith

/-- Two points of a cylinder of radius `r`: the perpendicular part of their difference is at
most `2r`. -/
lemma perp_sub_le_of_mem_cyl {m w p q : Space} {r h : ℝ} (hp : p ∈ Cyl m w r h)
    (hq : q ∈ Cyl m w r h) : ‖(q - p) - ⟪w, q - p⟫ • w‖ ≤ 2 * r := by
  have hin : ⟪w, q - p⟫ = ⟪w, q - m⟫ - ⟪w, p - m⟫ := by
    rw [← inner_sub_right]; congr 1; abel
  have e : (q - p) - ⟪w, q - p⟫ • w =
      ((q - m) - ⟪w, q - m⟫ • w) - ((p - m) - ⟪w, p - m⟫ • w) := by
    rw [hin]; module
  rw [e]
  calc ‖((q - m) - ⟪w, q - m⟫ • w) - ((p - m) - ⟪w, p - m⟫ • w)‖
      ≤ ‖(q - m) - ⟪w, q - m⟫ • w‖ + ‖(p - m) - ⟪w, p - m⟫ • w‖ := norm_sub_le _ _
    _ ≤ r + r := add_le_add hq.1 hp.1
    _ = 2 * r := by ring

/-- Two cylinders of radius `r` containing `p` and `q`, with `⟪w, q - p⟫ ≥ e` and
`⟪w', q - p⟫ ≥ e`, have directions `e ‖w - w'‖ ≤ 8 r`. -/
lemma dir_close_of_mem_cyl {m w m' w' p q : Space} {r h h' e : ℝ} (hw : ‖w‖ = 1)
    (hw' : ‖w'‖ = 1) (hp : p ∈ Cyl m w r h) (hq : q ∈ Cyl m w r h) (hp' : p ∈ Cyl m' w' r h')
    (hq' : q ∈ Cyl m' w' r h') (he : 0 < e) (hl : e ≤ ⟪w, q - p⟫) (hl' : e ≤ ⟪w', q - p⟫) :
    e * ‖w - w'‖ ≤ 8 * r := by
  set d := q - p with hd
  have h1 := norm_sub_dir_le hw (by linarith : 0 ≤ ⟪w, d⟫)
  have h2 := norm_sub_dir_le hw' (by linarith : 0 ≤ ⟪w', d⟫)
  have h3 := perp_sub_le_of_mem_cyl hp hq
  have h4 := perp_sub_le_of_mem_cyl hp' hq'
  have hdn : e ≤ ‖d‖ := hl.trans (by
    have := real_inner_le_norm w d
    rwa [hw, one_mul] at this)
  have e5 : ‖d‖ • (w - w') = (d - ‖d‖ • w') - (d - ‖d‖ • w) := by module
  have h5 : ‖d‖ * ‖w - w'‖ ≤ 8 * r := by
    calc ‖d‖ * ‖w - w'‖ = ‖‖d‖ • (w - w')‖ := by rw [norm_smul, norm_norm]
      _ = ‖(d - ‖d‖ • w') - (d - ‖d‖ • w)‖ := by rw [e5]
      _ ≤ ‖d - ‖d‖ • w'‖ + ‖d - ‖d‖ • w‖ := norm_sub_le _ _
      _ ≤ 2 * (2 * r) + 2 * (2 * r) := by linarith
      _ = 8 * r := by ring
  calc e * ‖w - w'‖ ≤ ‖d‖ * ‖w - w'‖ := mul_le_mul_of_nonneg_right hdn (norm_nonneg _)
    _ ≤ 8 * r := h5

open Classical in
/-- **Multiplicity.**  For a `NetSeparated` net of unit segments, a pair `(p, p')` with
`⟪w l, p' - p⟫ ≥ 3/10` lies in the short cylinders of at most `27` parents. -/
theorem mult_le_of_netSeparated {q : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (z w : Fin q → Space)
    (hw : ∀ l, ‖w l‖ = 1) (hsep : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NetSeparated ρ z w) (s : Finset (Fin q))
    (p p' : Space) :
    (s.filter (fun l => p ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      p' ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      3 / 10 ≤ ⟪w l, p' - p⟫)).card ≤ 27 := by
  set t := s.filter (fun l => p ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      p' ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      3 / 10 ≤ ⟪w l, p' - p⟫) with ht
  have hcl : ∀ l, ∃ a : Space, p ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) →
      a ∈ segment ℝ (z l) (z l + w l) ∧ dist a p ≤ 2 * ρ := by
    intro l
    by_cases h : p ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ)
    · obtain ⟨a, ha, hd⟩ := exists_seg_near_of_mem_cyl (hw l) h
      exact ⟨a, fun _ => ⟨ha, hd⟩⟩
    · exact ⟨p, fun h' => absurd h' h⟩
  choose y hy using hcl
  have hmem : ∀ l ∈ t, p ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      p' ∈ Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ) ∧
      3 / 10 ≤ ⟪w l, p' - p⟫ := fun l hl => (Finset.mem_filter.mp hl).2
  have hpack := card_mul_pow_le_of_packing t y p hρ (by positivity : (0 : ℝ) ≤ 2 * ρ)
    (fun l hl l' hl' hne => by
      obtain ⟨hp, hq, he⟩ := hmem l hl
      obtain ⟨hp', hq', he'⟩ := hmem l' hl'
      have hclose := dir_close_of_mem_cyl (hw l) (hw l') hp hq hp' hq'
        (by norm_num : (0 : ℝ) < 3 / 10) he he'
      rcases hsep l l' hne with htr | hfar
      · exfalso
        have h1 : min ‖w l - w l'‖ ‖w l + w l'‖ ≤ ‖w l - w l'‖ := min_le_left _ _
        linarith
      · exact hfar (y l) (hy l hp).1 (y l') (hy l' hp').1)
    (fun l hl => (hy l (hmem l hl).1).2)
  have h3 : (2 * ρ + ρ) ^ 3 = 27 * ρ ^ 3 := by ring
  rw [h3] at hpack
  have hρ3 : 0 < ρ ^ 3 := by positivity
  have : (t.card : ℝ) ≤ 27 := le_of_mul_le_mul_right hpack hρ3
  exact_mod_cast this

/-- A unit `δ`-tube in a unit `ρ`-tube (`ρ ≤ 1/100`) has two points `y, y'` with
`⟪w, y' - y⟫ ≥ 9/10`. -/
lemma extent_of_tube_subset {δ ρ : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1 / 100) {x v z w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hsub : Tube δ x v ⊆ Tube ρ z w) :
    ∃ y ∈ Tube δ x v, ∃ y' ∈ Tube δ x v, 9 / 10 ≤ ⟪w, y' - y⟫ := by
  have hdir := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.direction_near_of_subset hδ hv hw hsub
  have hx : x ∈ Tube δ x v := Metric.self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))
  have hxv : x + v ∈ Tube δ x v :=
    Metric.self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))
  have hnsq1 : ‖v - w‖ ^ 2 = 2 - 2 * ⟪w, v⟫ := by
    rw [norm_sub_sq_real, hv, hw, real_inner_comm]; ring
  have hnsq2 : ‖v + w‖ ^ 2 = 2 + 2 * ⟪w, v⟫ := by
    rw [norm_add_sq_real, hv, hw, real_inner_comm]; ring
  rcases le_total ‖v - w‖ ‖v + w‖ with h | h
  · rw [min_eq_left h] at hdir
    have h0 := norm_nonneg (v - w)
    have hsq : ‖v - w‖ ^ 2 ≤ (1 / 25) ^ 2 := by nlinarith
    refine ⟨x, hx, x + v, hxv, ?_⟩
    rw [add_sub_cancel_left]
    nlinarith
  · rw [min_eq_right h] at hdir
    have h0 := norm_nonneg (v + w)
    have hsq : ‖v + w‖ ^ 2 ≤ (1 / 25) ^ 2 := by nlinarith
    refine ⟨x + v, hxv, x, hx, ?_⟩
    rw [sub_add_cancel_left, inner_neg_right]
    nlinarith

open Classical in
/-- **Parent count.**  Saturation, the tube degree and the parentwise Katz–Tao bound on a convex
`V ⊇ R l ∩ U` (on the tubes) give `n_l(U) s₀ ≤ H D X` where `κ X` bounds `#{A i ⊆ R l ∩ V} δ²`. -/
lemma parent_count {n p q : ℕ} {δ κ H D s₀ X : ℝ} (hκ : 0 < κ) (hH : 0 ≤ H) (hD0 : 0 ≤ D)
    (A : Fin n → Set Space) (R : Fin q → Set Space) (P : Fin p → Set Space)
    (label : Fin p → Fin q)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, κ * s₀ ≤ H * (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ) * δ ^ 2)
    (l : Fin q) (U V : Set Space) (hUV : ∀ i, A i ⊆ R l → A i ⊆ U → A i ⊆ V)
    (hKT : (ncard {i | A i ⊆ R l ∧ A i ⊆ V} : ℝ) * δ ^ 2 ≤ κ * X) :
    ((Finset.univ.filter (fun j => label j = l ∧ P j ⊆ U)).card : ℝ) * s₀ ≤ H * D * X := by
  set J := Finset.univ.filter (fun j => label j = l ∧ P j ⊆ U) with hJ
  set I := Finset.univ.filter (fun i => A i ⊆ R l ∧ A i ⊆ V) with hI
  have h1 : ∀ j ∈ J, κ * s₀ ≤ H * ((I.filter (fun i => A i ⊆ P j)).card : ℝ) * δ ^ 2 := by
    intro j hj
    obtain ⟨hlj, hPU⟩ := (Finset.mem_filter.mp hj).2
    have hs := hsat j
    rw [hlj] at hs
    have hc : ncard {i | A i ⊆ R l ∧ A i ⊆ P j} ≤ (I.filter (fun i => A i ⊆ P j)).card := by
      rw [ncard_setOf_eq_card]
      apply Finset.card_le_card
      intro i hi
      simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨⟨hi.1, hUV i hi.1 (hi.2.trans hPU)⟩, hi.2⟩
    have hc' : (ncard {i | A i ⊆ R l ∧ A i ⊆ P j} : ℝ) ≤
        ((I.filter (fun i => A i ⊆ P j)).card : ℝ) := by exact_mod_cast hc
    calc κ * s₀ ≤ H * (ncard {i | A i ⊆ R l ∧ A i ⊆ P j} : ℝ) * δ ^ 2 := hs
      _ ≤ H * ((I.filter (fun i => A i ⊆ P j)).card : ℝ) * δ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' hH) (sq_nonneg δ)
  have h2 : ∑ j ∈ J, ((I.filter (fun i => A i ⊆ P j)).card : ℝ) ≤ D * I.card := by
    have hcomm : ∑ j ∈ J, (I.filter (fun i => A i ⊆ P j)).card =
        ∑ i ∈ I, (J.filter (fun j => A i ⊆ P j)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hle : ∀ i ∈ I, ((J.filter (fun j => A i ⊆ P j)).card : ℝ) ≤ D := by
      intro i _
      have hc : (J.filter (fun j => A i ⊆ P j)).card ≤ ncard {j | A i ⊆ P j} := by
        rw [ncard_setOf_eq_card]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      exact (by exact_mod_cast hc : ((J.filter (fun j => A i ⊆ P j)).card : ℝ) ≤
        (ncard {j | A i ⊆ P j} : ℝ)).trans (hdegree i)
    calc ∑ j ∈ J, ((I.filter (fun i => A i ⊆ P j)).card : ℝ)
        = ∑ i ∈ I, ((J.filter (fun j => A i ⊆ P j)).card : ℝ) := by exact_mod_cast hcomm
      _ ≤ ∑ i ∈ I, D := Finset.sum_le_sum hle
      _ = D * I.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hIc : (I.card : ℝ) * δ ^ 2 ≤ κ * X := by
    rw [ncard_setOf_eq_card] at hKT
    exact hKT
  have h3 : (J.card : ℝ) * (κ * s₀) ≤ H * δ ^ 2 * (D * I.card) := by
    calc (J.card : ℝ) * (κ * s₀) = ∑ j ∈ J, κ * s₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ J, H * ((I.filter (fun i => A i ⊆ P j)).card : ℝ) * δ ^ 2 :=
          Finset.sum_le_sum h1
      _ = H * δ ^ 2 * ∑ j ∈ J, ((I.filter (fun i => A i ⊆ P j)).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ H * δ ^ 2 * (D * I.card) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hH (sq_nonneg δ))
  have h4 : (J.card : ℝ) * s₀ * κ ≤ H * D * X * κ := by
    calc (J.card : ℝ) * s₀ * κ = (J.card : ℝ) * (κ * s₀) := by ring
      _ ≤ H * δ ^ 2 * (D * I.card) := h3
      _ = H * D * ((I.card : ℝ) * δ ^ 2) := by ring
      _ ≤ H * D * (κ * X) := mul_le_mul_of_nonneg_left hIc (mul_nonneg hH hD0)
      _ = H * D * X * κ := by ring
  exact le_of_mul_le_mul_right h4 hκ

/-- The closure of a convex set has the same volume. -/
lemma volume_closure_le_of_convex {U : Set Space} (hU : Convex ℝ U) :
    volume (closure U) ≤ volume U := by
  calc volume (closure U) ≤ volume (U ∪ frontier U) := measure_mono (fun y hy => by
          by_cases h : y ∈ U
          · exact Or.inl h
          · exact Or.inr ⟨hy, fun hi => h (interior_subset hi)⟩)
    _ ≤ volume U + volume (frontier U) := measure_union_le _ _
    _ = volume U := by rw [Convex.addHaar_frontier (μ := volume) hU, add_zero]

open Classical in
/-- **Quadratic count for parent-structured covers.**  See the module docstring. -/
theorem quad_count_of_parents {n p q : ℕ} {δ ρ κ H D s₀ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 100) (hκ : 0 < κ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hs₀ : 0 < s₀)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1) (hsep : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NetSeparated ρ z w)
    (P : Fin p → Set Space) (label : Fin p → Fin q)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z l) (w l) ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal κ * volume U)
    (hdegree : ∀ i, (ncard {j | Tube δ (x i) (v i) ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, κ * s₀ ≤ H * (ncard {i | Tube δ (x i) (v i) ⊆
        Tube ρ (z (label j)) (w (label j)) ∧ Tube δ (x i) (v i) ⊆ P j} : ℝ) * δ ^ 2)
    (U : Set Space) (hU : Convex ℝ U) :
    ENNReal.ofReal ((ncard {j | P j ⊆ U} : ℝ) * s₀ ^ 2) ≤
      ENNReal.ofReal (27 ^ 3 * (H * D) ^ 2) * volume U ^ 2 := by
  set A : Fin n → Set Space := fun i => Tube δ (x i) (v i) with hA
  set R : Fin q → Set Space := fun l => Tube ρ (z l) (w l) with hR
  set C : Fin q → Set Space := fun l => Cyl (z l + (1 / 2 : ℝ) • w l) (w l) ρ (1 / 2 + ρ)
    with hC
  set V : Fin q → Set Space := fun l => closure U ∩ C l with hV
  have hVconv : ∀ l, Convex ℝ (V l) := fun l => hU.closure.inter (cyl_convex _ _ _ _)
  have hVcpt : ∀ l, IsCompact (V l) := fun l =>
    (cyl_isCompact (hw l) _ _).inter_left isClosed_closure
  have hVfin : ∀ l, volume (V l) ≠ ⊤ := fun l => (hVcpt l).measure_lt_top.ne
  have hRC : ∀ l, R l ⊆ C l := fun l => tube_subset_cyl (hw l)
  set J : Fin q → Finset (Fin p) := fun l =>
    Finset.univ.filter (fun j => label j = l ∧ P j ⊆ U) with hJ
  set L : Finset (Fin q) := Finset.univ.filter (fun l => (J l).Nonempty) with hL
  set vol : Fin q → ℝ := fun l => (volume (V l)).toReal with hvol
  have hvol0 : ∀ l, 0 ≤ vol l := fun l => ENNReal.toReal_nonneg
  -- per-parent counts
  have hcount : ∀ l, ((J l).card : ℝ) * s₀ ≤ H * D * vol l := by
    intro l
    apply parent_count hκ hH hD A R P label hdegree hsat l U (V l)
    · intro i hiR hiU
      exact subset_inter (hiU.trans subset_closure) (hiR.trans (hRC l))
    · have h := hparent l (V l) (hVconv l)
      rw [← ENNReal.ofReal_toReal (hVfin l), ← ENNReal.ofReal_mul hκ.le] at h
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hκ.le (hvol0 l))).mp h
  -- extent of `V l` for the occupied parents
  have hext : ∀ l ∈ L, ∃ y ∈ V l, ∃ y' ∈ V l, 9 / 10 ≤ ⟪w l, y' - y⟫ := by
    intro l hl
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨hlj, hPU⟩ := (Finset.mem_filter.mp hj).2
    have hs := hsat j
    rw [hlj] at hs
    have hpos : 0 < ncard {i | A i ⊆ R l ∧ A i ⊆ P j} := by
      by_contra h0
      have h0' : ncard {i | A i ⊆ R l ∧ A i ⊆ P j} = 0 := by omega
      have : (ncard {i | Tube δ (x i) (v i) ⊆ Tube ρ (z l) (w l) ∧
          Tube δ (x i) (v i) ⊆ P j} : ℝ) = 0 := by exact_mod_cast h0'
      rw [this, mul_zero, zero_mul] at hs
      nlinarith [mul_pos hκ hs₀]
    obtain ⟨i, hiR, hiP⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    obtain ⟨y, hy, y', hy', hyy⟩ := extent_of_tube_subset hδ hρ1 (hv i) (hw l) hiR
    have hAV : A i ⊆ V l :=
      subset_inter ((hiP.trans hPU).trans subset_closure) (hiR.trans (hRC l))
    exact ⟨y, hAV hy, y', hAV hy', hyy⟩
  -- end pieces
  have hpieces : ∀ l, ∃ E₁ E₂ : Set Space, MeasurableSet E₁ ∧ MeasurableSet E₂ ∧
      E₁ ⊆ V l ∧ E₂ ⊆ V l ∧ (l ∈ L → volume (V l) ≤ 27 * volume E₁ ∧
        volume (V l) ≤ 27 * volume E₂ ∧ ∀ y ∈ E₁, ∀ y' ∈ E₂, 3 / 10 ≤ ⟪w l, y' - y⟫) := by
    intro l
    by_cases hl : l ∈ L
    · obtain ⟨E₁, E₂, h1, h2, h3, h4, h5, h6, h7⟩ :=
        end_pieces (hVconv l) (hVcpt l) (w l) (hext l hl)
      refine ⟨E₁, E₂, h1, h2, h3, h4, fun _ => ⟨h5, h6, fun y hy y' hy' => ?_⟩⟩
      have := h7 y hy y' hy'
      linarith
    · exact ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, empty_subset _, empty_subset _,
        fun h => absurd h hl⟩
  choose E₁ E₂ hE₁ hE₂ hE₁V hE₂V hEL using hpieces
  -- multiplicity
  have hmult : ∀ y y' : Space, (L.filter (fun l => y ∈ E₁ l ∧ y' ∈ E₂ l)).card ≤ 27 := by
    intro y y'
    refine le_trans (Finset.card_le_card ?_) (mult_le_of_netSeparated hρ z w hw hsep L y y')
    intro l hl
    rw [Finset.mem_filter] at hl ⊢
    obtain ⟨hlL, hy1, hy2⟩ := hl
    exact ⟨hlL, (hE₁V l hy1).2, (hE₂V l hy2).2, (hEL l hlL).2.2 y hy1 y' hy2⟩
  have hsumE := sum_mul_volume_le_of_mult L E₁ E₂ (closure U) 27 (fun l _ => hE₁ l)
    (fun l _ => hE₂ l) isClosed_closure.measurableSet
    (fun l _ => (hE₁V l).trans inter_subset_left) (fun l _ => (hE₂V l).trans inter_subset_left)
    hmult
  have hsumV : ∑ l ∈ L, volume (V l) ^ 2 ≤ 27 ^ 3 * volume U ^ 2 := by
    calc ∑ l ∈ L, volume (V l) ^ 2 ≤ ∑ l ∈ L, 27 ^ 2 * (volume (E₁ l) * volume (E₂ l)) := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          obtain ⟨h1, h2, -⟩ := hEL l hl
          calc volume (V l) ^ 2 = volume (V l) * volume (V l) := pow_two _
            _ ≤ (27 * volume (E₁ l)) * (27 * volume (E₂ l)) := mul_le_mul' h1 h2
            _ = 27 ^ 2 * (volume (E₁ l) * volume (E₂ l)) := by ring
      _ = 27 ^ 2 * ∑ l ∈ L, volume (E₁ l) * volume (E₂ l) := by rw [Finset.mul_sum]
      _ ≤ 27 ^ 2 * ((27 : ℕ) * (volume (closure U) * volume (closure U))) := by gcongr
      _ ≤ 27 ^ 2 * ((27 : ℕ) * (volume U * volume U)) := by
          have hcl := volume_closure_le_of_convex hU
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hcl hcl))
      _ = 27 ^ 3 * volume U ^ 2 := by push_cast; ring
  -- the count, in reals
  have hcard : (ncard {j | P j ⊆ U} : ℝ) = ∑ l ∈ L, ((J l).card : ℝ) := by
    rw [ncard_setOf_eq_card]
    rw [Finset.card_eq_sum_card_fiberwise (f := label) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    rw [← Finset.sum_filter_of_ne (p := fun l => (J l).Nonempty)]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      congr 2
      ext j
      simp [hJ, and_comm]
    · intro l _ hne
      have hne' : ((Finset.univ.filter (fun j => P j ⊆ U)).filter
          (fun j => label j = l)).card ≠ 0 := by exact_mod_cast hne
      obtain ⟨j, hj⟩ := Finset.card_ne_zero.mp hne'
      refine ⟨j, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [hJ, hj.1, hj.2]
  have hreal : (ncard {j | P j ⊆ U} : ℝ) * s₀ ^ 2 ≤ (H * D) ^ 2 * ∑ l ∈ L, vol l ^ 2 := by
    rw [hcard, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have h1 := hcount l
    have hJpos : (1 : ℝ) ≤ (J l).card := by
      have := Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
      exact_mod_cast this
    have hs : s₀ ≤ H * D * vol l := by nlinarith
    have hHD : 0 ≤ H * D * vol l := le_trans hs₀.le hs
    calc ((J l).card : ℝ) * s₀ ^ 2 = ((J l).card * s₀) * s₀ := by ring
      _ ≤ (H * D * vol l) * (H * D * vol l) := mul_le_mul h1 hs hs₀.le hHD
      _ = (H * D) ^ 2 * vol l ^ 2 := by ring
  have hvolsq : ∀ l, ENNReal.ofReal (vol l ^ 2) = volume (V l) ^ 2 := by
    intro l
    rw [ENNReal.ofReal_pow (hvol0 l), hvol, ENNReal.ofReal_toReal (hVfin l)]
  calc ENNReal.ofReal ((ncard {j | P j ⊆ U} : ℝ) * s₀ ^ 2)
      ≤ ENNReal.ofReal ((H * D) ^ 2 * ∑ l ∈ L, vol l ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((H * D) ^ 2) * ∑ l ∈ L, volume (V l) ^ 2 := by
        rw [ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg (vol l))]
        simp_rw [hvolsq]
    _ ≤ ENNReal.ofReal ((H * D) ^ 2) * (27 ^ 3 * volume U ^ 2) := by gcongr
    _ = ENNReal.ofReal (27 ^ 3 * (H * D) ^ 2) * volume U ^ 2 := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 27) 3,
          ENNReal.ofReal_ofNat]
        ring

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
