-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatParent.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FibreDichotomy
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalPrismGeometry
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatQuantitative

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FlatParent.lean), namespace renamed.
/-!
# Flat parents

The flat o064 boxes of the fibre of one coarse tube, cut down to the tube, as containers in the
shape of x0210's `LocalFactor` (`normalize_flat_parent`), with the frame helpers it needs.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set MeasureTheory
open scoped ENNReal

/-- An orthonormal frame `e₁, e₂, e₃` with `e₂ ⊥ w`, for unit `e₁, w` that are not parallel. -/
lemma exists_frame_perp {e₁ w : Space} (he₁ : ‖e₁‖ = 1) (hw : ‖w‖ = 1)
    (hnp : |inner ℝ e₁ w| < 1) :
    ∃ e₂ e₃ : Space, Orthonormal ℝ ![e₁, e₂, e₃] ∧ inner ℝ e₂ w = 0 := by
  set u : Space := w - inner ℝ e₁ w • e₁ with hu
  have hu1 : inner ℝ e₁ u = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he₁]; ring
  have hunorm : ‖u‖ ^ 2 = 1 - inner ℝ e₁ w ^ 2 := by
    rw [hu, norm_sub_sq_real, inner_smul_right, norm_smul, he₁, hw, Real.norm_eq_abs,
      real_inner_comm e₁ w, mul_one, sq_abs]
    ring
  have hupos : 0 < ‖u‖ := by
    have h1 : 0 < 1 - inner ℝ e₁ w ^ 2 := by
      have := abs_lt.mp hnp
      nlinarith
    have h2 : 0 < ‖u‖ ^ 2 := by rw [hunorm]; exact h1
    by_contra hle
    have h0 : ‖u‖ = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [h0] at h2; norm_num at h2
  set f : Space := ‖u‖⁻¹ • u with hf
  have hf1 : ‖f‖ = 1 := by
    rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hupos.ne']
  have hef : inner ℝ e₁ f = 0 := by rw [hf, inner_smul_right, hu1, mul_zero]
  have hwdecomp : w = ‖u‖ • f + inner ℝ e₁ w • e₁ := by
    rw [hf, smul_smul, mul_inv_cancel₀ hupos.ne', one_smul, hu]; abel
  -- extend `e₁, f` to an orthonormal basis
  let v3 : Fin 3 → Space := ![e₁, f, 0]
  have hv3 : Orthonormal ℝ (({0, 1} : Set (Fin 3)).domRestrict v3) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict, v3, he₁, hf1, hef, real_inner_comm]
  obtain ⟨B, hB⟩ := hv3.exists_orthonormalBasis_extension_of_card_eq (by simp [Space])
  have hB0 : B 0 = e₁ := by simpa [v3] using hB 0 (by simp)
  have hB1 : B 1 = f := by simpa [v3] using hB 1 (by simp)
  refine ⟨B 2, f, ?_, ?_⟩
  · have hBo := B.orthonormal
    rw [orthonormal_iff_ite] at hBo ⊢
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      first
      | (have := hBo 0 0; rw [hB0] at this; simpa using this)
      | (have := hBo 0 2; rw [hB0] at this; simpa using this)
      | (have := hBo 0 1; rw [hB0, hB1] at this; simpa using this)
      | (have := hBo 2 0; rw [hB0] at this; simpa using this)
      | (have := hBo 2 2; simpa using this)
      | (have := hBo 2 1; rw [hB1] at this; simpa using this)
      | (have := hBo 1 0; rw [hB0, hB1] at this; simpa using this)
      | (have := hBo 1 2; rw [hB1] at this; simpa using this)
      | (have := hBo 1 1; rw [hB1] at this; simpa using this)
  · have h20 : inner ℝ (B 2) e₁ = 0 := by
      have := (orthonormal_iff_ite.mp B.orthonormal) 2 0; rw [hB0] at this; simpa using this
    have h21 : inner ℝ (B 2) f = 0 := by
      have := (orthonormal_iff_ite.mp B.orthonormal) 2 1; rw [hB1] at this; simpa using this
    rw [hwdecomp, inner_add_right, inner_smul_right, h21, inner_smul_right, h20]; ring

/-- Points of a `ρ`-tube are within `ρ` of its axis in every direction orthogonal to it. -/
lemma tube_perp_bound {ρ : ℝ} {z w e : Space} (he : ‖e‖ = 1) (hew : inner ℝ e w = 0)
    {y : Space} (hy : y ∈ Tube ρ z w) : |inner ℝ e (y - z)| < ρ := by
  obtain ⟨p, hp, hyp⟩ := Metric.mem_thickening_iff.mp hy
  rw [segment_unit_eq] at hp
  obtain ⟨t, -, rfl⟩ := hp
  have : inner ℝ e (y - z) = inner ℝ e (y - (z + t • w)) := by
    rw [inner_sub_right, inner_sub_right, inner_add_right, inner_smul_right, hew]; ring
  rw [this]
  calc |inner ℝ e (y - (z + t • w))| ≤ ‖e‖ * ‖y - (z + t • w)‖ := abs_real_inner_le_norm _ _
    _ = dist y (z + t • w) := by rw [he, one_mul, dist_eq_norm]
    _ < ρ := hyp


/-- Coordinates of points of an affine-isometric `factorBox`. -/
lemma affine_box_coords (a b : ℝ) (e : Space ≃ᵃⁱ[ℝ] Space) :
    ∃ f₁ f₂ f₃ : Space, Orthonormal ℝ ![f₁, f₂, f₃] ∧
      ∀ y ∈ e '' factorBox a b, |inner ℝ f₁ (y - e 0)| ≤ a ∧ |inner ℝ f₂ (y - e 0)| ≤ b ∧
        |inner ℝ f₃ (y - e 0)| ≤ 2 := by
  let B₀ := EuclideanSpace.basisFun (Fin 3) ℝ
  let B := B₀.map e.linearIsometryEquiv
  have hB : Orthonormal ℝ ![B 0, B 1, B 2] := by
    convert B.orthonormal using 1
    ext i
    fin_cases i <;> rfl
  refine ⟨B 0, B 1, B 2, hB, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have he (i : Fin 3) : inner ℝ (B i) (e z - e 0) = z i := by
    have hez : e z - e 0 = e.linearIsometryEquiv z := by
      simpa only [vsub_eq_sub, sub_zero] using (e.map_vsub z 0).symm
    rw [hez]
    change inner ℝ (e.linearIsometryEquiv (B₀ i)) (e.linearIsometryEquiv z) = z i
    rw [e.linearIsometryEquiv.inner_map_map, ← OrthonormalBasis.repr_apply_apply]
    rfl
  rw [he 0, he 1, he 2]
  exact hz


open Classical in
/-- **One flat parent.** The flat o064 boxes of the fibre `F` of a unit `ρ`-tube `R`, cut down
to `R`, are containers in the shape of x0210's `LocalFactor`: thin `a` in `e₁`, at most
`min b ρ` in `e₂` (when `b ≥ ρ` the frame is turned so that `e₂ ⊥` the axis of `R`), with the
kept share `G`, its Katz–Tao constant `c`, covering, degree and saturation. Katz–Tao against a
recentred prism also bounds `b ≤ 8 ρ δ^(-ν)`, so `Λ a ≤ 8 δ^(-ν) min b ρ`. -/
theorem normalize_flat_parent {δ ρ ν Λ a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hΛ : 8 ≤ Λ) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    {z w : Space} (hw : ‖w‖ = 1) (F : Finset (Fin n))
    (hFR : ∀ i ∈ F, Tube δ (x i) (v i) ⊆ Tube ρ z w)
    (hδa : δ ≤ a) (hΛab : Λ * a < b) (hb2 : b ≤ 2)
    (hLF : LongFactor ν δ a b (fun j : Fin F.card =>
      Tube δ (x (F.equivFin.symm j)) (v (F.equivFin.symm j)))) :
    ∃ (G : Finset (Fin n)) (c : ℝ) (p : ℕ) (W : Fin p → Set Space)
      (c₀ e₁ e₂ e₃ : Fin p → Space),
      G ⊆ F ∧ δ ^ ν * F.card ≤ G.card ∧ 1 ≤ c ∧
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((G.filter (fun i => Tube δ (x i) (v i) ⊆ U)).card * δ ^ 2) ≤
          ENNReal.ofReal c * volume U) ∧
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (∀ j, W j ⊆ Tube ρ z w ∩ {y | |inner ℝ (e₁ j) (y - c₀ j)| ≤ a ∧
        |inner ℝ (e₂ j) (y - c₀ j)| ≤ min b ρ}) ∧
      (∀ i ∈ G, ∃ j, Tube δ (x i) (v i) ⊆ W j) ∧
      (∀ i ∈ G, (ncard {j | Tube δ (x i) (v i) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
      (∀ j, δ ^ ν * c * a * min b ρ ≤
        (G.filter (fun i => Tube δ (x i) (v i) ⊆ W j)).card * δ ^ 2) ∧
      Λ * a ≤ 8 * δ ^ (-ν) * min b ρ := by
  obtain ⟨k, g, hg, hk, hsize, c, hc1, hKTc, p, W, hshape, hcover, hdeg, hsat⟩ := hLF
  set e : Fin F.card ≃ F := F.equivFin.symm with he
  let idx : Fin k → Fin n := fun i => (e (g i) : Fin n)
  have hidx : Function.Injective idx :=
    fun a b h => hg (e.injective (Subtype.ext h))
  have hidxF : ∀ i, idx i ∈ F := fun i => (e (g i)).2
  set G : Finset (Fin n) := Finset.univ.image idx with hG
  have hGF : G ⊆ F := by
    intro i hi; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi; exact hidxF j
  have hGcard : G.card = k := by
    rw [hG, Finset.card_image_of_injective _ hidx, Finset.card_univ, Fintype.card_fin]
  have hmemG : ∀ i ∈ G, ∃ i', idx i' = i := by
    intro i hi; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi; exact ⟨j, rfl⟩
  -- counting inside a set through `idx`
  have hcount : ∀ U : Set Space, (G.filter (fun i => Tube δ (x i) (v i) ⊆ U)).card =
      ncard {i' : Fin k | Tube δ (x (idx i')) (v (idx i')) ⊆ U} := by
    intro U
    rw [← Set.ncard_coe_finset]
    have himg : (↑(G.filter (fun i => Tube δ (x i) (v i) ⊆ U)) : Set (Fin n)) =
        idx '' {i' | Tube δ (x (idx i')) (v (idx i')) ⊆ U} := by
      ext i
      simp only [Finset.coe_filter, mem_ofPred_eq, mem_image, hG, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, rfl⟩, hj⟩; exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, rfl⟩, hj⟩
    rw [himg, ncard_image_of_injective _ hidx]
  have hKTG : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((G.filter (fun i => Tube δ (x i) (v i) ⊆ U)).card * δ ^ 2) ≤
        ENNReal.ofReal c * volume U := by
    intro U hU; rw [hcount U]; exact hKTc U hU
  -- the boxes, their frames and the cut-down containers
  have hboxes : ∀ j, ∃ (f₁ f₂ f₃ c₁ : Space), Orthonormal ℝ ![f₁, f₂, f₃] ∧
      ∀ y ∈ W j, |inner ℝ f₁ (y - c₁)| ≤ a ∧ |inner ℝ f₂ (y - c₁)| ≤ b := by
    intro j
    obtain ⟨eaff, heW⟩ := hshape j
    obtain ⟨f₁, f₂, f₃, hf, hco⟩ := affine_box_coords a b eaff
    refine ⟨f₁, f₂, f₃, eaff 0, hf, fun y hy => ?_⟩
    rw [heW] at hy
    exact ⟨(hco y hy).1, (hco y hy).2.1⟩
  choose f₁ f₂ f₃ c₁ hf hbox using hboxes
  let W' : Fin p → Set Space := fun j => W j ∩ Tube ρ z w
  have hGR : ∀ i ∈ G, Tube δ (x i) (v i) ⊆ Tube ρ z w := fun i hi => hFR i (hGF hi)
  have hcountW' : ∀ j, (G.filter (fun i => Tube δ (x i) (v i) ⊆ W' j)).card =
      (G.filter (fun i => Tube δ (x i) (v i) ⊆ W j)).card := by
    intro j
    congr 1
    ext i
    simp only [Finset.mem_filter, W']
    constructor
    · rintro ⟨hi, h⟩; exact ⟨hi, h.trans inter_subset_left⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, subset_inter h (hGR i hi)⟩
  have hsatW : ∀ j, δ ^ ν * c * a * b ≤
      (G.filter (fun i => Tube δ (x i) (v i) ⊆ W' j)).card * δ ^ 2 := by
    intro j
    rw [hcountW' j, hcount (W j)]
    exact hsat j
  have ha0 : 0 < a := hδ.trans_le hδa
  have hb0 : 0 < b := by nlinarith
  have hδν : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
  have hδnν : 1 ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcover' : ∀ i ∈ G, ∃ j, Tube δ (x i) (v i) ⊆ W' j := by
    intro i hi
    obtain ⟨i', rfl⟩ := hmemG i hi
    obtain ⟨j, hj⟩ := hcover i'
    exact ⟨j, subset_inter hj (hGR _ hi)⟩
  have hdeg' : ∀ i ∈ G, (ncard {j | Tube δ (x i) (v i) ⊆ W' j} : ℝ) ≤ δ ^ (-ν) := by
    intro i hi
    obtain ⟨i', rfl⟩ := hmemG i hi
    refine le_trans ?_ (hdeg i')
    exact_mod_cast ncard_le_ncard
      (fun j (hj : Tube δ (x (idx i')) (v (idx i')) ⊆ W' j) => hj.trans inter_subset_left)
      (toFinite _)
  -- some kept tube lies in each container
  have hnonempty : ∀ j, ∃ i ∈ G, Tube δ (x i) (v i) ⊆ W' j := by
    intro j
    by_contra hno
    simp only [not_exists, not_and] at hno
    have h0 : (G.filter (fun i => Tube δ (x i) (v i) ⊆ W' j)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun i hi h => hno i hi h
    have hs := hsatW j
    rw [h0, Nat.cast_zero, zero_mul] at hs
    have hpos : 0 < δ ^ ν * c * a * b := by positivity
    linarith
  by_cases hbρ : b < ρ
  · -- containers keep the box frame
    have hmin : min b ρ = b := min_eq_left hbρ.le
    refine ⟨G, c, p, W', c₁, f₁, f₂, f₃, hGF, ?_, hc1, hKTG, hf, ?_, hcover', hdeg', ?_, ?_⟩
    · rw [hGcard]; exact hsize
    · intro j y hy
      refine ⟨hy.2, ?_⟩
      rw [hmin]
      exact hbox j y hy.1
    · intro j; rw [hmin]; exact hsatW j
    · rw [hmin]
      nlinarith
  · -- turn the frame so that its second vector is orthogonal to the axis of `R`
    have hmin : min b ρ = ρ := min_eq_right (not_lt.mp hbρ)
    have hframes : ∀ j, ∃ g₂ g₃ : Space, Orthonormal ℝ ![f₁ j, g₂, g₃] ∧ inner ℝ g₂ w = 0 := by
      intro j
      obtain ⟨i, hiG, hiW⟩ := hnonempty j
      have hf₁ : ‖f₁ j‖ = 1 := by simpa using (hf j).norm_eq_one 0
      -- the tube's direction is almost orthogonal to `f₁ j`
      have hxi : x i ∈ W j := (hiW.trans inter_subset_left) (left_mem_tube hδ _ _)
      have hxvi : x i + v i ∈ W j := (hiW.trans inter_subset_left) (right_mem_tube hδ _ _)
      have hproj : |inner ℝ (f₁ j) (v i)| ≤ 2 * a :=
        axis_projection_of_endpoints (hbox j _ hxi).1 (hbox j _ hxvi).1
      have hnear := axes_near_of_tube_subset hδ (hv i) hw (hGR i hiG)
      have hlt : |inner ℝ (f₁ j) w| < 1 := by
        have hb2' : a < 1 / 4 := by nlinarith
        rcases hnear with h | h
        · have : |inner ℝ (f₁ j) w| ≤ |inner ℝ (f₁ j) (v i)| + ‖v i - w‖ := by
            have e1 : inner ℝ (f₁ j) w = inner ℝ (f₁ j) (v i) - inner ℝ (f₁ j) (v i - w) := by
              rw [inner_sub_right]; ring
            rw [e1]
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            exact (abs_real_inner_le_norm _ _).trans (by rw [hf₁, one_mul])
          linarith
        · have : |inner ℝ (f₁ j) w| ≤ |inner ℝ (f₁ j) (v i)| + ‖v i + w‖ := by
            have e1 : inner ℝ (f₁ j) w = inner ℝ (f₁ j) (v i + w) - inner ℝ (f₁ j) (v i) := by
              rw [inner_add_right]; ring
            have h1 : |inner ℝ (f₁ j) (v i + w)| ≤ ‖v i + w‖ :=
              (abs_real_inner_le_norm _ _).trans (by rw [hf₁, one_mul])
            have h2 := abs_sub (inner ℝ (f₁ j) (v i + w)) (inner ℝ (f₁ j) (v i))
            rw [e1]
            linarith
          linarith
      exact exists_frame_perp hf₁ hw hlt
    choose g₂ g₃ hg using hframes
    let c₂ : Fin p → Space := fun j => c₁ j + inner ℝ (g₂ j) (z - c₁ j) • g₂ j
    have hcont : ∀ j, W' j ⊆ Tube ρ z w ∩ {y | |inner ℝ (f₁ j) (y - c₂ j)| ≤ a ∧
        |inner ℝ (g₂ j) (y - c₂ j)| ≤ ρ} := by
      intro j y hy
      have hon := (hg j).1
      have h12 : inner ℝ (f₁ j) (g₂ j) = 0 := by
        simpa using (orthonormal_iff_ite.mp hon) 0 1
      have h22 : inner ℝ (g₂ j) (g₂ j) = 1 := by
        simpa using (orthonormal_iff_ite.mp hon) 1 1
      have hg₂ : ‖g₂ j‖ = 1 := by simpa using hon.norm_eq_one 1
      refine ⟨hy.2, ?_, ?_⟩
      · have : inner ℝ (f₁ j) (y - c₂ j) = inner ℝ (f₁ j) (y - c₁ j) := by
          simp only [c₂, inner_sub_right, inner_add_right, inner_smul_right, h12]; ring
        rw [this]; exact (hbox j y hy.1).1
      · have : inner ℝ (g₂ j) (y - c₂ j) = inner ℝ (g₂ j) (y - z) := by
          simp only [c₂, inner_sub_right, inner_add_right, inner_smul_right, h22]; ring
        rw [this]
        exact (tube_perp_bound hg₂ (hg j).2 hy.2).le
    -- `b ≤ 8 ρ δ^(-ν)` from Katz–Tao against a recentred prism
    have hbbound : b ≤ 8 * ρ * δ ^ (-ν) := by
      have hp0 : 0 < p := by
        obtain ⟨i, hi⟩ : G.Nonempty := by
          rw [← Finset.card_pos, hGcard]; exact hk
        obtain ⟨j, -⟩ := hcover' i hi
        exact j.pos
      set j₀ : Fin p := ⟨0, hp0⟩
      have hon := (hg j₀).1
      let Pr := Prism a ρ (c₂ j₀ - inner ℝ (g₃ j₀) (c₂ j₀) • g₃ j₀) (f₁ j₀) (g₂ j₀) (g₃ j₀)
      have hsubPr : ∀ i ∈ G, Tube δ (x i) (v i) ⊆ W' j₀ → Tube δ (x i) (v i) ⊆ Pr := by
        intro i hi hiW y hy
        apply prism_recenter_longitudinal _ _ _ _ hon
        exact ⟨hball i hy, (hcont j₀ (hiW hy)).2⟩
      have hle : (G.filter (fun i => Tube δ (x i) (v i) ⊆ W' j₀)).card ≤
          (G.filter (fun i => Tube δ (x i) (v i) ⊆ Pr)).card := by
        apply Finset.card_le_card
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, hsubPr i hi.1 hi.2⟩
      have hKTPr := hKTG Pr (prism_convex _ _ _ _ _ _)
      rw [prism_volume ha0.le hρ.le _ _ _ _ hon, ← ENNReal.ofReal_mul (by linarith)] at hKTPr
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hKTPr
      have hs := hsatW j₀
      have hle' : ((G.filter (fun i => Tube δ (x i) (v i) ⊆ W' j₀)).card : ℝ) * δ ^ 2 ≤
          ((G.filter (fun i => Tube δ (x i) (v i) ⊆ Pr)).card : ℝ) * δ ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (sq_nonneg δ)
      have key : δ ^ ν * c * a * b ≤ c * (8 * a * ρ) := by linarith
      have hca : 0 < c * a := by positivity
      have key2 : δ ^ ν * b ≤ 8 * ρ := by
        have : (δ ^ ν * b) * (c * a) ≤ (8 * ρ) * (c * a) := by nlinarith
        exact le_of_mul_le_mul_right this hca
      calc b = δ ^ (-ν) * (δ ^ ν * b) := by
            rw [← mul_assoc, ← Real.rpow_add hδ]; simp
        _ ≤ δ ^ (-ν) * (8 * ρ) := mul_le_mul_of_nonneg_left key2 (by positivity)
        _ = 8 * ρ * δ ^ (-ν) := by ring
    refine ⟨G, c, p, W', c₂, f₁, g₂, g₃, hGF, ?_, hc1, hKTG, fun j => (hg j).1, ?_, hcover',
      hdeg', ?_, ?_⟩
    · rw [hGcard]; exact hsize
    · intro j; rw [hmin]; exact hcont j
    · intro j
      rw [hmin]
      have := hsatW j
      have hρb : ρ ≤ b := not_lt.mp hbρ
      have : δ ^ ν * c * a * ρ ≤ δ ^ ν * c * a * b := by
        have : 0 ≤ δ ^ ν * c * a := by positivity
        nlinarith
      linarith
    · rw [hmin]
      nlinarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
