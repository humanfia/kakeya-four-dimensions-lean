-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.Geom.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Boxes crossed end to end

Elementary geometry of the boxes `P a b c z e` of the frozen statement:

* `tube_slab_subset_box`: an open convex set meeting a box, whose intersection with the
  boundary of the box lies on the two end faces, lies inside the box within the end slab
  (and inside the open box within the open end slab);
* `crossing_widen`: widening the box in its middle direction keeps the end-face crossing
  property, and the convex set meets the wider box only inside the narrow one;
* `halve_mid`: every point of a box is within a quarter of the middle width of the box with
  half the middle width;
* `axis_sq_le`: the alignment of a frame with a direction survives a small change of the
  direction.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains.Geom

open Set Metric

local notation "V3" => EuclideanSpace ℝ (Fin 3)

/-- The closed box of the frozen statement (coordinates in the frame `e` around `z`). -/
def box (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) : Set V3 :=
  {p | |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2}

/-- The open box. -/
def obox (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) : Set V3 :=
  {p | |e (p - z) 0| < a / 2 ∧ |e (p - z) 1| < b / 2 ∧ |e (p - z) 2| < c / 2}

theorem continuous_coord (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) (k : Fin 3) :
    Continuous fun p : V3 => e (p - z) k :=
  (EuclideanSpace.proj k).continuous.comp (e.continuous.comp (continuous_id.sub continuous_const))

theorem isClosed_box (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) : IsClosed (box a b c z e) := by
  have h := fun k => (continuous_coord z e k).abs
  exact ((isClosed_le (h 0) continuous_const).inter
    ((isClosed_le (h 1) continuous_const).inter (isClosed_le (h 2) continuous_const)))

theorem isOpen_obox (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) : IsOpen (obox a b c z e) := by
  have h := fun k => (continuous_coord z e k).abs
  exact ((isOpen_lt (h 0) continuous_const).inter
    ((isOpen_lt (h 1) continuous_const).inter (isOpen_lt (h 2) continuous_const)))

theorem obox_subset_box (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) :
    obox a b c z e ⊆ box a b c z e :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

theorem obox_subset_interior (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) :
    obox a b c z e ⊆ interior (box a b c z e) :=
  interior_maximal (obox_subset_box a b c z e) (isOpen_obox a b c z e)

/-- Coordinates after a shift given in the frame. -/
theorem coord_shift (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) (p u : V3) (k : Fin 3) :
    e (p + e.symm u - z) k = e (p - z) k + u k := by
  have : p + e.symm u - z = (p - z) + e.symm u := by abel
  rw [this, map_add, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem single_apply_ne {k j : Fin 3} (h : j ≠ k) (t : ℝ) :
    (EuclideanSpace.single k t : V3) j = 0 := by
  rw [EuclideanSpace.single_apply, ite_eq_right_iff.mpr (fun h' => absurd h' h)]

theorem single_apply_self (k : Fin 3) (t : ℝ) : (EuclideanSpace.single k t : V3) k = t := by
  rw [EuclideanSpace.single_apply, if_pos rfl]

theorem norm_symm_single (e : V3 ≃ₗᵢ[ℝ] V3) (k : Fin 3) (t : ℝ) :
    ‖e.symm (EuclideanSpace.single k t)‖ = |t| := by
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_single, Real.norm_eq_abs]

/-- A point of the interior of a box has all its coordinates strictly inside. -/
theorem interior_box_subset (a b c : ℝ) (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) :
    interior (box a b c z e) ⊆ obox a b c z e := by
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  have hin : ∀ q, dist q p < r → q ∈ box a b c z e :=
    fun q hq => interior_subset (hball (Metric.mem_ball.mpr hq))
  -- moving by `r/2` along the axis `k`, away from the centre, leaves the box
  have key : ∀ (k : Fin 3) (B : ℝ), (∀ q ∈ box a b c z e, |e (q - z) k| ≤ B) →
      |e (p - z) k| < B := by
    intro k B hB
    by_contra hcon
    push_neg at hcon
    set s : ℝ := if 0 ≤ e (p - z) k then r / 2 else -(r / 2) with hs
    have hsabs : |s| = r / 2 := by
      rw [hs]; split_ifs <;> simp [abs_of_pos (half_pos hr)]
    have hq : p + e.symm (EuclideanSpace.single k s) ∈ box a b c z e := by
      apply hin
      rw [dist_eq_norm, add_sub_cancel_left, norm_symm_single, hsabs]
      linarith
    have h1 := hB _ hq
    rw [coord_shift, single_apply_self] at h1
    have h2 : |e (p - z) k + s| = |e (p - z) k| + r / 2 := by
      rw [hs]
      split_ifs with h
      · rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]
      · push_neg at h
        rw [abs_of_neg h, abs_of_neg (by linarith)]
        ring
    linarith
  exact ⟨key 0 (a / 2) (fun q hq => hq.1), key 1 (b / 2) (fun q hq => hq.2.1),
    key 2 (c / 2) (fun q hq => hq.2.2)⟩

/-- A point of a box which is not in the open box lies on the boundary. -/
theorem mem_frontier_of_not_obox {a b c : ℝ} {z : V3} {e : V3 ≃ₗᵢ[ℝ] V3} {p : V3}
    (hp : p ∈ box a b c z e) (hn : p ∉ obox a b c z e) : p ∈ frontier (box a b c z e) := by
  rw [frontier, (isClosed_box a b c z e).closure_eq]
  exact ⟨hp, fun h => hn (interior_box_subset a b c z e h)⟩

/-- Points of an open set can be moved strictly into the end slab without changing their
first two coordinates. -/
theorem exists_inward {T : Set V3} (hTo : IsOpen T) {c : ℝ} (hc : 0 < c) {z : V3}
    {e : V3 ≃ₗᵢ[ℝ] V3} {p : V3} (hp : p ∈ T) (hp2 : |e (p - z) 2| ≤ c / 2) :
    ∃ q ∈ T, e (q - z) 0 = e (p - z) 0 ∧ e (q - z) 1 = e (p - z) 1 ∧ |e (q - z) 2| < c / 2 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hTo p hp
  set s : ℝ := min (1 / 2) (r / (c + 1)) with hs_def
  have hs0 : 0 < s := lt_min (by norm_num) (div_pos hr (by linarith))
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hsr : s * (c + 1) ≤ r := by
    have := min_le_right (1 / 2 : ℝ) (r / (c + 1))
    rw [← hs_def] at this
    calc s * (c + 1) ≤ r / (c + 1) * (c + 1) := by gcongr
      _ = r := by field_simp
  set t : ℝ := -(s * e (p - z) 2) with ht
  refine ⟨p + e.symm (EuclideanSpace.single 2 t), hball ?_, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_symm_single, ht, abs_neg,
      abs_mul, abs_of_pos hs0]
    calc s * |e (p - z) 2| ≤ s * (c / 2) := by gcongr
      _ < s * (c + 1) := by gcongr; linarith
      _ ≤ r := hsr
  · rw [coord_shift, single_apply_ne (by decide), add_zero]
  · rw [coord_shift, single_apply_ne (by decide), add_zero]
  · rw [coord_shift, single_apply_self, ht]
    have : e (p - z) 2 + -(s * e (p - z) 2) = (1 - s) * e (p - z) 2 := by ring
    rw [this, abs_mul, abs_of_pos (by linarith)]
    calc (1 - s) * |e (p - z) 2| ≤ (1 - s) * (c / 2) := by gcongr
      _ < c / 2 := by nlinarith

/-- An open convex set meeting a box only through its end faces lies in the box within the
end slab, and in the open box within the open end slab. -/
theorem tube_slab_subset_box {a b c : ℝ} {z : V3} {e : V3 ≃ₗᵢ[ℝ] V3} {T : Set V3}
    (hTo : IsOpen T) (hTc : Convex ℝ T) (hc : 0 < c)
    (hne : (T ∩ box a b c z e).Nonempty)
    (hfr : ∀ p ∈ T ∩ frontier (box a b c z e), |e (p - z) 2| = c / 2) :
    (∀ p ∈ T, |e (p - z) 2| < c / 2 → p ∈ obox a b c z e) ∧
    (∀ p ∈ T, |e (p - z) 2| ≤ c / 2 → p ∈ box a b c z e) := by
  set W : Set V3 := T ∩ {p | |e (p - z) 2| < c / 2} with hW
  have hWo : IsOpen W :=
    hTo.inter (isOpen_lt (continuous_coord z e 2).abs continuous_const)
  have hWc : Convex ℝ W := by
    refine hTc.inter ?_
    have : {p : V3 | |e (p - z) 2| < c / 2} =
        (fun p : V3 => e (p - z) 2) ⁻¹' Set.Ioo (-(c / 2)) (c / 2) := by
      ext p; simp [abs_lt]
    rw [this]
    have hlin : (fun p : V3 => e (p - z) 2) =
        fun p => (EuclideanSpace.proj (2 : Fin 3) : V3 →L[ℝ] ℝ) (e.toLinearEquiv p) -
          (EuclideanSpace.proj (2 : Fin 3) : V3 →L[ℝ] ℝ) (e z) := by
      funext p; simp [map_sub]
    rw [hlin]
    exact (convex_Ioo _ _).affine_preimage
      ((((EuclideanSpace.proj (2 : Fin 3) : V3 →L[ℝ] ℝ).toLinearMap.comp
        e.toLinearEquiv.toLinearMap).toAffineMap) -
        AffineMap.const ℝ V3 ((EuclideanSpace.proj (2 : Fin 3) : V3 →L[ℝ] ℝ) (e z)))
  -- inside `W`, a point of the box lies in the open box
  have hdich : ∀ p ∈ W, p ∈ box a b c z e → p ∈ obox a b c z e := by
    intro p hpW hpB
    by_contra hn
    have := hfr p ⟨hpW.1, mem_frontier_of_not_obox hpB hn⟩
    have h2 : |e (p - z) 2| < c / 2 := hpW.2
    linarith
  have hsub : W ⊆ obox a b c z e ∪ (box a b c z e)ᶜ := by
    intro p hp
    by_cases hB : p ∈ box a b c z e
    · exact Or.inl (hdich p hp hB)
    · exact Or.inr hB
  have hdisj : Disjoint (obox a b c z e) (box a b c z e)ᶜ :=
    Set.disjoint_compl_right_iff_subset.mpr (obox_subset_box a b c z e)
  have hmeet : (W ∩ obox a b c z e).Nonempty := by
    obtain ⟨p₀, hp₀T, hp₀B⟩ := hne
    obtain ⟨q, hqT, hq0, hq1, hq2⟩ := exists_inward hTo hc hp₀T hp₀B.2.2
    have hqB : q ∈ box a b c z e := ⟨hq0 ▸ hp₀B.1, hq1 ▸ hp₀B.2.1, hq2.le⟩
    exact ⟨q, ⟨hqT, hq2⟩, hdich q ⟨hqT, hq2⟩ hqB⟩
  have hWobox : W ⊆ obox a b c z e :=
    hWc.isPreconnected.subset_left_of_subset_union (isOpen_obox a b c z e)
      (isClosed_box a b c z e).isOpen_compl hdisj hsub hmeet
  refine ⟨fun p hp h2 => hWobox ⟨hp, h2⟩, ?_⟩
  intro p hp h2
  obtain ⟨q, hqT, hq0, hq1, hq2⟩ := exists_inward hTo hc hp h2
  have hq := hWobox ⟨hqT, hq2⟩
  exact ⟨(hq0 ▸ hq.1).le, (hq1 ▸ hq.2.1).le, h2⟩

theorem box_mono_mid {a b b' c : ℝ} (hb : b ≤ b') (z : V3) (e : V3 ≃ₗᵢ[ℝ] V3) :
    box a b c z e ⊆ box a b' c z e :=
  fun _ hp => ⟨hp.1, hp.2.1.trans (by linarith), hp.2.2⟩

/-- Widening the middle side of a box crossed end to end by an open convex set. -/
theorem crossing_widen {a b b' c : ℝ} {z : V3} {e : V3 ≃ₗᵢ[ℝ] V3} {T : Set V3}
    (hTo : IsOpen T) (hTc : Convex ℝ T) (hc : 0 < c) (hb : b ≤ b')
    (hne : (T ∩ box a b c z e).Nonempty)
    (hfr : ∀ p ∈ T ∩ frontier (box a b c z e), |e (p - z) 2| = c / 2) :
    (∀ p ∈ T ∩ frontier (box a b' c z e), |e (p - z) 2| = c / 2) ∧
    T ∩ box a b' c z e ⊆ box a b c z e := by
  obtain ⟨hopen, hclosed⟩ := tube_slab_subset_box hTo hTc hc hne hfr
  refine ⟨?_, fun p hp => hclosed p hp.1 hp.2.2.2⟩
  rintro p ⟨hpT, hpF⟩
  have hpB : p ∈ box a b' c z e := by
    have := frontier_subset_closure hpF
    rwa [(isClosed_box a b' c z e).closure_eq] at this
  by_contra hne2
  have hlt : |e (p - z) 2| < c / 2 := lt_of_le_of_ne hpB.2.2 hne2
  have hpo := hopen p hpT hlt
  have hpo' : p ∈ obox a b' c z e := ⟨hpo.1, hpo.2.1.trans_le (by linarith), hpo.2.2⟩
  exact hpF.2 (obox_subset_interior a b' c z e hpo')

/-- Halving the middle coordinate moves a point of a box into the box of half the middle
width, by at most a quarter of the middle width. -/
theorem halve_mid {a b c : ℝ} {z : V3} {e : V3 ≃ₗᵢ[ℝ] V3} {p : V3}
    (hp : p ∈ box a b c z e) :
    ∃ q ∈ box a (b / 2) c z e, dist p q ≤ b / 4 := by
  refine ⟨p + e.symm (EuclideanSpace.single 1 (-(e (p - z) 1 / 2))), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [coord_shift, single_apply_ne (by decide), add_zero]; exact hp.1
  · rw [coord_shift, single_apply_self]
    have : e (p - z) 1 + -(e (p - z) 1 / 2) = e (p - z) 1 / 2 := by ring
    rw [this, abs_div, abs_two]
    linarith [hp.2.1]
  · rw [coord_shift, single_apply_ne (by decide), add_zero]; exact hp.2.2
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_symm_single, abs_neg, abs_div, abs_two]
    linarith [hp.2.1]

theorem sq_coord_le_norm_sq (u : V3) : u 0 ^ 2 + u 1 ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (u 2)]

/-- The alignment of the frame with a direction is stable under small changes of the
direction. -/
theorem axis_sq_le {e : V3 ≃ₗᵢ[ℝ] V3} {w w' : V3} {A B : ℝ}
    (h : e w' 0 ^ 2 + e w' 1 ^ 2 ≤ A ^ 2) (hd : ‖w - w'‖ ≤ B) (hB : 0 ≤ B) :
    e w 0 ^ 2 + e w 1 ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
  have hsplit : ∀ k, e w k = e w' k + e (w - w') k := by
    intro k
    rw [map_sub]
    simp
  have hdd := sq_coord_le_norm_sq (e (w - w'))
  rw [LinearIsometryEquiv.norm_map] at hdd
  have hB2 : ‖w - w'‖ ^ 2 ≤ B ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [hsplit 0, hsplit 1]
  nlinarith [sq_nonneg (e w' 0 - e (w - w') 0), sq_nonneg (e w' 1 - e (w - w') 1)]

end WangZahlLot.Obl.wz_coarse_tube_grains.Geom
