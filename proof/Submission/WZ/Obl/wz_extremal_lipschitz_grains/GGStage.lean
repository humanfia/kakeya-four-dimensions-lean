-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGGlue

/-!
# The slab stage of the global grains

Prop. 4.1, Step 1 of the sticky Kakeya paper, after the fibre has been rescaled: choose the
tube `q0` of property (P), a thick block of slabs carrying a fixed fraction of the mass, and in
every slab of the block met by `q0` the AD direction `perpDir w0 (V p_z)` given by the plane
map at a point `p_z` of the shading of `q0`. These directions vary in a Lipschitz way.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- A point of a fine tube in a coarse tube: the plane map is almost orthogonal to the axis. -/
theorem inner_V_axis_le {τ ρ0 : ℝ} (hτ : 0 < τ) (hρ01 : ρ0 ≤ 1 / 100)
    {x v z0 w0 V : Space} (hv : ‖v‖ = 1) (hw0 : ‖w0‖ = 1) (hV : ‖V‖ = 1)
    (hT : tube τ x v ⊆ tube ρ0 z0 w0) (hVv : |⟪v, V⟫| ≤ τ) :
    |⟪V, w0⟫| ≤ τ + 4 * ρ0 := by
  have hd := dir_close_of_subset hτ hv hw0 hT
  have ho := orDir_sub_le hv hw0 (by linarith) hd
  have h1 : |⟪V, orDir w0 v⟫| ≤ τ := by
    rw [orDir]; split_ifs
    · rw [real_inner_comm]; exact hVv
    · rw [inner_neg_right, abs_neg, real_inner_comm]; exact hVv
  have e : ⟪V, w0⟫ = ⟪V, orDir w0 v⟫ - ⟪V, orDir w0 v - w0⟫ := by
    rw [inner_sub_right]; ring
  have h2 := abs_real_inner_le_norm V (orDir w0 v - w0)
  rw [hV, one_mul] at h2
  rw [e]
  calc |⟪V, orDir w0 v⟫ - ⟪V, orDir w0 v - w0⟫| ≤ |⟪V, orDir w0 v⟫| + |⟪V, orDir w0 v - w0⟫| :=
        abs_sub _ _
    _ ≤ τ + 4 * ρ0 := by linarith

/-- A fine tube in a coarse tube is transverse to the slabs. -/
theorem inner_axis_ge {τ ρ0 : ℝ} (hτ : 0 < τ) (hρ01 : ρ0 ≤ 1 / 100)
    {x v z0 w0 : Space} (hv : ‖v‖ = 1) (hw0 : ‖w0‖ = 1)
    (hT : tube τ x v ⊆ tube ρ0 z0 w0) : 1 / 2 ≤ |⟪v, w0⟫| := by
  have hd := dir_close_of_subset hτ hv hw0 hT
  have ho := orDir_sub_le hv hw0 (by linarith) hd
  have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
  have h1 : |⟪orDir w0 v, w0⟫| = |⟪v, w0⟫| := by
    rw [orDir]; split_ifs
    · rfl
    · rw [inner_neg_left, abs_neg]
  have e : ⟪orDir w0 v, w0⟫ = 1 + ⟪orDir w0 v - w0, w0⟫ := by rw [inner_sub_left, hww]; ring
  have h2 := abs_real_inner_le_norm (orDir w0 v - w0) w0
  rw [hw0, mul_one] at h2
  rw [← h1, e, abs_le] at *
  rw [abs_of_pos (by linarith [h2.1])]
  linarith [h2.1]

/-- The slab stage: a tube with property (P), a thick block of slabs, and AD directions. -/
theorem slab_stage {σ C L τ ρ0 b τ' εF : ℝ} (hτ : 0 < τ) (hτρ : τ ≤ ρ0) (hρ0 : ρ0 ≤ 1 / 100)
    (hb : 0 < b) (hb1 : b ≤ 1) (hσ : σ ≤ 1) (hC : 0 ≤ C) (hL : 0 ≤ L) (hτ'0 : 0 < τ')
    {E : Set Space} {V : Space → Space}
    (hV1 : ∀ p ∈ E, ‖V p‖ = 1)
    (hVL : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ L * dist p q)
    (hloc : ∀ p ∈ E, Covering ((5 * ρ0) ^ 2) (1 - σ) C
      ((fun q => ⟪V p, q⟫) '' (E ∩ ball p (5 * ρ0))))
    {z0 w0 c0 : Space} (hw0 : ‖w0‖ = 1)
    {n : ℕ} {x v : Fin n → Space} {Y' : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1)
    {m : ℕ} (ι : Fin m → Fin n)
    (hYE : ∀ q, Y' (ι q) ⊆ E) (hYT : ∀ q, Y' (ι q) ⊆ tube τ (x (ι q)) (v (ι q)))
    (hTlev : ∀ q, tube τ (x (ι q)) (v (ι q)) ⊆ tube ρ0 z0 w0)
    (hVv : ∀ q, ∀ p ∈ Y' (ι q), |⟪v (ι q), V p⟫| ≤ τ)
    {Xh Vh : Fin m → Space}
    (hFam : Family εF τ' m Xh Vh (fun q => resc w0 c0 (1 / 100 / ρ0) b '' Y' (ι q)))
    (hVhw : ∀ q, 1 / 2 ≤ |⟪Vh q, w0⟫|)
    (hτ'h : τ' ≤ b * ρ0)
    {N : ℕ} (hN : 1 ≤ N) (hNh : (N : ℝ) * (b * ρ0) ≤ 1) :
    ∃ (q0 : Fin m) (k : ℤ) (Zb : Finset ℤ) (Vhat : ℤ → Space),
      (N : ℝ) * (b * ρ0) / 7 * (τ' ^ εF * τ' ^ εF * m * τ' ^ 2 / 11648) ≤
        ∑ q, (volume (resc w0 c0 (1 / 100 / ρ0) b '' Y' (ι q) ∩
          slabsOf w0 (b * ρ0) (resc w0 c0 (1 / 100 / ρ0) b '' Y' (ι q0)) ∩
          slab w0 ((N : ℝ) * (b * ρ0)) k)).toReal ∧
      (∀ q, ∀ p ∈ resc w0 c0 (1 / 100 / ρ0) b '' Y' (ι q) ∩
          slabsOf w0 (b * ρ0) (resc w0 c0 (1 / 100 / ρ0) b '' Y' (ι q0)) ∩
          slab w0 ((N : ℝ) * (b * ρ0)) k, ∃ z ∈ Zb, p ∈ slab w0 (b * ρ0) z) ∧
      (∀ z ∈ Zb, ‖Vhat z‖ = 1 ∧ ⟪Vhat z, w0⟫ = 0 ∧
        Covering (b * ρ0) (1 - σ) (4 ^ (1 - σ) * C)
          ((fun q => ⟪Vhat z, q⟫) ''
            (resc w0 c0 (1 / 100 / ρ0) b '' (⋃ q, Y' (ι q)) ∩ slab w0 (b * ρ0) z))) ∧
      (∀ z ∈ Zb, ∀ z' ∈ Zb,
        ‖Vhat z - Vhat z'‖ ≤ 8 * L * (2 * (ρ0 * (|(z : ℝ) - z'| + 1)) + 6 * τ)) ∧
      (∀ z ∈ Zb, ∀ z' ∈ Zb, |(z : ℝ) - z'| ≤ N + 1) := by
  classical
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le hτ hτρ
  set h : ℝ := b * ρ0 with hh_def
  have hh : 0 < h := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh1 : h ≤ 1 := by nlinarith
  set H : ℝ := (N : ℝ) * h with hH_def
  have hH : 0 < H := by positivity
  set φ := resc w0 c0 (1 / 100 / ρ0) b with hφ
  obtain ⟨hm, -, hball, -, hYm, hYsub, -⟩ := id hFam
  -- property (P)
  obtain ⟨q0, hq0⟩ := slab_selection hτ'0 hτ'h hh1 hFam hw0 hVhw
  set Y1 : Fin m → Set Space := fun q => φ '' Y' (ι q) ∩ slabsOf w0 h (φ '' Y' (ι q0))
    with hY1
  have hY1m : ∀ q, MeasurableSet (Y1 q) := fun q =>
    (hYm q).inter (measurableSet_slabsOf w0 h _)
  have hY1b : ∀ q, Y1 q ⊆ ball 0 1 := fun q =>
    inter_subset_left.trans ((hYsub q).trans (hball q))
  -- a thick block of slabs
  obtain ⟨k, hk⟩ := thick_slab_selection hH hNh hY1m hY1b hw0
  -- the slabs of the block met by `q0`
  set Zb := (Finset.Icc (-(⌈1 / h⌉ + 1)) (⌈1 / h⌉ + 1)).filter
    (fun z => (φ '' Y' (ι q0) ∩ slab w0 h z).Nonempty ∧ (slab w0 h z ∩ slab w0 H k).Nonempty)
    with hZb
  have hex : ∀ z ∈ Zb, ∃ p ∈ Y' (ι q0), φ p ∈ slab w0 h z := by
    intro z hz
    obtain ⟨-, ⟨_, ⟨p, hp, rfl⟩, hps⟩, -⟩ := Finset.mem_filter.mp hz
    exact ⟨p, hp, hps⟩
  choose! pz hpzY hpzs using hex
  have hpzE : ∀ z ∈ Zb, pz z ∈ E := fun z hz => hYE q0 (hpzY z hz)
  have hVw : ∀ z ∈ Zb, |⟪V (pz z), w0⟫| ≤ 5 * ρ0 := by
    intro z hz
    have := inner_V_axis_le hτ hρ0 (hv (ι q0)) hw0 (hV1 _ (hpzE z hz)) (hTlev q0)
      (hVv q0 _ (hpzY z hz))
    linarith
  have hVw' : ∀ z ∈ Zb, |⟪V (pz z), w0⟫| ≤ 1 / 2 := fun z hz => (hVw z hz).trans (by linarith)
  refine ⟨q0, k, Zb, fun z => perpDir w0 (V (pz z)), ?_, ?_, ?_, ?_, ?_⟩
  · -- mass
    have h1 : H / 7 * (τ' ^ εF * τ' ^ εF * m * τ' ^ 2 / 11648) ≤
        H / 7 * ∑ q, (volume (Y1 q)).toReal :=
      mul_le_mul_of_nonneg_left hq0 (by positivity)
    exact h1.trans hk
  · -- every point lies in a slab of the block met by `q0`
    intro q p hp
    obtain ⟨⟨hpY, hpS⟩, hpk⟩ := hp
    refine ⟨slabIndex w0 h p, Finset.mem_filter.mpr ⟨?_, hpS, ⟨p, mem_slab_slabIndex hh p, hpk⟩⟩,
      mem_slab_slabIndex hh p⟩
    exact slabIndex_mem_Icc hw0 hh ((hYsub q).trans (hball q) hpY)
  · -- the AD directions
    intro z hz
    refine ⟨norm_perpDir (hV1 _ (hpzE z hz)) hw0 (hVw' z hz), inner_perpDir_self hw0, ?_⟩
    have hFE : (⋃ q, Y' (ι q)) ⊆ E := iUnion_subset hYE
    have hFt : (⋃ q, Y' (ι q)) ⊆ tube ρ0 z0 w0 :=
      iUnion_subset fun q => (hYT q).trans (hTlev q)
    exact slab_covering hρ0pos hρ0 hb hw0 hFE hFt (mem_iUnion.mpr ⟨q0, hpzY z hz⟩)
      (hV1 _ (hpzE z hz)) (hVw z hz) (hloc _ (hpzE z hz)) hσ hC z (hpzs z hz)
  · -- the directions are Lipschitz along the axis
    intro z hz z' hz'
    have h1 := perpDir_sub_le (hV1 _ (hpzE z hz)) (hV1 _ (hpzE z' hz')) hw0 (hVw' z hz)
      (hVw' z' hz')
    have h2 := hVL _ (hpzE z hz) _ (hpzE z' hz')
    rw [dist_eq_norm, dist_eq_norm] at h2
    have hvw := inner_axis_ge hτ hρ0 (hv (ι q0)) hw0 (hTlev q0)
    have h3 := dist_le_of_heights (hv (ι q0)) hw0 hvw (hYT q0 (hpzY z hz)) (hYT q0 (hpzY z' hz'))
    -- the heights of the two points
    have hzs := hpzs z hz
    have hzs' := hpzs z' hz'
    simp only [slab, mem_setOf_eq, hφ] at hzs hzs'
    simp only [inner_resc_self hw0] at hzs hzs'
    have hdiff : ⟪pz z - pz z', w0⟫ = ⟪pz z - c0, w0⟫ - ⟪pz z' - c0, w0⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have h4 : |⟪pz z - pz z', w0⟫| ≤ ρ0 * (|(z : ℝ) - z'| + 1) := by
      rw [hdiff, abs_le]
      have e1 : h = b * ρ0 := rfl
      have hz1 : b * ρ0 * z ≤ b * ⟪pz z - c0, w0⟫ := by rw [← e1]; exact hzs.1
      have hz2 : b * ⟪pz z - c0, w0⟫ < b * ρ0 * (z + 1) := by rw [← e1]; exact hzs.2
      have hz3 : b * ρ0 * z' ≤ b * ⟪pz z' - c0, w0⟫ := by rw [← e1]; exact hzs'.1
      have hz4 : b * ⟪pz z' - c0, w0⟫ < b * ρ0 * (z' + 1) := by rw [← e1]; exact hzs'.2
      have a1 : ρ0 * z ≤ ⟪pz z - c0, w0⟫ := by nlinarith
      have a2 : ⟪pz z - c0, w0⟫ ≤ ρ0 * (z + 1) := by nlinarith
      have a3 : ρ0 * z' ≤ ⟪pz z' - c0, w0⟫ := by nlinarith
      have a4 : ⟪pz z' - c0, w0⟫ ≤ ρ0 * (z' + 1) := by nlinarith
      have hab := le_abs_self ((z : ℝ) - z')
      have hab2 := neg_abs_le ((z : ℝ) - z')
      constructor <;> nlinarith
    calc ‖perpDir w0 (V (pz z)) - perpDir w0 (V (pz z'))‖ ≤ 8 * ‖V (pz z) - V (pz z')‖ := h1
      _ ≤ 8 * (L * ‖pz z - pz z'‖) := by gcongr
      _ ≤ 8 * (L * (2 * |⟪pz z - pz z', w0⟫| + 6 * τ)) := by gcongr
      _ ≤ 8 * (L * (2 * (ρ0 * (|(z : ℝ) - z'| + 1)) + 6 * τ)) := by gcongr
      _ = 8 * L * (2 * (ρ0 * (|(z : ℝ) - z'| + 1)) + 6 * τ) := by ring
  · -- the block has width `N + 1`
    intro z hz z' hz'
    obtain ⟨-, -, ⟨p, ⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, -, ⟨p', ⟨hp1', hp2'⟩, ⟨hp3', hp4'⟩⟩⟩ := Finset.mem_filter.mp hz'
    have e1 : h * (z - z') < H + h := by
      have : h * z ≤ ⟪p, w0⟫ := hp1
      nlinarith
    have e2 : h * (z' - z) < H + h := by nlinarith
    have e3 : |(z : ℝ) - z'| < N + 1 := by
      rw [abs_lt]
      constructor
      · have : h * ((z' : ℝ) - z) < h * (N + 1) := by rw [hH_def] at e2; linarith
        have := lt_of_mul_lt_mul_left this hh.le
        linarith
      · have : h * ((z : ℝ) - z') < h * (N + 1) := by rw [hH_def] at e1; linarith
        exact lt_of_mul_lt_mul_left this hh.le
    exact e3.le

/-- Inner product of unit vectors from their distance. -/
theorem inner_ge_of_dist_le {a b : Space} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ‖a - b‖ ≤ 1 / 2) :
    1 / 2 ≤ ⟪a, b⟫ := by
  have h := norm_sub_sq_real a b
  rw [ha, hb] at h
  have h2 : ‖a - b‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (a - b)]
  nlinarith

/-- The rotation stage: rotate the fibre axis to `e₂` and a reference AD direction to `e₀`;
the slopes of the rotated AD directions extend to a Lipschitz function, and every set near the
rotated union has AD twisted slices. -/
theorem rotate_stage {σ C L τ ρ0 b : ℝ} (hτ : 0 < τ) (hτρ : τ ≤ ρ0) (hb : 1 / 2 ≤ b)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C) (hL : 0 ≤ L)
    {w0 : Space} (hw0 : ‖w0‖ = 1) {U G : Set Space} (hUb : U ⊆ ball 0 1) (hUG : U ⊆ G)
    (Zb : Finset ℤ) (hZb : Zb.Nonempty) (Vhat : ℤ → Space)
    (hU : ∀ p ∈ U, ∃ z ∈ Zb, p ∈ slab w0 (b * ρ0) z)
    (hV : ∀ z ∈ Zb, ‖Vhat z‖ = 1 ∧ ⟪Vhat z, w0⟫ = 0 ∧
        Covering (b * ρ0) (1 - σ) C ((fun q => ⟪Vhat z, q⟫) '' (G ∩ slab w0 (b * ρ0) z)))
    (hVL : ∀ z ∈ Zb, ∀ z' ∈ Zb,
      ‖Vhat z - Vhat z'‖ ≤ 8 * L * (2 * (ρ0 * (|(z : ℝ) - z'| + 1)) + 6 * τ))
    {N : ℕ} (hblock : ∀ z ∈ Zb, ∀ z' ∈ Zb, |(z : ℝ) - z'| ≤ N + 1)
    (hNL : 8 * L * (2 * (ρ0 * (N + 2)) + 6 * τ) ≤ 1 / 2) :
    ∃ (R : Space ≃ₗᵢ[ℝ] Space) (f : ℝ → ℝ), (∀ s t, |f s - f t| ≤ 1280 * L * |s - t|) ∧
      ∀ (Ef : Set Space) (δf K : ℝ), 0 < δf → δf ≤ 1 / 10 → 1 ≤ K → 1280 * L ≤ K →
        b * ρ0 ≤ K * δf → δf ≤ K * (b * ρ0) → Ef ⊆ thickening (10 * δf) (R '' U) →
        ∀ t, Covering δf (1 - σ) (20800 * K ^ 3 * C) (projectedSlice f Ef t) := by
  classical
  have hρ0 : 0 < ρ0 := lt_of_lt_of_le hτ hτρ
  set h : ℝ := b * ρ0 with hh_def
  have hh : 0 < h := by rw [hh_def]; nlinarith
  obtain ⟨zs, hzs⟩ := hZb
  obtain ⟨hVs1, hVsw, -⟩ := hV zs hzs
  obtain ⟨R, hRe0, hRe2⟩ := exists_rotation hVs1 hw0 hVsw
  -- coordinates after the rotation
  have hc0 : ∀ p : Space, (R p) 0 = ⟪p, Vhat zs⟫ := by
    intro p
    rw [coord_eq_inner, ← hRe0, LinearIsometryEquiv.inner_map_map]
  have hc2 : ∀ p : Space, (R p) 2 = ⟪p, w0⟫ := by
    intro p
    rw [coord_eq_inner, ← hRe2, LinearIsometryEquiv.inner_map_map]
  set a : ℤ → Space := fun z => R (Vhat z) with ha_def
  have ha_norm : ∀ z ∈ Zb, ‖a z‖ = 1 := fun z hz => by
    rw [ha_def, LinearIsometryEquiv.norm_map]; exact (hV z hz).1
  have ha0 : ∀ z ∈ Zb, 1 / 2 ≤ a z 0 := by
    intro z hz
    rw [ha_def, hc0]
    apply inner_ge_of_dist_le (hV z hz).1 hVs1
    have h1 := hVL z hz zs hzs
    have h2 := hblock z hz zs hzs
    calc ‖Vhat z - Vhat zs‖ ≤ 8 * L * (2 * (ρ0 * (|(z : ℝ) - zs| + 1)) + 6 * τ) := h1
      _ ≤ 8 * L * (2 * (ρ0 * (N + 2)) + 6 * τ) := by
          have h3 : ρ0 * (|(z : ℝ) - zs| + 1) ≤ ρ0 * (N + 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hρ0.le
          have hL8 : 0 ≤ 8 * L := by positivity
          nlinarith
      _ ≤ 1 / 2 := hNL
  have ha1 : ∀ z ∈ Zb, |a z 1| ≤ 1 := by
    intro z hz
    have := PiLp.norm_apply_le (a z) 1
    rw [Real.norm_eq_abs, ha_norm z hz] at this
    exact this
  have ha2 : ∀ z ∈ Zb, a z 2 = 0 := fun z hz => by rw [ha_def, hc2]; exact (hV z hz).2.1
  -- the rotated union lies in the rotated slabs
  have hE1b : R '' U ⊆ ball 0 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have := hUb hp
    rw [mem_ball_zero_iff] at this ⊢
    rwa [LinearIsometryEquiv.norm_map]
  have hslabR : ∀ (p : Space) (z : ℤ), R p ∈ hslab h z ↔ p ∈ slab w0 h z := by
    intro p z
    simp only [hslab, slab, mem_ofPred_eq, hc2]
  have hE1 : ∀ p ∈ R '' U, ∃ z ∈ Zb, p ∈ hslab h z := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, hpz⟩ := hU p hp
    exact ⟨z, hz, (hslabR p z).mpr hpz⟩
  have hcov : ∀ z ∈ Zb, Covering h (1 - σ) C
      ((fun q => ⟪a z, q⟫) '' (R '' U ∩ hslab h z)) := by
    intro z hz
    apply (hV z hz).2.2.mono
    rintro _ ⟨_, ⟨⟨p, hp, rfl⟩, hpz⟩, rfl⟩
    refine ⟨p, ⟨hUG hp, (hslabR p z).mp hpz⟩, ?_⟩
    simp only [ha_def, LinearIsometryEquiv.inner_map_map]
  -- the slope function on the slab heights
  set g : ℝ → ℝ := fun s => a ⌊s / h⌋ 1 / a ⌊s / h⌋ 0 with hg
  have hgz : ∀ z : ℤ, g (h * z) = a z 1 / a z 0 := by
    intro z
    have : ⌊h * (z : ℝ) / h⌋ = z := by rw [mul_div_cancel_left₀ _ hh.ne', Int.floor_intCast]
    simp only [hg, this]
  set S : Set ℝ := (fun z : ℤ => h * z) '' (Zb : Set ℤ) with hS
  have hgL : LipschitzOnWith (Real.toNNReal (1280 * L)) g S := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, hgz, hgz]
    have h1 := slope_sub_le (ha_norm z hz) (ha_norm z' hz') (ha0 z hz) (ha0 z' hz')
    have h2 : ‖a z - a z'‖ = ‖Vhat z - Vhat z'‖ := by
      rw [ha_def, ← map_sub, LinearIsometryEquiv.norm_map]
    rw [h2] at h1
    have h3 := hVL z hz z' hz'
    rcases eq_or_ne z z' with hzz | hzz
    · subst hzz; simp
    have hzz' : (1 : ℝ) ≤ |(z : ℝ) - z'| := by
      have : (z : ℤ) - z' ≠ 0 := sub_ne_zero.mpr hzz
      have h4 : (1 : ℤ) ≤ |z - z'| := Int.one_le_abs this
      exact_mod_cast h4
    have hρh : ρ0 ≤ 2 * h := by rw [hh_def]; nlinarith
    have e1 : |h * (z : ℝ) - h * z'| = h * |(z : ℝ) - z'| := by
      rw [← mul_sub, abs_mul, abs_of_pos hh]
    rw [e1]
    have hτ' : τ ≤ ρ0 * |(z : ℝ) - z'| := by nlinarith
    calc |a z 1 / a z 0 - a z' 1 / a z' 0| ≤ 8 * ‖Vhat z - Vhat z'‖ := h1
      _ ≤ 8 * (8 * L * (2 * (ρ0 * (|(z : ℝ) - z'| + 1)) + 6 * τ)) := by gcongr
      _ ≤ 8 * (8 * L * (10 * (ρ0 * |(z : ℝ) - z'|))) := by
          gcongr
          nlinarith
      _ = 640 * L * (ρ0 * |(z : ℝ) - z'|) := by ring
      _ ≤ 640 * L * (2 * h * |(z : ℝ) - z'|) := by
          gcongr
      _ = 1280 * L * (h * |(z : ℝ) - z'|) := by ring
  obtain ⟨f, hfL, hfg⟩ := hgL.extend_real
  have hf : ∀ z ∈ Zb, f (h * z) = a z 1 / a z 0 := by
    intro z hz
    rw [← hfg ⟨z, hz, rfl⟩, hgz]
  have hfL' : ∀ s t, |f s - f t| ≤ 1280 * L * |s - t| := by
    intro s t
    have := hfL.dist_le_mul s t
    rwa [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq] at this
  refine ⟨R, f, hfL', ?_⟩
  intro Ef δf K hδf hδf1 hK hLK hhK hδK hEf t
  exact slices_covering hh hδf hδf1 hσ0 hσ1 hC hK hhK hδK hE1b Zb a ha0 ha1 ha2 hcov hE1 f hf
    (fun s t => (hfL' s t).trans (mul_le_mul_of_nonneg_right hLK (abs_nonneg _))) hEf t

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
