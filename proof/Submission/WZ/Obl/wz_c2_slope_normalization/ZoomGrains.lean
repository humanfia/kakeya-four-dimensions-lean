-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomBasic
import Submission.WZ.Obl.wz_c2_slope_normalization.BoundedSlope

/-!
# The grains data of a zoomed family

Zooming by `r ≥ 1` about `c` and cutting each shading by the slab `|⟪p - c, v⟫| ≤ 1/(2r)`
transports every global and local grains estimate with the same constant at the scale `r δ`.
The new slope is `z ↦ g (c 2 + z / r)` and the new plane map is `P` composed with the inverse
zoom.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- The slab of axial half-width `1/(2r)` about `c` in direction `v`. -/
def zslab (r : ℝ) (c v : Space) : Set Space := {p | |⟪p - c, v⟫| ≤ 1 / (2 * r)}

/-- The zoomed shading cut by the slab. -/
def zshade (r : ℝ) (c v : Space) (Y : Set Space) : Set Space := zoom r c '' (Y ∩ zslab r c v)

/-- The inverse of the zoom. -/
def unzoom (r : ℝ) (c p : Space) : Space := c + r⁻¹ • p

theorem unzoom_zoom {r : ℝ} (hr : r ≠ 0) (c p : Space) : unzoom r c (zoom r c p) = p := by
  simp only [unzoom, zoom, smul_smul, inv_mul_cancel₀ hr, one_smul, add_sub_cancel]

theorem zoom_unzoom {r : ℝ} (hr : r ≠ 0) (c p : Space) : zoom r c (unzoom r c p) = p := by
  simp only [unzoom, zoom, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem zslab_closed (r : ℝ) (c v : Space) : IsClosed (zslab r c v) :=
  isClosed_le (continuous_abs.comp ((continuous_id.sub continuous_const).inner continuous_const))
    continuous_const

theorem Assouad.empty {d α C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) : Assouad d α C ∅ := by
  intro r R a hdr hrR
  refine ⟨0, Fin.elim0, by simp, ?_⟩
  simp only [Nat.cast_zero]
  exact mul_nonneg hC (Real.rpow_nonneg (div_nonneg (hd.le.trans (hdr.trans hrR))
    (hd.le.trans hdr)) _)

/-- The twisted slices of a zoomed set are affine images of the original slices. -/
theorem projectedSlice_zoom {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) (c : Space) (E : Set Space)
    (z : ℝ) :
    ProjectedSlice (fun t => g (c 2 + t / r)) (zoom r c '' E) z =
      (fun u => r * u + (-(r * (c 0 + g (c 2 + z / r) * c 1)))) ''
        ProjectedSlice g E (c 2 + z / r) := by
  ext u
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, he⟩
    obtain ⟨hu, hz⟩ := Prod.mk.inj he
    have hz' : p 2 = c 2 + z / r := by
      simp only [zoom, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hz
      field_simp at hz ⊢
      linarith
    refine ⟨p 0 + g (p 2) * p 1, ⟨p, hp, ?_⟩, ?_⟩
    · simp only [hz']
    · simp only [zoom, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hu
      rw [← hu, ← hz']
      have : c 2 + r * (p 2 - c 2) / r = p 2 := by field_simp; ring
      rw [this]
      ring
  · rintro ⟨w, ⟨p, hp, he⟩, rfl⟩
    obtain ⟨hw, hz⟩ := Prod.mk.inj he
    refine ⟨zoom r c p, ⟨p, hp, rfl⟩, ?_⟩
    have h2 : zoom r c p 2 = z := by
      simp only [zoom, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [hz]; field_simp; ring
    have hg : c 2 + zoom r c p 2 / r = p 2 := by rw [h2, hz]
    simp only
    rw [hg, h2]
    simp only [zoom, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [← hw, hz]
    congr 1
    ring

theorem zoom_image_iUnion {m : ℕ} (r : ℝ) (c : Space) (F : Fin m → Set Space) :
    (⋃ k, zoom r c '' F k) = zoom r c '' ⋃ k, F k := (image_iUnion ..).symm

/-- Zooming a cut subfamily transports all grains estimates, with the same constant, to the
scale `r δ`. -/
theorem Grains.zoomed {σ δ K r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 1 ≤ r) (hK : 0 ≤ K)
    {n m : ℕ} {v : Fin n → Space} {Y : Fin n → Set Space} {g : ℝ → ℝ} {P : Space → Space}
    (h : Grains σ δ K v Y g P) (hball : ∀ p ∈ ⋃ i, Y i, ‖p‖ < 1)
    (a : Fin m → Fin n) (c : Space) :
    Grains σ (r * δ) K (fun k => v (a k)) (fun k => zshade r c (v (a k)) (Y (a k)))
      (fun t => g (c 2 + t / r)) (fun p => P (unzoom r c p)) := by
  obtain ⟨hglobal, hLip, hnorm, horth, hlocal⟩ := h
  have hr0 : 0 < r := by linarith
  set Esub := ⋃ k, Y (a k) ∩ zslab r c (v (a k))
  have hE' : (⋃ k, zshade r c (v (a k)) (Y (a k))) = zoom r c '' Esub :=
    zoom_image_iUnion r c _
  have hsub : Esub ⊆ ⋃ i, Y i := by
    intro p hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨a k, hk.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hE', projectedSlice_zoom hr0]
    by_cases hz' : c 2 + z / r ∈ Icc (-1 : ℝ) 1
    · exact ((hglobal _ hz').mono_set (projectedSlice_mono hsub _)).affine_image hδ hr0
    · have hempty : ProjectedSlice g Esub (c 2 + z / r) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro u ⟨p, hp, he⟩
        obtain ⟨-, hz2⟩ := Prod.mk.inj he
        apply hz'
        rw [← hz2]
        have h1 := hball p (hsub hp)
        have h2 : |p 2| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p 2
        have h3 := (abs_le.mp (h2.trans h1.le))
        exact ⟨h3.1, h3.2⟩
      rw [hempty, image_empty]
      exact Assouad.empty (mul_pos hr0 hδ) hK
  · refine LipschitzWith.of_dist_le_mul fun p q => ?_
    have h1 := hLip.dist_le_mul (unzoom r c p) (unzoom r c q)
    have h2 : dist (unzoom r c p) (unzoom r c q) = r⁻¹ * dist p q := by
      simp only [unzoom, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    have h3 : r⁻¹ * dist p q ≤ dist p q :=
      mul_le_of_le_one_left dist_nonneg (inv_le_one_of_one_le₀ hr)
    simp only [NNReal.coe_one, one_mul] at h1 ⊢
    linarith
  · intro p hp
    rw [hE'] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [unzoom_zoom hr0.ne']
    exact hnorm q (hsub hq)
  · rintro k _ ⟨q, hq, rfl⟩
    simp only [unzoom_zoom hr0.ne']
    exact (horth (a k) q hq.1).trans (le_mul_of_one_le_left hδ.le hr)
  · intro ρ hρ hρ1 p hp
    rw [hE'] at hp ⊢
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [unzoom_zoom hr0.ne']
    set ρ₀ := max δ (ρ / r ^ 2)
    have hρpos : 0 < ρ := (mul_pos hr0 hδ).trans_le hρ
    have hρ₀ : δ ≤ ρ₀ := le_max_left _ _
    have hρ₀1 : ρ₀ ≤ 1 := by
      apply max_le hδ1
      rw [div_le_one (by positivity)]
      nlinarith
    have hold := hlocal ρ₀ hρ₀ hρ₀1 q (hsub hq)
    have hscale : ρ₀ ≤ ρ / r := by
      apply max_le
      · rw [le_div_iff₀ hr0]; linarith
      · rw [div_le_div_iff₀ (by positivity) hr0]
        nlinarith [mul_nonneg (mul_nonneg hρpos.le hr0.le) (sub_nonneg.mpr hr)]
    have hA := (hold.mono_scale hscale).affine_image (b := -(r * ⟪P q, c⟫))
      (div_pos hρpos hr0) hr0
    rw [mul_div_cancel₀ _ hr0.ne'] at hA
    apply hA.mono_set
    rintro _ ⟨y, ⟨⟨y₀, hy₀, rfl⟩, hyball⟩, rfl⟩
    refine ⟨⟪P q, y₀⟫, ⟨y₀, ⟨mem_iUnion.mpr ?_, ?_⟩, rfl⟩, ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hy₀
      exact ⟨a k, hk.1⟩
    · rw [mem_ball, dist_eq_norm] at hyball ⊢
      rw [norm_zoom_sub hr0.le] at hyball
      have h1 : ‖y₀ - q‖ < Real.sqrt ρ / r := by
        rw [lt_div_iff₀ hr0]; linarith
      have h2 : Real.sqrt ρ / r ≤ Real.sqrt ρ₀ := by
        have he : Real.sqrt ρ / r = Real.sqrt (ρ / r ^ 2) := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0.le]
        rw [he]
        exact Real.sqrt_le_sqrt (le_max_right _ _)
      linarith
    · simp only [zoom, inner_smul_right, inner_sub_right]
      ring


/-- Grains data with a plane map of Lipschitz constant `Kp`. -/
def GrainsK (σ δ K Kp : ℝ) {n : ℕ} (v : Fin n → Space) (Y : Fin n → Set Space)
    (f : ℝ → ℝ) (P : Space → Space) : Prop :=
  (∀ z ∈ Icc (-1 : ℝ) 1, Assouad δ (1 - σ) K (ProjectedSlice f (⋃ i, Y i) z)) ∧
  (∀ p q, dist (P p) (P q) ≤ Kp * dist p q) ∧
  (∀ p ∈ ⋃ i, Y i, ‖P p‖ = 1) ∧
  (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
  (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ ⋃ i, Y i,
    Assouad ρ (1 - σ) K
      ((fun q => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

theorem GrainsK.toGrains {σ δ K Kp : ℝ} {n : ℕ} {v : Fin n → Space} {Y : Fin n → Set Space}
    {f : ℝ → ℝ} {P : Space → Space} (hKp : Kp ≤ 1) (h : GrainsK σ δ K Kp v Y f P) :
    Grains σ δ K v Y f P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, LipschitzWith.of_dist_le_mul fun p q => ?_, h3, h4, h5⟩
  simp only [NNReal.coe_one, one_mul]
  exact (h2 p q).trans (mul_le_of_le_one_left dist_nonneg hKp)

theorem GrainsK.zoomed {σ δ K Kp r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 1 ≤ r) (hK : 0 ≤ K)
    {n m : ℕ} {v : Fin n → Space} {Y : Fin n → Set Space} {g : ℝ → ℝ} {P : Space → Space}
    (h : GrainsK σ δ K Kp v Y g P) (hball : ∀ p ∈ ⋃ i, Y i, ‖p‖ < 1)
    (a : Fin m → Fin n) (c : Space) :
    GrainsK σ (r * δ) K (Kp / r) (fun k => v (a k)) (fun k => zshade r c (v (a k)) (Y (a k)))
      (fun t => g (c 2 + t / r)) (fun p => P (unzoom r c p)) := by
  obtain ⟨hglobal, hLip, hnorm, horth, hlocal⟩ := h
  have hr0 : 0 < r := by linarith
  set Esub := ⋃ k, Y (a k) ∩ zslab r c (v (a k))
  have hE' : (⋃ k, zshade r c (v (a k)) (Y (a k))) = zoom r c '' Esub :=
    zoom_image_iUnion r c _
  have hsub : Esub ⊆ ⋃ i, Y i := by
    intro p hp
    obtain ⟨k, hk⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨a k, hk.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hE', projectedSlice_zoom hr0]
    by_cases hz' : c 2 + z / r ∈ Icc (-1 : ℝ) 1
    · exact ((hglobal _ hz').mono_set (projectedSlice_mono hsub _)).affine_image hδ hr0
    · have hempty : ProjectedSlice g Esub (c 2 + z / r) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro u ⟨p, hp, he⟩
        obtain ⟨-, hz2⟩ := Prod.mk.inj he
        apply hz'
        rw [← hz2]
        have h1 := hball p (hsub hp)
        have h2 : |p 2| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p 2
        have h3 := (abs_le.mp (h2.trans h1.le))
        exact ⟨h3.1, h3.2⟩
      rw [hempty, image_empty]
      exact Assouad.empty (mul_pos hr0 hδ) hK
  · intro p q
    have h1 := hLip (unzoom r c p) (unzoom r c q)
    have h2 : dist (unzoom r c p) (unzoom r c q) = r⁻¹ * dist p q := by
      simp only [unzoom, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    rw [h2] at h1
    calc dist (P (unzoom r c p)) (P (unzoom r c q)) ≤ Kp * (r⁻¹ * dist p q) := h1
      _ = Kp / r * dist p q := by ring
  · intro p hp
    rw [hE'] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [unzoom_zoom hr0.ne']
    exact hnorm q (hsub hq)
  · rintro k _ ⟨q, hq, rfl⟩
    simp only [unzoom_zoom hr0.ne']
    exact (horth (a k) q hq.1).trans (le_mul_of_one_le_left hδ.le hr)
  · intro ρ hρ hρ1 p hp
    rw [hE'] at hp ⊢
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [unzoom_zoom hr0.ne']
    set ρ₀ := max δ (ρ / r ^ 2)
    have hρpos : 0 < ρ := (mul_pos hr0 hδ).trans_le hρ
    have hρ₀ : δ ≤ ρ₀ := le_max_left _ _
    have hρ₀1 : ρ₀ ≤ 1 := by
      apply max_le hδ1
      rw [div_le_one (by positivity)]
      nlinarith
    have hold := hlocal ρ₀ hρ₀ hρ₀1 q (hsub hq)
    have hscale : ρ₀ ≤ ρ / r := by
      apply max_le
      · rw [le_div_iff₀ hr0]; linarith
      · rw [div_le_div_iff₀ (by positivity) hr0]
        nlinarith [mul_nonneg (mul_nonneg hρpos.le hr0.le) (sub_nonneg.mpr hr)]
    have hA := (hold.mono_scale hscale).affine_image (b := -(r * ⟪P q, c⟫))
      (div_pos hρpos hr0) hr0
    rw [mul_div_cancel₀ _ hr0.ne'] at hA
    apply hA.mono_set
    rintro _ ⟨y, ⟨⟨y₀, hy₀, rfl⟩, hyball⟩, rfl⟩
    refine ⟨⟪P q, y₀⟫, ⟨y₀, ⟨mem_iUnion.mpr ?_, ?_⟩, rfl⟩, ?_⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hy₀
      exact ⟨a k, hk.1⟩
    · rw [mem_ball, dist_eq_norm] at hyball ⊢
      rw [norm_zoom_sub hr0.le] at hyball
      have h1 : ‖y₀ - q‖ < Real.sqrt ρ / r := by
        rw [lt_div_iff₀ hr0]; linarith
      have h2 : Real.sqrt ρ / r ≤ Real.sqrt ρ₀ := by
        have he : Real.sqrt ρ / r = Real.sqrt (ρ / r ^ 2) := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0.le]
        rw [he]
        exact Real.sqrt_le_sqrt (le_max_right _ _)
      linarith
    · simp only [zoom, inner_smul_right, inner_sub_right]
      ring

end

end WangZahlLot.Obl.wz_c2_slope_normalization
