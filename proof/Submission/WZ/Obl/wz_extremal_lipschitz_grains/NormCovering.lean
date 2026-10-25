-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormCovering.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs

/-!
# Covering estimates under the zoom

`Covering` is invariant under affine maps of the line (with the resolution scaled), monotone in
the resolution and the constant. The twisted slices and the local plane projections of a zoomed
set are affine images of those of the original set.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

theorem Covering.mono_res {d d' α C : ℝ} {B : Set ℝ} (h : Covering d α C B) (hd : d ≤ d') :
    Covering d' α C B := fun r R a hr hrR => h r R a (hd.trans hr) hrR

theorem Covering.mono_const {d α C C' : ℝ} {B : Set ℝ} (h : Covering d α C B) (hd : 0 < d)
    (hC : C ≤ C') : Covering d α C' B := by
  intro r R a hr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hr hrR
  refine ⟨m, c, hc, hm.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _)

theorem covering_empty {d α C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) : Covering d α C ∅ := by
  intro r R a hr hrR
  refine ⟨0, fun _ => 0, by simp, ?_⟩
  simp only [Nat.cast_zero]
  exact mul_nonneg hC (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _)

/-- Affine images: scaling by `lam > 0` scales the resolution. -/
theorem Covering.affine_zoom {d α C : ℝ} {B : Set ℝ} (h : Covering d α C B) {lam : ℝ} (hlam : 0 < lam)
    (b : ℝ) : Covering (lam * d) α C ((fun u => lam * u + b) '' B) := by
  intro r R a hr hrR
  have hr' : d ≤ r / lam := by rw [le_div_iff₀ hlam]; linarith
  have hrR' : r / lam ≤ R / lam := div_le_div_of_nonneg_right hrR hlam.le
  obtain ⟨m, c, hc, hm⟩ := h (r / lam) (R / lam) ((a - b) / lam) hr' hrR'
  refine ⟨m, fun j => lam * c j + b, ?_, ?_⟩
  · rintro u ⟨⟨y, hy, rfl⟩, hu⟩
    have hyI : y ∈ Icc ((a - b) / lam) ((a - b) / lam + R / lam) := by
      obtain ⟨hu1, hu2⟩ := hu
      constructor
      · rw [div_le_iff₀ hlam]; linarith
      · rw [← add_div, le_div_iff₀ hlam]; linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hy, hyI⟩)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Real.dist_eq] at hj ⊢
    have he : lam * y + b - (lam * c j + b) = lam * (y - c j) := by ring
    rw [he, abs_mul, abs_of_pos hlam]
    calc lam * |y - c j| ≤ lam * (r / lam) := mul_le_mul_of_nonneg_left hj hlam.le
      _ = r := by field_simp
  · have he : R / lam / (r / lam) = R / r := by
      rcases eq_or_ne r 0 with h0 | h0
      · simp [h0]
      · field_simp
    rwa [he] at hm


theorem zoom_apply (c : Space) (lam : ℝ) (p : Space) (k : Fin 3) :
    zoom c lam p k = lam * (p k - c k) := by
  simp [zoom]

theorem coord_mem_Icc_of_mem_ball {p : Space} (hp : p ∈ ball (0 : Space) 1) (k : Fin 3) :
    p k ∈ Icc (-1 : ℝ) 1 := by
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hc : |p k| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p k
  exact abs_le.mp (hc.trans hp1.le)

/-- Twisted slices of a zoomed set are affine images of twisted slices of the original set. -/
theorem projectedSlice_zoom_subset {c : Space} {lam : ℝ} (hlam : 0 < lam) (f : ℝ → ℝ)
    (E₀ : Set Space) (z' : ℝ) :
    projectedSlice (fun z => f (c 2 + z / lam)) (zoom c lam '' E₀) z' ⊆
      (fun u => lam * u + -(lam * (c 0 + f (c 2 + z' / lam) * c 1))) ''
        projectedSlice f E₀ (c 2 + z' / lam) := by
  rintro u ⟨p', ⟨p, hp, rfl⟩, he⟩
  simp only [Prod.mk.injEq, zoom_apply] at he
  obtain ⟨hu, hz⟩ := he
  have hp2 : p 2 = c 2 + z' / lam := by
    rw [← hz]; field_simp; ring
  refine ⟨p 0 + f (p 2) * p 1, ⟨p, hp, Prod.ext rfl hp2⟩, ?_⟩
  rw [← hu, ← hp2]
  have : lam * (p 2 - c 2) / lam = p 2 - c 2 := by field_simp
  rw [this, show c 2 + (p 2 - c 2) = p 2 by ring]
  ring

/-- The global grains estimate survives the zoom (with the resolution multiplied by `lam`). -/
theorem covering_projectedSlice_zoom {δ α C lam : ℝ} {f : ℝ → ℝ} {E E₀ : Set Space}
    {c : Space} (hlam : 0 < lam) (hE₀ : E₀ ⊆ E) (hEb : E ⊆ ball 0 1) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcov : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering δ α C (projectedSlice f E z)) (z' : ℝ) :
    Covering (lam * δ) α C
      (projectedSlice (fun z => f (c 2 + z / lam)) (zoom c lam '' E₀) z') := by
  apply Covering.mono _ (projectedSlice_zoom_subset hlam f E₀ z')
  by_cases hz : c 2 + z' / lam ∈ Icc (-1 : ℝ) 1
  · exact ((hcov _ hz).mono (projectedSlice_mono hE₀ _)).affine_zoom hlam _
  · have hempty : projectedSlice f E₀ (c 2 + z' / lam) = ∅ := by
      ext u
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨p, hp, he⟩
      simp only [Prod.mk.injEq] at he
      apply hz
      rw [← he.2]
      exact coord_mem_Icc_of_mem_ball (hEb (hE₀ hp)) 2
    rw [hempty, image_empty]
    exact covering_empty (by positivity) hC

/-- Local plane projections of a zoomed set are affine images of those of the original set. -/
theorem local_zoom_subset {c : Space} {lam : ℝ} (hlam : 0 < lam) (u : Space) (E₀ : Set Space)
    (p : Space) (s : ℝ) :
    (fun q' : Space => inner ℝ u q') '' (zoom c lam '' E₀ ∩ ball (zoom c lam p) s) ⊆
      (fun t => lam * t + -(lam * inner ℝ u c)) ''
        ((fun q : Space => inner ℝ u q) '' (E₀ ∩ ball p (s / lam))) := by
  rintro t ⟨q', ⟨⟨q, hq, rfl⟩, hqb⟩, rfl⟩
  refine ⟨inner ℝ u q, ⟨q, ⟨hq, ?_⟩, rfl⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm] at hqb ⊢
    rw [norm_zoom_sub hlam.le] at hqb
    rw [lt_div_iff₀ hlam]; linarith
  · simp only [zoom, inner_smul_right, inner_sub_right]
    ring

/-- The local grains estimate survives the zoom for every resolution `ρ' ∈ [lam δ, 1]`. -/
theorem covering_local_zoom {δ α C lam ρ' : ℝ} {V : Space → Space} {E E₀ : Set Space}
    {c p : Space} (hlam : 1 ≤ lam) (hE₀ : E₀ ⊆ E) (hp : p ∈ E) (hδ : 0 < δ)
    (hloc : ∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p : Space, p ∈ E →
      Covering ρ α C ((fun q : Space => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))))
    (hρ'1 : lam * δ ≤ ρ') (hρ'2 : ρ' ≤ 1) :
    Covering ρ' α C ((fun q' : Space => inner ℝ (V p) q') ''
      (zoom c lam '' E₀ ∩ ball (zoom c lam p) (Real.sqrt ρ'))) := by
  have hlam0 : 0 < lam := by linarith
  apply Covering.mono _ (local_zoom_subset hlam0 (V p) E₀ p _)
  set ρ := max δ (ρ' / lam ^ 2) with hρ
  have hδρ : δ ≤ ρ := le_max_left _ _
  have hρ1 : ρ ≤ 1 := by
    apply max_le
    · nlinarith
    · rw [div_le_one (by positivity)]
      nlinarith
  have hsqrt : Real.sqrt ρ' / lam ≤ Real.sqrt ρ := by
    have h1 : Real.sqrt ρ' / lam = Real.sqrt (ρ' / lam ^ 2) := by
      rw [Real.sqrt_div' _ (sq_nonneg lam), Real.sqrt_sq hlam0.le]
    rw [h1]
    exact Real.sqrt_le_sqrt (le_max_right _ _)
  have hres : ρ ≤ ρ' / lam := by
    apply max_le
    · rw [le_div_iff₀ hlam0]; linarith
    · rw [div_le_div_iff₀ (by positivity) hlam0]
      have hρ'0 : 0 ≤ ρ' := by nlinarith
      have hl2 : lam ≤ lam ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hl2 hρ'0
  have hcov := ((hloc ρ hδρ hρ1 p hp).mono (image_mono
    (inter_subset_inter hE₀ (ball_subset_ball hsqrt)))).mono_res hres
  have h := hcov.affine_zoom hlam0 (-(lam * inner ℝ (V p) c))
  rwa [show lam * (ρ' / lam) = ρ' by field_simp] at h

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
