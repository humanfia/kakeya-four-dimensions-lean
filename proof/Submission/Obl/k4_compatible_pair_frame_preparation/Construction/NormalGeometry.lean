-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/NormalGeometry.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/NormalGeometry.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Saturation
import Submission.Lib.K4QuadraticSublevel

/-!
# Geometry for the normal-exception bound

For an old chart with frame `(c, u, Q)` on an old dyadic block of length
`2^-T₀`, every assigned line has its velocity in the *velocity ellipse*
`{w | ‖Q⁻¹ (w - u)‖ ≤ 2 κ 2^T₀}`, and on any longer interval of length `ℓ`
containing the old block its spatial point stays in the enlarged box
`‖Q⁻¹ (y - c - t u)‖ ≤ κ + 2 κ 2^T₀ ℓ`.  We also count the closed hidden bins
meeting a regular quadratic sublevel set, and the velocity bins meeting a set of
bounded diameter.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- The velocity ellipse of a chart frame. -/
def velEllipse (κ : ℝ) (T₀ : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {w | ‖Matrix.toEuclideanLin Q⁻¹ (w - u)‖ ≤ 2 * κ * (2 : ℝ) ^ T₀}

theorem y_eq_add_smul_v (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : y l t = y l 0 + t • v l := by
  ext i
  fin_cases i <;> simp [y, x, v]

theorem y_sub_y (l : ℕ × (Fin 6 → ℝ)) (s t : ℝ) : y l t - y l s = (t - s) • v l := by
  rw [y_eq_add_smul_v l t, y_eq_add_smul_v l s, sub_smul]
  abel

/-- Lines of a chart move with velocity inside its velocity ellipse. -/
theorem v_mem_velEllipse {κ j₀ : ℝ} {T₀ : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {l : ℕ × (Fin 6 → ℝ)}
    (hbox : ∀ t ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ) :
    v l ∈ velEllipse κ T₀ u Q := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  set t₁ := j₀ / (2 : ℝ) ^ T₀
  set t₂ := (j₀ + 1) / (2 : ℝ) ^ T₀
  have hle : t₁ ≤ t₂ := div_le_div_of_nonneg_right (by linarith) hpos.le
  have h₁ := hbox t₁ ⟨le_rfl, hle⟩
  have h₂ := hbox t₂ ⟨hle, le_rfl⟩
  have hdiff : t₂ - t₁ = ((2 : ℝ) ^ T₀)⁻¹ := by
    simp only [t₁, t₂]; field_simp; ring
  have hkey : v l - u = (2 : ℝ) ^ T₀ • ((y l t₂ - c - t₂ • u) - (y l t₁ - c - t₁ • u)) := by
    have e : (y l t₂ - c - t₂ • u) - (y l t₁ - c - t₁ • u) = (t₂ - t₁) • (v l - u) := by
      rw [smul_sub, ← y_sub_y, sub_smul]
      abel
    rw [e, hdiff, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  simp only [velEllipse, mem_ofPred_eq]
  rw [hkey, map_smul, map_sub, norm_smul, Real.norm_of_nonneg hpos.le]
  calc (2 : ℝ) ^ T₀ * ‖Matrix.toEuclideanLin Q⁻¹ (y l t₂ - c - t₂ • u) -
        Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖
      ≤ (2 : ℝ) ^ T₀ * (κ + κ) := by
        apply mul_le_mul_of_nonneg_left _ hpos.le
        exact (norm_sub_le _ _).trans (add_le_add h₂ h₁)
    _ = 2 * κ * (2 : ℝ) ^ T₀ := by ring

/-- On a longer interval of length `ℓ` containing the old block, the lines of a chart
stay in the enlarged box of radius `κ + 2 κ 2^T₀ ℓ`. -/
theorem box_extrapolate {κ j₀ a ℓ : ℝ} {T₀ : ℕ} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {l : ℕ × (Fin 6 → ℝ)}
    (hbox : ∀ t ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀),
      ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ)
    (ha : a ≤ j₀ / (2 : ℝ) ^ T₀) (hb : (j₀ + 1) / (2 : ℝ) ^ T₀ ≤ a + ℓ)
    {t : ℝ} (ht : t ∈ Icc a (a + ℓ)) :
    ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ + 2 * κ * (2 : ℝ) ^ T₀ * ℓ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  set t₁ := j₀ / (2 : ℝ) ^ T₀
  have hle : t₁ ≤ (j₀ + 1) / (2 : ℝ) ^ T₀ := div_le_div_of_nonneg_right (by linarith) hpos.le
  have h₁ := hbox t₁ ⟨le_rfl, hle⟩
  have hv := v_mem_velEllipse hbox
  simp only [velEllipse, mem_ofPred_eq] at hv
  have hsplit : y l t - c - t • u = (y l t₁ - c - t₁ • u) + (t - t₁) • (v l - u) := by
    rw [smul_sub, ← y_sub_y, sub_smul]
    abel
  have hdist : |t - t₁| ≤ ℓ := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  rw [hsplit, map_add, map_smul]
  calc ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u) +
        (t - t₁) • Matrix.toEuclideanLin Q⁻¹ (v l - u)‖
      ≤ ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ +
          |t - t₁| * ‖Matrix.toEuclideanLin Q⁻¹ (v l - u)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ κ + ℓ * (2 * κ * (2 : ℝ) ^ T₀) := by
        apply add_le_add h₁
        exact mul_le_mul hdist hv (norm_nonneg _) (le_trans (abs_nonneg _) hdist)
    _ = κ + 2 * κ * (2 : ℝ) ^ T₀ * ℓ := by ring

/-! ## Counting bins -/

/-- Closed hidden bins meeting a regular quadratic sublevel set are at most
`16 (1 + ε / (β h))`. -/
theorem closed_bins_card_le (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h) :
    {n : ℤ | ∃ w ∈ Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h),
        |p.eval w| ≤ ε ∧ β ≤ |p.derivative.eval w|}.Finite ∧
      (({n : ℤ | ∃ w ∈ Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h),
        |p.eval w| ≤ ε ∧ β ≤ |p.derivative.eval w|}.ncard : ℕ) : ℝ) ≤
        16 * (1 + ε / (β * h)) := by
  classical
  obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_quadratic_sublevel
    p hp hε hβ hh 0
  set Z := (fun w : ℝ => ⌊(w - 0) / h⌋) '' {w : ℝ | |p.eval w| ≤ ε ∧ β ≤ |p.derivative.eval w|}
  have hsub : {n : ℤ | ∃ w ∈ Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h),
      |p.eval w| ≤ ε ∧ β ≤ |p.derivative.eval w|} ⊆ Z ∪ ((fun n => n - 1) '' Z) := by
    rintro n ⟨w, ⟨hw1, hw2⟩, hwS⟩
    have hfl : ⌊(w - 0) / h⌋ = n ∨ ⌊(w - 0) / h⌋ = n + 1 := by
      have h1 : (n : ℝ) ≤ (w - 0) / h := by rw [sub_zero, le_div_iff₀ hh]; linarith
      have h2 : (w - 0) / h ≤ (n : ℝ) + 1 := by rw [sub_zero, div_le_iff₀ hh]; linarith
      have hlo : n ≤ ⌊(w - 0) / h⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
      have hhi : ⌊(w - 0) / h⌋ ≤ n + 1 := by
        have := Int.floor_le_floor h2
        rwa [show ((n : ℝ) + 1) = ((n + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast] at this
      omega
    rcases hfl with hf | hf
    · left; exact ⟨w, hwS, hf⟩
    · right; exact ⟨⌊(w - 0) / h⌋, ⟨w, hwS, rfl⟩, by simp only [hf]; ring⟩
  have hfinU : (Z ∪ ((fun n => n - 1) '' Z)).Finite := hfin.union (hfin.image _)
  refine ⟨hfinU.subset hsub, ?_⟩
  calc (({n : ℤ | ∃ w ∈ Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h),
        |p.eval w| ≤ ε ∧ β ≤ |p.derivative.eval w|}.ncard : ℕ) : ℝ)
      ≤ ((Z ∪ ((fun n => n - 1) '' Z)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinU
    _ ≤ ((Z.ncard + ((fun n => n - 1) '' Z).ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_union_le _ _
    _ ≤ ((Z.ncard + Z.ncard : ℕ) : ℝ) := by
        have := Set.ncard_image_le (f := fun n : ℤ => n - 1) hfin
        exact_mod_cast Nat.add_le_add_left this _
    _ ≤ 16 * (1 + ε / (β * h)) := by
        push_cast
        linarith

/-- Velocity bins meeting a set inside a closed ball of radius `ρ` are at most
`(4 ρ / δ + 2)²`. -/
theorem velocity_bins_card_le {S : Set (EuclideanSpace ℝ (Fin 2))}
    {w₀ : EuclideanSpace ℝ (Fin 2)} {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hS : S ⊆ Metric.closedBall w₀ ρ) :
    ((fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 2 => ⌊w i / δ⌋) '' S).Finite ∧
      ((((fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 2 => ⌊w i / δ⌋) '' S).ncard : ℕ) : ℝ) ≤
        (4 * ρ / δ + 2) ^ 2 := by
  classical
  -- coordinate images
  have hcoord (i : Fin 2) : ∀ a ∈ (fun w : EuclideanSpace ℝ (Fin 2) => w i) '' S,
      ∀ b ∈ (fun w : EuclideanSpace ℝ (Fin 2) => w i) '' S, dist a b ≤ 2 * ρ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha' := hS ha
    have hb' := hS hb
    rw [Metric.mem_closedBall] at ha' hb'
    have hab : dist a b ≤ 2 * ρ := by
      calc dist a b ≤ dist a w₀ + dist w₀ b := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add ha' (by rw [dist_comm]; exact hb')
        _ = 2 * ρ := by ring
    calc dist (a i) (b i) = |a i - b i| := Real.dist_eq _ _
      _ ≤ ‖a - b‖ := by
          rw [← PiLp.sub_apply]
          exact PiLp.norm_apply_le (a - b) i
      _ = dist a b := (dist_eq_norm a b).symm
      _ ≤ 2 * ρ := hab
  have hb (i : Fin 2) := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    ((fun w : EuclideanSpace ℝ (Fin 2) => w i) '' S) (by positivity) hδ 0 (hcoord i)
  set Z₀ := (fun a : ℝ => ⌊(a - 0) / δ⌋) '' ((fun w : EuclideanSpace ℝ (Fin 2) => w 0) '' S)
  set Z₁ := (fun a : ℝ => ⌊(a - 0) / δ⌋) '' ((fun w : EuclideanSpace ℝ (Fin 2) => w 1) '' S)
  have hsub : ((fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 2 => ⌊w i / δ⌋) '' S) ⊆
      (fun k : ℤ × ℤ => ![k.1, k.2]) '' (Z₀ ×ˢ Z₁) := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(⌊w 0 / δ⌋, ⌊w 1 / δ⌋), ⟨⟨w 0, ⟨w, hw, rfl⟩, by simp⟩,
      ⟨w 1, ⟨w, hw, rfl⟩, by simp⟩⟩, ?_⟩
    funext i
    fin_cases i <;> simp
  have hfinP : (Z₀ ×ˢ Z₁).Finite := (hb 0).1.prod (hb 1).1
  have hfinI := hfinP.image (fun k : ℤ × ℤ => ![k.1, k.2])
  refine ⟨hfinI.subset hsub, ?_⟩
  calc ((((fun w : EuclideanSpace ℝ (Fin 2) => fun i : Fin 2 => ⌊w i / δ⌋) '' S).ncard : ℕ) : ℝ)
      ≤ (((fun k : ℤ × ℤ => ![k.1, k.2]) '' (Z₀ ×ˢ Z₁)).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hfinI
    _ ≤ ((Z₀ ×ˢ Z₁).ncard : ℝ) := by exact_mod_cast Set.ncard_image_le hfinP
    _ = (Z₀.ncard : ℝ) * (Z₁.ncard : ℝ) := by
        rw [Set.ncard_prod]; push_cast; ring
    _ ≤ (2 * (2 * ρ) / δ + 2) * (2 * (2 * ρ) / δ + 2) := by
        apply mul_le_mul (hb 0).2 (hb 1).2 (by positivity) (by positivity)
    _ = (4 * ρ / δ + 2) ^ 2 := by ring

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
