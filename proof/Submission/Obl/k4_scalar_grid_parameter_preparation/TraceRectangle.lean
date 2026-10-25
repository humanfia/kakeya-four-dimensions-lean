/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/TraceRectangle.lean -/
import Submission.Lib.K4QuadraticSublevel
import Submission.Obl.k4_scalar_grid_parameter_preparation.VelocityBins

/-! Fine rectangular incidence counts for fixed-time prior estimates. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem scalarVelocityBin_diameter_le {ξ u v : ℝ} {q : ℤ} (hξ : 0 < ξ)
    (hu : u ∈ scalarVelocityBin ξ q) (hv : v ∈ scalarVelocityBin ξ q) : dist u v ≤ ξ := by
  have h := Int.abs_sub_lt_one_of_floor_eq_floor (hu.trans hv.symm)
  rw [← sub_div, abs_div, abs_of_pos hξ] at h
  exact ((div_lt_one hξ).mp h).le

/-- A label set localized in two scalar bins at a fixed time, and propagated
over a fine time window, meets only `O(A*ξ/δ)` original incidence rectangles.
The original palette event is retained exactly, so no doubling is required. -/
theorem propagated_rectangle_mass_le {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (Y X : α → ℝ → ℝ) (V : α → ℝ)
    (C : Set α) (I : Set ℝ) (P : Set ℝ) (p : ℝ≥0∞)
    (t₀ τ ξ ζ δ A U B : ℝ) (q a : ℤ)
    (hδ : 0 < δ) (hξ : δ ≤ ξ) (hζ : 0 < ζ) (hA : 1 ≤ A)
    (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hI : I ⊆ Set.Icc τ (τ + δ))
    (hY : ∀ l ∈ C, Y l t₀ ∈ scalarVelocityBin ξ q)
    (hX : ∀ l ∈ C, X l t₀ ∈ scalarVelocityBin ζ a)
    (hV : ∀ l ∈ C, V l ∈ P)
    (hYmove : ∀ l ∈ C, ∀ t ∈ I, dist (Y l t) (Y l t₀) ≤ A * δ)
    (hXmove : ∀ l ∈ C, ∀ t ∈ I, dist (X l t) (X l t₀) ≤ ζ)
    (hcap : ∀ i j b : ℤ,
      μ {ω | (⌊ω.2 / δ⌋ : ℤ) = i ∧ (⌊Y ω.1 ω.2 / δ⌋ : ℤ) = j ∧
        (⌊X ω.1 ω.2 / ζ⌋ : ℤ) = b ∧ V ω.1 ∈ P} ≤
          ENNReal.ofReal (U * δ ^ 2 * B) * p) :
    μ (C ×ˢ I) ≤ ENNReal.ofReal (256 * A * U * ξ * δ * B) * p := by
  have hξpos : 0 < ξ := hδ.trans_le hξ
  have hApos : 0 < A := zero_lt_one.trans_le hA
  let RY : Set ℝ := {y | ∃ l ∈ C, ∃ t ∈ I, Y l t = y}
  let RX : Set ℝ := {x | ∃ l ∈ C, ∃ t ∈ I, X l t = x}
  have htime : ∀ s ∈ I, ∀ t ∈ I, dist s t ≤ δ := by
    intro s hs t ht
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [(hI hs).1, (hI ht).2],
      by linarith [(hI hs).2, (hI ht).1]⟩
  have hydiam : ∀ y ∈ RY, ∀ y' ∈ RY, dist y y' ≤ ξ + 2 * A * δ := by
    rintro y ⟨l, hl, t, ht, rfl⟩ y' ⟨l', hl', t', ht', rfl⟩
    calc
      dist (Y l t) (Y l' t') ≤ dist (Y l t) (Y l t₀) +
          (dist (Y l t₀) (Y l' t₀) + dist (Y l' t₀) (Y l' t')) :=
        (dist_triangle (Y l t) (Y l t₀) (Y l' t')).trans
          (add_le_add le_rfl (dist_triangle (Y l t₀) (Y l' t₀) (Y l' t')))
      _ ≤ A * δ + (ξ + A * δ) := add_le_add (hYmove l hl t ht)
        (add_le_add (scalarVelocityBin_diameter_le hξpos (hY l hl) (hY l' hl'))
          (by rw [dist_comm]; exact hYmove l' hl' t' ht'))
      _ = _ := by ring
  have hxdiam : ∀ x ∈ RX, ∀ x' ∈ RX, dist x x' ≤ 3 * ζ := by
    rintro x ⟨l, hl, t, ht, rfl⟩ x' ⟨l', hl', t', ht', rfl⟩
    calc
      dist (X l t) (X l' t') ≤ dist (X l t) (X l t₀) +
          (dist (X l t₀) (X l' t₀) + dist (X l' t₀) (X l' t')) :=
        (dist_triangle (X l t) (X l t₀) (X l' t')).trans
          (add_le_add le_rfl (dist_triangle (X l t₀) (X l' t₀) (X l' t')))
      _ ≤ ζ + (ζ + ζ) := add_le_add (hXmove l hl t ht)
        (add_le_add (scalarVelocityBin_diameter_le hζ (hX l hl) (hX l' hl'))
          (by rw [dist_comm]; exact hXmove l' hl' t' ht'))
      _ = _ := by ring
  obtain ⟨hTf, hTc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    I hδ.le hδ 0 htime
  obtain ⟨hYf, hYc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    RY (by positivity : 0 ≤ ξ + 2 * A * δ) hδ 0 hydiam
  obtain ⟨hXf, hXc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    RX (by positivity : 0 ≤ 3 * ζ) hζ 0 hxdiam
  simp only [sub_zero] at hTf hTc hYf hYc hXf hXc
  let T : Finset ℤ := hTf.toFinset
  let J : Finset ℤ := hYf.toFinset
  let F : Finset ℤ := hXf.toFinset
  have hT : (T.card : ℝ) ≤ 4 := by
    rw [← Set.ncard_eq_toFinset_card _ hTf]
    exact hTc.trans_eq (by field_simp; ring)
  have hF : (F.card : ℝ) ≤ 8 := by
    rw [← Set.ncard_eq_toFinset_card _ hXf]
    exact hXc.trans_eq (by field_simp; ring)
  have hJ : (J.card : ℝ) ≤ 8 * A * ξ / δ := by
    rw [← Set.ncard_eq_toFinset_card _ hYf]
    apply hYc.trans
    have hratio : 1 ≤ ξ / δ := (one_le_div hδ).mpr hξ
    have he : 2 * (ξ + 2 * A * δ) / δ + 2 = 2 * (ξ / δ) + 4 * A + 2 := by
      field_simp
      ring
    rw [he]
    have hAx : ξ / δ ≤ A * (ξ / δ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ ξ / δ)
    have hAA : A ≤ A * (ξ / δ) := le_mul_of_one_le_right hApos.le hratio
    calc
      _ ≤ 2 * (A * (ξ / δ)) + 4 * (A * (ξ / δ)) + 2 * (A * (ξ / δ)) := by
        linarith [hA.trans hAA]
      _ = _ := by ring
  let Cell : ℤ → ℤ → ℤ → Set (α × ℝ) := fun i j b =>
    {ω | (⌊ω.2 / δ⌋ : ℤ) = i ∧ (⌊Y ω.1 ω.2 / δ⌋ : ℤ) = j ∧
      (⌊X ω.1 ω.2 / ζ⌋ : ℤ) = b ∧ V ω.1 ∈ P}
  have hcover : C ×ˢ I ⊆ ⋃ i ∈ T, ⋃ j ∈ J, ⋃ b ∈ F, Cell i j b := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    refine Set.mem_iUnion₂.mpr ⟨⌊t / δ⌋, ?_, Set.mem_iUnion₂.mpr ⟨⌊Y l t / δ⌋, ?_,
      Set.mem_iUnion₂.mpr ⟨⌊X l t / ζ⌋, ?_, ⟨rfl, rfl, rfl, hV l hl⟩⟩⟩⟩
    · exact hTf.mem_toFinset.mpr ⟨t, ht, rfl⟩
    · exact hYf.mem_toFinset.mpr ⟨Y l t, ⟨l, hl, t, ht, rfl⟩, rfl⟩
    · exact hXf.mem_toFinset.mpr ⟨X l t, ⟨l, hl, t, ht, rfl⟩, rfl⟩
  have hmass : μ (C ×ˢ I) ≤
      (T.card : ℝ≥0∞) * (J.card : ℝ≥0∞) * (F.card : ℝ≥0∞) *
        (ENNReal.ofReal (U * δ ^ 2 * B) * p) := by
    calc
      _ ≤ μ (⋃ i ∈ T, ⋃ j ∈ J, ⋃ b ∈ F, Cell i j b) := measure_mono hcover
      _ ≤ ∑ i ∈ T, ∑ j ∈ J, ∑ b ∈ F, μ (Cell i j b) := by
        apply (measure_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        apply (measure_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        exact measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ T, ∑ j ∈ J, ∑ b ∈ F, ENNReal.ofReal (U * δ ^ 2 * B) * p := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_le_sum (fun b hb => hcap i j b)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hcounts : (T.card : ℝ) * J.card * F.card ≤ 4 * (8 * A * ξ / δ) * 8 :=
    mul_le_mul (mul_le_mul hT hJ (Nat.cast_nonneg _) (by norm_num)) hF
      (Nat.cast_nonneg _) (by positivity)
  have hnum : ((T.card : ℝ) * J.card * F.card) * (U * δ ^ 2 * B) ≤
      256 * A * U * ξ * δ * B := by
    apply (mul_le_mul_of_nonneg_right hcounts (by positivity)).trans_eq
    field_simp
    ring
  have heq : (T.card : ℝ≥0∞) * (J.card : ℝ≥0∞) * (F.card : ℝ≥0∞) *
        (ENNReal.ofReal (U * δ ^ 2 * B) * p) =
      ENNReal.ofReal (((T.card : ℝ) * J.card * F.card) * (U * δ ^ 2 * B)) * p := by
    simp [ENNReal.ofReal_mul, mul_assoc]
  rw [heq] at hmass
  exact hmass.trans (mul_le_mul (ENNReal.ofReal_le_ofReal hnum) le_rfl bot_le bot_le)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
