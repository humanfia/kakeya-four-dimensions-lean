/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PhysicalSupportCover.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle

/-! Physical support counts from base extent and hidden-coordinate oscillation. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set
open scoped Classical BigOperators

def physicalScalarGridTag (ξ : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℤ :=
  fun e => ⌊p e / ξ⌋

def physicalScalarRectangularTag (ξ ζ : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℤ :=
  ![⌊p 0 / ξ⌋,⌊p 1 / ξ⌋,⌊p 2 / ζ⌋]

/-- Count the physical cubes of an arbitrary set, using only its base extent and
the hidden-coordinate diameter inside each base cube. No regularity of the set is needed. -/
theorem physical_rectangular_grid_cover_of_base_fibers (S : Set (Fin 3 → ℝ))
    (ξ ζ h A B t₀ y₀ : ℝ) (hξ : 0 < ξ) (hζ : 0 < ζ) (hξh : ξ ≤ h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htime : ∀ p ∈ S, p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ S, |p 1 - y₀| ≤ A * h)
    (hhidden : ∀ p ∈ S, ∀ p' ∈ S,
      (⌊p 0 / ξ⌋ : ℤ) = ⌊p' 0 / ξ⌋ → (⌊p 1 / ξ⌋ : ℤ) = ⌊p' 1 / ξ⌋ →
        dist (p 2) (p' 2) ≤ B * ζ) :
    (physicalScalarRectangularTag ξ ζ '' S).Finite ∧
      ((physicalScalarRectangularTag ξ ζ '' S).ncard : ℝ) ≤
        4 * (4 * A + 2) * (2 * B + 2) * (h / ξ) ^ 2 := by
  have hh : 0 < h := hξ.trans_le hξh
  have hratio : 1 ≤ h / ξ := (one_le_div hξ).mpr hξh
  have htdiam : ∀ t ∈ (fun p : Fin 3 → ℝ => p 0) '' S,
      ∀ t' ∈ (fun p : Fin 3 → ℝ => p 0) '' S, dist t t' ≤ h := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [(htime p hp).1, (htime p' hp').2],
      by linarith [(htime p hp).2, (htime p' hp').1]⟩
  have hydiam : ∀ y ∈ (fun p : Fin 3 → ℝ => p 1) '' S,
      ∀ y' ∈ (fun p : Fin 3 → ℝ => p 1) '' S, dist y y' ≤ 2 * A * h := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    rw [Real.dist_eq]
    calc
      _ ≤ |p 1 - y₀| + |p' 1 - y₀| := by
        simpa only [abs_sub_comm] using abs_sub_le (p 1) y₀ (p' 1)
      _ ≤ A * h + A * h := add_le_add (hY p hp) (hY p' hp')
      _ = _ := by ring
  obtain ⟨hTf, hTc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    ((fun p : Fin 3 → ℝ => p 0) '' S) hh.le hξ 0 htdiam
  obtain ⟨hJf, hJc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    ((fun p : Fin 3 → ℝ => p 1) '' S) (by positivity : 0 ≤ 2 * A * h) hξ 0 hydiam
  simp only [sub_zero] at hTf hTc hJf hJc
  let T := hTf.toFinset
  let J := hJf.toFinset
  have hT : (T.card : ℝ) ≤ 4 * h / ξ := by
    rw [← Set.ncard_eq_toFinset_card _ hTf]
    apply hTc.trans
    simp only [mul_div_assoc]
    linarith
  have hJ : (J.card : ℝ) ≤ (4 * A + 2) * h / ξ := by
    rw [← Set.ncard_eq_toFinset_card _ hJf]
    apply hJc.trans
    have he : 2 * (2 * A * h) / ξ + 2 = 4 * A * (h / ξ) + 2 := by ring
    rw [he, mul_div_assoc]
    nlinarith
  let X : ℤ → ℤ → Set ℝ := fun i j =>
    {x | ∃ p ∈ S, (⌊p 0 / ξ⌋ : ℤ) = i ∧ (⌊p 1 / ξ⌋ : ℤ) = j ∧ p 2 = x}
  have hXdiam (i j : ℤ) : ∀ x ∈ X i j, ∀ x' ∈ X i j, dist x x' ≤ B * ζ := by
    rintro _ ⟨p, hp, hpi, hpj, rfl⟩ _ ⟨p', hp', hp'i, hp'j, rfl⟩
    exact hhidden p hp p' hp' (hpi.trans hp'i.symm) (hpj.trans hp'j.symm)
  have hXfinite (i j : ℤ) :=
    Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le (X i j)
      (mul_nonneg hB hζ.le) hζ 0 (hXdiam i j)
  simp only [sub_zero] at hXfinite
  let F : ℤ → ℤ → Finset ℤ := fun i j => (hXfinite i j).1.toFinset
  have hF (i j : ℤ) : ((F i j).card : ℝ) ≤ 2 * B + 2 := by
    rw [← Set.ncard_eq_toFinset_card _ (hXfinite i j).1]
    exact (hXfinite i j).2.trans_eq (by field_simp)
  let Codes : Finset (Fin 3 → ℤ) := T.biUnion fun i =>
    J.biUnion fun j => (F i j).image fun b => ![i,j,b]
  have hcover : physicalScalarRectangularTag ξ ζ '' S ⊆ (Codes : Set (Fin 3 → ℤ)) := by
    rintro q ⟨p, hp, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊p 0 / ξ⌋, hTf.mem_toFinset.mpr ⟨p 0, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊p 1 / ξ⌋, hJf.mem_toFinset.mpr ⟨p 1, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨⌊p 2 / ζ⌋, ?_, ?_⟩
    · exact (hXfinite _ _).1.mem_toFinset.mpr
        ⟨p 2, ⟨p, hp, rfl, rfl, rfl⟩, rfl⟩
    · ext e
      fin_cases e <;> rfl
  have hcard : (Codes.card : ℝ) ≤ (T.card : ℝ) * J.card * (2 * B + 2) := by
    calc
      _ ≤ ∑ i ∈ T, ((J.biUnion fun j => (F i j).image fun b => ![i,j,b]).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ T, ∑ j ∈ J, (((F i j).image fun b => ![i,j,b]).card : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ i ∈ T, ∑ j ∈ J, ((F i j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum fun j hj => Nat.cast_le.mpr Finset.card_image_le
      _ ≤ ∑ i ∈ T, ∑ j ∈ J, (2 * B + 2) := by
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hF i j
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  refine ⟨Codes.finite_toSet.subset hcover, ?_⟩
  calc
    _ ≤ (Codes.card : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hcover Codes.finite_toSet
    _ ≤ (T.card : ℝ) * J.card * (2 * B + 2) := hcard
    _ ≤ (4 * h / ξ) * ((4 * A + 2) * h / ξ) * (2 * B + 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hT hJ (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring


/-- Equal base and hidden widths give the ordinary physical grid. -/
theorem physical_grid_cover_of_base_fibers (S : Set (Fin 3 → ℝ))
    (ξ h A B t₀ y₀ : ℝ) (hξ : 0 < ξ) (hξh : ξ ≤ h) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htime : ∀ p ∈ S, p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ S, |p 1 - y₀| ≤ A * h)
    (hhidden : ∀ p ∈ S, ∀ p' ∈ S,
      (⌊p 0 / ξ⌋ : ℤ) = ⌊p' 0 / ξ⌋ → (⌊p 1 / ξ⌋ : ℤ) = ⌊p' 1 / ξ⌋ →
        dist (p 2) (p' 2) ≤ B * ξ) :
    (physicalScalarGridTag ξ '' S).Finite ∧
      ((physicalScalarGridTag ξ '' S).ncard : ℝ) ≤
        4 * (4 * A + 2) * (2 * B + 2) * (h / ξ) ^ 2 := by
  have hc := physical_rectangular_grid_cover_of_base_fibers S ξ ξ h A B t₀ y₀
    hξ hξ hξh hA hB htime hY hhidden
  have he : physicalScalarRectangularTag ξ ξ = physicalScalarGridTag ξ := by
    funext p e
    fin_cases e <;> rfl
  simpa only [he] using hc

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
