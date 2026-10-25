/-
Adapted from this LOT tree, obligation o093, session x0535, commit b0d1e0aa,
Submission/Obl/k4_scalar_critical_path_terminal/PointStateCounts.lean. Original attribution is retained below.
-/
import Submission.Lib.K4QuadraticSublevel

/-! Finite point-state records from relative coordinate diameters.
The one-dimensional grid bound is the accepted shared library theorem;
only the finite product of its coordinate sets is assembled here. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts

open Set

noncomputable section

def record {X ι : Type*} (state : X → ι → ℝ) (δ : ι → ℝ) (x : X) : ι → ℤ :=
  fun i => ⌊state x i / δ i⌋

theorem records_finite_card {X ι : Type*} [Fintype ι]
    (S : Set X) (state : X → ι → ℝ) (δ L : ι → ℝ)
    (hδ : ∀ i, 0 < δ i) (hL : ∀ i, 0 ≤ L i)
    (hdiam : ∀ i, ∀ x ∈ S, ∀ y ∈ S, |state x i - state y i| ≤ L i) :
    (record state δ '' S).Finite ∧
      ((record state δ '' S).ncard : ℝ) ≤ ∏ i, (2 * L i / δ i + 2) := by
  classical
  have hcoord (i : ι) :
      ((fun x => (⌊state x i / δ i⌋ : ℤ)) '' S).Finite ∧
        (((fun x => (⌊state x i / δ i⌋ : ℤ)) '' S).ncard : ℝ) ≤ 2 * L i / δ i + 2 := by
    have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      ((fun x => state x i) '' S) (hL i) (hδ i) 0 (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        simpa only [Real.dist_eq] using hdiam i x hx y hy)
    simpa only [Set.image_image, sub_zero, Function.comp_def] using h
  let Q : ι → Finset ℤ := fun i => (hcoord i).1.toFinset
  have hsub : record state δ '' S ⊆ (↑(Fintype.piFinset Q) : Set (ι → ℤ)) := by
    rintro _ ⟨x, hx, rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    change (⌊state x i / δ i⌋ : ℤ) ∈ (hcoord i).1.toFinset
    exact (hcoord i).1.mem_toFinset.mpr ⟨x, hx, rfl⟩
  have hfinite := (Fintype.piFinset Q).finite_toSet
  refine ⟨hfinite.subset hsub, ?_⟩
  calc
    _ ≤ ((Fintype.piFinset Q).card : ℝ) := by
      exact_mod_cast (Set.ncard_le_ncard hsub hfinite).trans_eq (Set.ncard_coe_finset _)
    _ = ∏ i, ((Q i).card : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro i _
      have h := (hcoord i).2
      rw [Set.ncard_eq_toFinset_card _ (hcoord i).1] at h
      exact h

/-- A common relative diameter gives an explicit finite ambiguity bound
for ANY finite collection of tested depths and point coordinates. -/
theorem records_finite_card_of_relative_diameter {X ι : Type*} [Fintype ι]
    (S : Set X) (state : X → ι → ℝ) (δ : ι → ℝ) (A : ℝ)
    (hδ : ∀ i, 0 < δ i) (hA : 0 ≤ A)
    (hdiam : ∀ i, ∀ x ∈ S, ∀ y ∈ S, |state x i - state y i| ≤ A * δ i) :
    (record state δ '' S).Finite ∧
      ((record state δ '' S).ncard : ℝ) ≤ (2 * A + 2) ^ Fintype.card ι := by
  obtain ⟨hfinite, hcard⟩ := records_finite_card S state δ (fun i => A * δ i)
    hδ (fun i => mul_nonneg hA (hδ i).le) hdiam
  refine ⟨hfinite, ?_⟩
  have heq (i : ι) : 2 * (A * δ i) / δ i + 2 = 2 * A + 2 := by
    field_simp [(hδ i).ne']
  simpa only [heq, Finset.prod_const, Finset.card_univ] using hcard

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts
