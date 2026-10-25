import Mathlib

/- Developed in this workspace by x0047 for o015 and its endpoint-volume child. -/
import Submission.Lib.K4QuadraticSublevel

/-!
# A polynomial cardinal bound for separated subsets of a cube

The scalar floor-bin count is imported from the accepted local library. Taking
its finite product supplies the grid bound used for endpoint-map fibers.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set
open scoped BigOperators

/-- Integer coordinates of the half-open grid of mesh `δ`. -/
noncomputable def gridTag {m : ℕ} (δ : ℝ) (x : Fin m → ℝ) : Fin m → ℤ :=
  fun i => ⌊x i / δ⌋

lemma dist_le_mesh_of_gridTag_eq {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x y : Fin m → ℝ} (h : gridTag δ x = gridTag δ y) : dist x y ≤ δ := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro i
  have hi := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h i)
  change |x i / δ - y i / δ| < 1 at hi
  rw [← sub_div, abs_div, abs_of_pos hδ] at hi
  have hh : |x i - y i| < δ := (div_lt_one hδ).mp hi
  exact hh.le

lemma gridTag_injOn_of_separated {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Set (Fin m → ℝ))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y) : InjOn (gridTag δ) S := by
  intro x hx y hy hxy
  by_contra hne
  exact (not_le_of_gt (hsep x hx y hy hne)) (dist_le_mesh_of_gridTag_eq hδ hxy)

/-- A separated subset of a bounded sup-norm cube is finite, with a bound
polynomial in the ratio of the cube radius to the separation. -/
theorem finite_ncard_le_of_cube_separated {m : ℕ} (S : Set (Fin m → ℝ))
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ x ∈ S, ‖x‖ ≤ B)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ < dist x y) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * B / δ + 2) ^ m := by
  classical
  let bins : Fin m → Set ℤ := fun i =>
    (fun z : ℝ => ⌊(z - 0) / δ⌋) '' ((fun x : Fin m → ℝ => x i) '' S)
  have hscalar (i : Fin m) : (bins i).Finite ∧
      ((bins i).ncard : ℝ) ≤ 4 * B / δ + 2 := by
    have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      ((fun x : Fin m → ℝ => x i) '' S) (show 0 ≤ 2 * B by positivity) hδ 0 ?_
    · refine ⟨h.1, ?_⟩
      convert h.2 using 1 <;> ring
    · rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
      calc
        dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
        _ = ‖x - y‖ := dist_eq_norm x y
        _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        _ ≤ 2 * B := by linarith [hbound x hx, hbound y hy]
  let I : Finset (Fin m → ℤ) := Fintype.piFinset fun i => (hscalar i).1.toFinset
  have hmaps : MapsTo (gridTag δ) S (I : Set (Fin m → ℤ)) := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    rw [(hscalar i).1.mem_toFinset]
    exact ⟨x i, ⟨x, hx, rfl⟩, by simp [gridTag]⟩
  have hinj := gridTag_injOn_of_separated hδ S hsep
  have hfinite : S.Finite := Set.Finite.of_injOn hmaps hinj I.finite_toSet
  refine ⟨hfinite, ?_⟩
  have hcard : S.ncard ≤ I.card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard_of_injOn (gridTag δ) hmaps hinj
      I.finite_toSet
  calc
    (S.ncard : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hcard
    _ = ∏ i : Fin m, ((bins i).ncard : ℝ) := by
      simp only [I, Fintype.card_piFinset, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      exact_mod_cast (Set.ncard_eq_toFinset_card (bins i) (hscalar i).1).symm
    _ ≤ ∏ _i : Fin m, (4 * B / δ + 2) :=
      Finset.prod_le_prod₀ (fun i hi => Nat.cast_nonneg _) (fun i hi => (hscalar i).2)
    _ = (4 * B / δ + 2) ^ m := by simp

end Submission.Obl.k4_matching_endpoint_volume
