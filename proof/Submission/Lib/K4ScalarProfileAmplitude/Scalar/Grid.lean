/- Adapted from: here:o266
Original accepted finite kernel: here:o016, session x0049.
Original file: Submission/Obl/k4_scalar_coefficient_clustering/Grid.lean.
The accepted scalar binning/lifting kernels are packaged here because
shared-library contributions cannot import obligation modules. -/
import Submission.Lib.K4ScalarProfileAmplitude.Scalar.Geometry
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Lib.K4ScalarProfileAmplitude.Scalar

open Set

noncomputable section

def coefficientCode (p : ℝ) (a : Coeff) : Fin 3 → ℤ := fun j => ⌊a j / p⌋

/-- Distinct coefficient codes in a family of diameter L have a cubic grid bound. -/
theorem card_coefficient_codes {ι : Type*} (S : Finset ι) (a : ι → Coeff)
    {p L : ℝ} (hp : 0 < p) (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, ‖a i - a j‖ ≤ L) :
    ((S.image (coefficientCode p ∘ a)).card : ℝ) ≤ (2 * L / p + 2) ^ 3 := by
  classical
  let Q : Fin 3 → Finset ℤ := fun j => S.image (fun i => ⌊a i j / p⌋)
  have hcard : ∀ j, ((Q j).card : ℝ) ≤ 2 * L / p + 2 := by
    intro j
    have hh := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      ((fun i => a i j) '' (↑S : Set ι)) hL hp 0 (by
        rintro x ⟨i, hi, rfl⟩ y ⟨k, hk, rfl⟩
        have hc := (PiLp.norm_apply_le (a i - a k) j).trans (hdiam i hi k hk)
        simpa only [Real.dist_eq, Real.norm_eq_abs, PiLp.sub_apply] using hc)
    have heq : (fun x : ℝ => ⌊(x - 0) / p⌋) '' ((fun i => a i j) '' (↑S : Set ι)) =
        (↑(Q j) : Set ℤ) := by
      simp [Q, Finset.coe_image, Set.image_image]
    rw [heq, Set.ncard_coe_finset] at hh
    exact hh.2
  have hsub : S.image (coefficientCode p ∘ a) ⊆ Fintype.piFinset Q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨i, hi, rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  calc
    ((S.image (coefficientCode p ∘ a)).card : ℝ) ≤ ((Fintype.piFinset Q).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = ∏ j, ((Q j).card : ℝ) := by simp
    _ ≤ ∏ _j : Fin 3, (2 * L / p + 2) := by
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hcard j)
    _ = (2 * L / p + 2) ^ 3 := by simp

/-- A specialized use of the shared one-dimensional grid-counting estimate. -/
theorem card_fin_grid_of_diameter {D : ℕ} (S : Finset (Fin D)) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ L) :
    (S.card : ℝ) ≤ 2 * L + 2 := by
  let f : Fin D → ℝ := fun i => (i : ℕ)
  have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (f '' (↑S : Set (Fin D))) hL (by norm_num : (0 : ℝ) < 1) 0 (by
      rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩
      exact hdiam i hi j hj)
  have himg : (fun x : ℝ => ⌊(x - 0) / 1⌋) '' (f '' (↑S : Set (Fin D))) =
      (fun i : Fin D => ((i : ℕ) : ℤ)) '' (↑S : Set (Fin D)) := by
    simp [Set.image_image, f]
  have hinj : Function.Injective (fun i : Fin D => ((i : ℕ) : ℤ)) := by
    intro i j hij
    exact Fin.ext (Int.ofNat_inj.mp hij)
  have hc := h.2
  rw [himg, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset] at hc
  simpa using hc

theorem card_int_grid_of_diameter (S : Finset ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, |(i : ℝ) - (j : ℝ)| ≤ L) :
    (S.card : ℝ) ≤ 2 * L + 2 := by
  have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (((↑) : ℤ → ℝ) '' (↑S : Set ℤ)) hL (by norm_num : (0 : ℝ) < 1) 0 (by
      rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩
      exact hdiam i hi j hj)
  have himg : (fun x : ℝ => ⌊(x - 0) / 1⌋) '' (((↑) : ℤ → ℝ) '' (↑S : Set ℤ)) =
      (↑S : Set ℤ) := by simp [Set.image_image]
  rw [himg, Set.ncard_coe_finset] at h
  simpa using h.2

theorem card_le_image_mul_fiber {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (f : ι → κ) (M : ℝ)
    (hM : ∀ q ∈ S.image f, ((S.filter (fun i => f i = q)).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ ((S.image f).card : ℝ) * M := by
  classical
  have hs := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [← hs]
  calc
    (∑ q ∈ S.image f, ((S.filter (fun i => f i = q)).card : ℝ)) ≤ ∑ _q ∈ S.image f, M :=
      Finset.sum_le_sum hM
    _ = _ := by simp

/-- Only O(D times physical narrow width) points of the auxiliary grid fit a plank. -/
theorem card_dummy_in_plank {D : ℕ} (hD : 1 ≤ D) {R α : ℝ} (hR : 1 ≤ R)
    (hα : 1 ≤ α) {c w e : Plane} {a : Coeff} (he : ‖e‖ = 1)
    (S : Finset (Fin D))
    (hS : ∀ k ∈ S, InNarrowPlank c w e (R * α / (D : ℝ)) a
      (((k : ℕ) : ℝ) / (D : ℝ))) :
    (S.card : ℝ) ≤ 18 * R * α := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hdiam : ∀ i ∈ S, ∀ j ∈ S,
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ 8 * R * α := by
    intro i hi j hj
    have h := dummy_gap_in_plank he (hS i hi) (hS j hj)
    rw [← sub_div, abs_div, abs_of_pos hDpos] at h
    have hh := (div_le_iff₀ hDpos).mp h
    have heq : 8 * (R * α / (D : ℝ)) * (D : ℝ) = 8 * R * α := by
      field_simp
    exact hh.trans_eq heq
  have hh := card_fin_grid_of_diameter S (by positivity : 0 ≤ 8 * R * α) hdiam
  have hmul : 1 ≤ R * α := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hα)]
  nlinarith

end
end Submission.Lib.K4ScalarProfileAmplitude.Scalar
