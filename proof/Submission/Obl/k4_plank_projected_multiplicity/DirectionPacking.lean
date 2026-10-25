import Submission.Obl.k4_plank_projected_multiplicity.Basic
import Submission.Obl.k4_scalar_coefficient_clustering.Grid

namespace Submission.Obl.k4_plank_projected_multiplicity

open Set Finset

noncomputable section

theorem abs_sub_le_mesh_of_floor_eq {x y p : ℝ} (hp : 0 < p)
    (h : ⌊x / p⌋ = ⌊y / p⌋) : |x - y| ≤ p := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hp] at hh
  simpa only [one_mul] using ((div_lt_iff₀ hp).mp hh).le

/-- Count a grid in a box with a separate diameter in each coordinate. -/
theorem card_grid_codes_of_coordinate_diameters {ι : Type*}
    (S : Finset ι) (x : ι → Fin 3 → ℝ) {p : ℝ} (hp : 0 < p)
    (L : Fin 3 → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hdiam : ∀ i ∈ S, ∀ i' ∈ S, ∀ j, |x i j - x i' j| ≤ L j) :
    ((S.image (fun i => fun j => ⌊x i j / p⌋)).card : ℝ) ≤
      ∏ j : Fin 3, (2 * L j / p + 4) := by
  classical
  let Q : Fin 3 → Finset ℤ := fun j => S.image (fun i => ⌊x i j / p⌋)
  have hQ : ∀ j, ((Q j).card : ℝ) ≤ 2 * L j / p + 4 := by
    intro j
    have hh := Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter
      (Q j) (L := L j / p + 1) (by have := hL j; positivity) (by
        rintro z hz z' hz'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hz'
        have hxy : |x i j / p - x i' j / p| ≤ L j / p := by
          rw [← sub_div, abs_div, abs_of_pos hp]
          exact div_le_div_of_nonneg_right (hdiam i hi i' hi' j) hp.le
        have hxi := Int.floor_le (x i j / p)
        have hxj := Int.floor_le (x i' j / p)
        have hix := Int.lt_floor_add_one (x i j / p)
        have hjx := Int.lt_floor_add_one (x i' j / p)
        apply abs_le.mpr
        have hxy' := abs_le.mp hxy
        constructor <;> linarith)
    convert hh using 1 <;> ring
  have hsub : S.image (fun i => fun j => ⌊x i j / p⌋) ⊆ Fintype.piFinset Q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  calc
    ((S.image (fun i => fun j => ⌊x i j / p⌋)).card : ℝ) ≤
        ((Fintype.piFinset Q).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ∏ j : Fin 3, ((Q j).card : ℝ) := by simp
    _ ≤ ∏ j : Fin 3, (2 * L j / p + 4) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hQ j)

def planarPart (s : E3) : E2 := WithLp.toLp 2 ![s 0, s 1]

def orthogonalSlopeCoordinates (e₁ e₂ : E2) (s : E3) : Fin 3 → ℝ :=
  ![inner ℝ (planarPart s) e₁, inner ℝ (planarPart s) e₂, s 2]

/-- A small common grid code in orthogonal coordinates contradicts slope separation. -/
theorem orthogonal_slope_codes_injOn {ι : Type*} (S : Finset ι) (s : ι → E3)
    {δ : ℝ} (hδ : 0 < δ) (e₁ e₂ : E2)
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ ‖s i - s j‖) :
    Set.InjOn (fun i => fun j => ⌊orthogonalSlopeCoordinates e₁ e₂ (s i) j / (δ / 16)⌋)
      (↑S : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  have hmesh : 0 < δ / 16 := by positivity
  have hcoord (k : Fin 3) :
      |orthogonalSlopeCoordinates e₁ e₂ (s i) k -
        orthogonalSlopeCoordinates e₁ e₂ (s j) k| ≤ δ / 16 :=
    abs_sub_le_mesh_of_floor_eq hmesh (congrFun hij k)
  have hplanar : planarPart (s i - s j) = planarPart (s i) - planarPart (s j) := by
    ext k
    fin_cases k <;> rfl
  have hnorm : ‖planarPart (s i - s j)‖ ≤ 2 * (δ / 16) := by
    apply Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_two_mul h₁ h₂ ho
    · rw [hplanar, inner_sub_left]
      exact hcoord 0
    · rw [hplanar, inner_sub_left]
      exact hcoord 1
  have hfull : ‖s i - s j‖ ≤ 3 * (2 * (δ / 16)) := by
    apply trajectory_norm_le (by positivity)
    intro k
    fin_cases k
    · exact (PiLp.norm_apply_le (planarPart (s i - s j)) 0).trans hnorm
    · exact (PiLp.norm_apply_le (planarPart (s i - s j)) 1).trans hnorm
    · have hh := hcoord 2
      change |s i 2 - s j 2| ≤ 2 * (δ / 16)
      have hh' : |s i 2 - s j 2| ≤ δ / 16 := by
        simpa [orthogonalSlopeCoordinates] using hh
      linarith
  have hh := hsep i hi j hj hne
  linarith

/-- An anisotropic rectangular cap for a separated three-dimensional slope family. -/
theorem separated_slopes_in_rectangular_plank {ι : Type*} (S : Finset ι) (s : ι → E3)
    {δ a β R : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (e₁ e₂ w : E2) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ ‖s i - s j‖)
    (hrect : ∀ i ∈ S, |inner ℝ (planarPart (s i) - w) e₁| ≤ a ∧
      |inner ℝ (planarPart (s i) - w) e₂| ≤ β ∧ |s i 2| ≤ R) :
    (S.card : ℝ) ≤ (64 * a / δ + 4) * (64 * β / δ + 4) * (64 * R / δ + 4) := by
  classical
  have hdiam : ∀ i ∈ S, ∀ j ∈ S, ∀ k : Fin 3,
      |orthogonalSlopeCoordinates e₁ e₂ (s i) k -
        orthogonalSlopeCoordinates e₁ e₂ (s j) k| ≤ (![2 * a, 2 * β, 2 * R] : Fin 3 → ℝ) k := by
    intro i hi j hj k
    have hi' := hrect i hi
    have hj' := hrect j hj
    simp only [inner_sub_left] at hi' hj'
    have hi1 := abs_le.mp hi'.1
    have hj1 := abs_le.mp hj'.1
    have hi2 := abs_le.mp hi'.2.1
    have hj2 := abs_le.mp hj'.2.1
    have hi3 := abs_le.mp hi'.2.2
    have hj3 := abs_le.mp hj'.2.2
    fin_cases k <;> dsimp [orthogonalSlopeCoordinates]
    all_goals apply abs_le.mpr; constructor <;> linarith
  have hh := card_grid_codes_of_coordinate_diameters S (fun i => orthogonalSlopeCoordinates e₁ e₂ (s i))
    (show 0 < δ / 16 by positivity) ![2 * a, 2 * β, 2 * R]
    (by intro k; fin_cases k <;> simp <;> positivity) hdiam
  rw [Finset.card_image_of_injOn
    (orthogonal_slope_codes_injOn S s hδ e₁ e₂ h₁ h₂ ho hsep)] at hh
  convert hh using 1
  simp only [Fin.prod_univ_three]
  dsimp
  ring

theorem separated_slopes_plank_card {ι : Type*} (S : Finset ι) (s : ι → E3)
    {δ α β R : ℝ} (hδ : 0 < δ) (hα : 1 ≤ α) (hβ : 1 ≤ β) (hR : δ ≤ R)
    (e₁ e₂ w : E2) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ ‖s i - s j‖)
    (hrect : ∀ i ∈ S, |inner ℝ (planarPart (s i) - w) e₁| ≤ α * δ ∧
      |inner ℝ (planarPart (s i) - w) e₂| ≤ β * δ ∧ |s i 2| ≤ R) :
    (S.card : ℝ) ≤ 314432 * α * β * R / δ := by
  have hRp : 0 < R := hδ.trans_le hR
  have hRD : 1 ≤ R / δ := (le_div_iff₀ hδ).mpr (by simpa using hR)
  have hcard := separated_slopes_in_rectangular_plank S s hδ (by positivity)
    (by positivity) hRp.le e₁ e₂ w h₁ h₂ ho hsep hrect
  have hEq : 64 * (α * δ) / δ + 4 = 64 * α + 4 := by field_simp
  have hEq' : 64 * (β * δ) / δ + 4 = 64 * β + 4 := by field_simp
  rw [hEq, hEq'] at hcard
  calc
    (S.card : ℝ) ≤ (64 * α + 4) * (64 * β + 4) * (64 * R / δ + 4) := hcard
    _ ≤ (68 * α) * (68 * β) * (68 * R / δ) := by
      gcongr
      · linarith
      · linarith
      · simp only [mul_div_assoc]
        linarith
    _ = 314432 * α * β * R / δ := by ring

end

end Submission.Obl.k4_plank_projected_multiplicity
