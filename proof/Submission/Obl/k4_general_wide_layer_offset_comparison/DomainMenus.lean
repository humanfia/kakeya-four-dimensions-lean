import Submission.Lib.K4MovingMeshBoxes.Geometry
import Mathlib.MeasureTheory.Function.Floor

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/DomainMenus.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set
open scoped ENNReal

noncomputable section

/-- Time, transverse velocity, and transverse position at the left endpoint
are recorded before any pair restriction is made. -/
def movingDomainCode (h g b a w t : ℝ) : ℤ × ℤ × ℤ :=
  let j := ⌊t / h⌋
  (j, ⌊w / g⌋, ⌊(a + (j : ℝ) * h * w) / b⌋)

theorem affine_band_velocity_bound {a w u v M : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a + t * w - u - t * v| ≤ M) :
    |w - v| ≤ 2 * M := by
  have h₀ := h 0 (by norm_num)
  have h₁ := h 1 (by norm_num)
  norm_num only [zero_mul, one_mul, add_zero, sub_zero] at h₀ h₁
  calc
    _ = |(a + w - u - v) - (a - u)| := by congr 1; ring
    _ ≤ |a + w - u - v| + |a - u| := abs_sub _ _
    _ ≤ M + M := add_le_add h₁ h₀
    _ = _ := by ring

/-- A projected label has only the expected number of common-domain
options. Multiplication by the domain Jacobian `h*b` recovers its original
whole-interval width `beta`. -/
theorem exists_moving_domain_menu
    {H β h g b : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hh1 : h ≤ 1)
    (hb : 0 < b) (hbβ : b ≤ β) (hβg : β ≤ g) (u v : ℝ) :
    ∃ D : Finset (ℤ × ℤ × ℤ),
      (D.card : ℝ) ≤ 240 * H ^ 2 * β / (h * b) ∧
      ∀ a w t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (∀ t' ∈ Icc (0 : ℝ) 1, |a + t' * w - u - t' * v| ≤ H * β) →
        movingDomainCode h g b a w t ∈ D := by
  classical
  have hH0 : 0 ≤ H := by linarith
  have hβ : 0 < β := hb.trans_le hbβ
  have hg : 0 < g := hβ.trans_le hβg
  obtain ⟨Ft, hFt, htime⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hh (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2)
  obtain ⟨Fv, hFv, hvelocity⟩ :=
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hg
      (by positivity : 0 ≤ 2 * H * β) v
  choose Fy hFy hposition using fun j : ℤ =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hb
      (by positivity : 0 ≤ H * β) (u + (j : ℝ) * h * v)
  have hFt' : (Ft.card : ℝ) ≤ 4 / h := by
    apply hFt.trans
    apply (le_div_iff₀ hh).mpr
    field_simp
    nlinarith
  have hFv' : (Fv.card : ℝ) ≤ 10 * H := by
    apply hFv.trans
    have hratio : 4 * (2 * H * β) / g ≤ 8 * H := by
      apply (div_le_iff₀ hg).mpr
      nlinarith [mul_le_mul_of_nonneg_left hβg hH0]
    linarith
  have hFy' (j : ℤ) : ((Fy j).card : ℝ) ≤ 6 * H * β / b := by
    apply (hFy j).trans
    apply (le_div_iff₀ hb).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hH hβ.le]
  let D : Finset (ℤ × ℤ × ℤ) :=
    Ft.biUnion (fun j => (Fv.product (Fy j)).image (fun p => (j, p.1, p.2)))
  refine ⟨D, ?_, ?_⟩
  · calc
      (D.card : ℝ) ≤ ∑ j ∈ Ft, (((Fv.product (Fy j)).image (fun p => (j, p.1, p.2))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Ft, (Fv.card : ℝ) * ((Fy j).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact_mod_cast (Finset.card_image_le.trans_eq (Finset.card_product Fv (Fy j)))
      _ ≤ ∑ _j ∈ Ft, (10 * H) * (6 * H * β / b) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul hFv' (hFy' j) (Nat.cast_nonneg _) (by positivity)
      _ = (Ft.card : ℝ) * ((10 * H) * (6 * H * β / b)) := by simp
      _ ≤ (4 / h) * ((10 * H) * (6 * H * β / b)) := by gcongr
      _ = 240 * H ^ 2 * β / (h * b) := by ring
  · intro a w t ht hband
    let j : ℤ := ⌊t / h⌋
    have hj : j ∈ Ft := htime t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Int.floor_nonneg.mpr (div_nonneg ht.1 hh.le))
    have hjt : (j : ℝ) * h ≤ t := (le_div_iff₀ hh).mp (Int.floor_le (t / h))
    have htj : (j : ℝ) * h ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hj0 hh.le, hjt.trans ht.2⟩
    have hw : ⌊w / g⌋ ∈ Fv := hvelocity w (by
      simpa only [mul_assoc] using affine_band_velocity_bound hband)
    have hy : ⌊(a + (j : ℝ) * h * w) / b⌋ ∈ Fy j := by
      apply hposition j
      convert hband ((j : ℝ) * h) htj using 1 <;> congr 1 <;> ring
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_image.mpr ?_⟩
    exact ⟨(_, _), Finset.mem_product.mpr ⟨hw, hy⟩, rfl⟩

/-- All common-domain options are charged to the original projected
weights before any current pair masses are inspected. -/
theorem exists_moving_domain_menus_with_budget
    {ι : Type*} [Fintype ι] {H h g b : ℝ}
    (hH : 1 ≤ H) (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b)
    (β u v : ι → ℝ) (hbβ : ∀ i, b ≤ β i) (hβg : ∀ i, β i ≤ g)
    (w : ι → ℝ≥0∞) :
    ∃ D : ι → Finset (ℤ × ℤ × ℤ),
      (∀ i a v' t, t ∈ Icc (0 : ℝ) 1 →
        (∀ t' ∈ Icc (0 : ℝ) 1, |a + t' * v' - u i - t' * v i| ≤ H * β i) →
        movingDomainCode h g b a v' t ∈ D i) ∧
      (∑ i, ((D i).card : ℝ≥0∞) * (ENNReal.ofReal (h * b) * w i)) ≤
        ENNReal.ofReal (240 * H ^ 2) * ∑ i, ENNReal.ofReal (β i) * w i := by
  classical
  choose D hcount hcover using fun i =>
    exists_moving_domain_menu hH hh hh1 hb (hbβ i) (hβg i) (u i) (v i)
  refine ⟨D, hcover, ?_⟩
  have hcost (i : ι) : ((D i).card : ℝ≥0∞) * ENNReal.ofReal (h * b) ≤
      ENNReal.ofReal (240 * H ^ 2 * β i) := by
    have hr := (le_div_iff₀ (mul_pos hh hb)).mp (hcount i)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hr
  calc
    _ = ∑ i, (((D i).card : ℝ≥0∞) * ENNReal.ofReal (h * b)) * w i := by
      simp only [mul_assoc]
    _ ≤ ∑ i, ENNReal.ofReal (240 * H ^ 2 * β i) * w i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_left (hcost i) _)
    _ = ∑ i, ENNReal.ofReal (240 * H ^ 2) * (ENNReal.ofReal (β i) * w i) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 240 * H ^ 2), mul_assoc]
    _ = _ := (Finset.mul_sum ..).symm

/-- Every occurrence lies in the moving box associated to its domain code.
The code is the same for every later restriction or pairing. -/
theorem moving_domain_geometry {h g b : ℝ} (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    (a w t : ℝ) :
    let c := movingDomainCode h g b a w t
    |t - (c.1 : ℝ) * h| ≤ h ∧
    |a + t * w - ((c.2.2 : ℝ) * b + (t - (c.1 : ℝ) * h) * ((c.2.1 : ℝ) * g))| ≤
      b + h * g := by
  let j : ℤ := ⌊t / h⌋
  let r : ℤ := ⌊w / g⌋
  let y : ℤ := ⌊(a + (j : ℝ) * h * w) / b⌋
  have bin (x δ : ℝ) (hδ : 0 < δ) : |x - (⌊x / δ⌋ : ℝ) * δ| ≤ δ := by
    have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (x / δ))
    have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x / δ))
    rw [abs_le]
    constructor <;> linarith
  have ht : |t - (j : ℝ) * h| ≤ h := bin t h hh
  have hw : |w - (r : ℝ) * g| ≤ g := bin w g hg
  have hy : |a + (j : ℝ) * h * w - (y : ℝ) * b| ≤ b := bin _ b hb
  refine ⟨ht, ?_⟩
  change |a + t * w - ((y : ℝ) * b + (t - (j : ℝ) * h) * ((r : ℝ) * g))| ≤ _
  calc
    _ = |(a + (j : ℝ) * h * w - (y : ℝ) * b) +
        (t - (j : ℝ) * h) * (w - (r : ℝ) * g)| := by congr 1; ring
    _ ≤ |a + (j : ℝ) * h * w - (y : ℝ) * b| +
        |(t - (j : ℝ) * h) * (w - (r : ℝ) * g)| := abs_add_le _ _
    _ ≤ b + h * g := by
      rw [abs_mul]
      exact add_le_add hy (mul_le_mul ht hw (abs_nonneg _) hh.le)

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
