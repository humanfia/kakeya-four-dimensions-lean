/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedDomainBudget.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomains
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! The common domains met by one full-time projected label have its original reference budget. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Set

noncomputable section

theorem projected_velocity_error (b : Fin 6 → ℝ) {u v E : ℝ}
    (hfit : ∀ t ∈ Icc (0 : ℝ) 1, |b 1 + t * b 4 - u - t * v| ≤ E) :
    |b 4 - v| ≤ 2 * E := by
  have h₀ := hfit 0 (by constructor <;> norm_num)
  have h₁ := hfit 1 (by constructor <;> norm_num)
  have hid : b 4 - v = (b 1 + 1 * b 4 - u - 1 * v) - (b 1 + 0 * b 4 - u - 0 * v) := by ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

/-- A literal finite domain menu for one projected label. Multiplying its cardinality
by the time and transverse cell widths gives at most `360 H³ β`, independently of
the number of fine cells and of the original major coefficient tag. -/
theorem projected_domain_menu {H q g m β : ℝ} (hH : 1 ≤ H)
    (hq : 0 < q) (hq1 : q ≤ 1) (hg : 0 < g) (hm : 0 < m)
    (hmβ : m ≤ β) (hβg : β ≤ H * g) (χ u v : ℝ) (tag : Fin 2 → ℤ) :
    ∃ S : Finset Code, (S.card : ℝ) * q * m ≤ 360 * H ^ 3 * β ∧
      (∀ c ∈ S, c 1 = tag 0 ∧ c 2 = tag 1) ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        ⌊b 3 / χ⌋ = tag 0 → ⌊b 0 / χ⌋ = tag 1 →
        (∀ r ∈ Icc (0 : ℝ) 1, |b 1 + r * b 4 - u - r * v| ≤ H * β) →
        code q χ g m b t ∈ S := by
  classical
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hβ : 0 < β := hm.trans_le hmβ
  obtain ⟨J, hJ, hJcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hq
    (by norm_num : (0 : ℝ) ≤ 1) 0
  obtain ⟨V, hV, hVcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hg
    (by positivity : 0 ≤ 2 * H * β) v
  choose P hP hPcover using fun j : ℤ =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hm (by positivity : 0 ≤ H * β)
      (u + ((j : ℝ) * q) * v)
  let encode (j : ℤ) (w : ℤ × ℤ) : Code := ![j, tag 0, tag 1, w.1, w.2]
  let S : Finset Code := J.biUnion fun j => (V ×ˢ P j).image (encode j)
  have hJ' : (J.card : ℝ) ≤ 6 / q := by
    apply hJ.trans
    apply (le_div_iff₀ hq).mpr
    field_simp
    linarith
  have hV' : (V.card : ℝ) ≤ 10 * H ^ 2 := by
    apply hV.trans
    rw [show 4 * (2 * H * β) / g + 2 = (8 * H * β + 2 * g) / g by field_simp; ring]
    apply (div_le_iff₀ hg).mpr
    have hHg := mul_le_mul_of_nonneg_left hβg (by positivity : 0 ≤ 8 * H)
    have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
    nlinarith [mul_le_mul_of_nonneg_right hH2 hg.le]
  have hP' : ∀ j, ((P j).card : ℝ) ≤ 6 * H * β / m := by
    intro j
    apply (hP j).trans
    apply (le_div_iff₀ hm).mpr
    have hHm : m ≤ H * β := hmβ.trans (by nlinarith)
    field_simp
    nlinarith
  have hcount : (S.card : ℝ) ≤ (6 / q) * (10 * H ^ 2) * (6 * H * β / m) := by
    calc
      _ ≤ ∑ j ∈ J, (((V ×ˢ P j).image (encode j)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ J, (V.card : ℝ) * (P j).card := by
        apply Finset.sum_le_sum
        intro j _
        exact_mod_cast (Finset.card_image_le.trans_eq (Finset.card_product _ _))
      _ ≤ ∑ _j ∈ J, (10 * H ^ 2) * (6 * H * β / m) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul hV' (hP' j) (by positivity) (by positivity)
      _ = (J.card : ℝ) * ((10 * H ^ 2) * (6 * H * β / m)) := by simp
      _ ≤ (6 / q) * ((10 * H ^ 2) * (6 * H * β / m)) :=
        mul_le_mul_of_nonneg_right hJ' (by positivity)
      _ = _ := by ring
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      (S.card : ℝ) * q * m ≤ ((6 / q) * (10 * H ^ 2) * (6 * H * β / m)) * q * m := by gcongr
      _ = 360 * H ^ 3 * β := by field_simp; ring
  · intro c hc
    obtain ⟨j, hj, hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    simp [encode]
  · intro b t ht htag₀ htag₁ hfit
    let j : ℤ := ⌊t / q⌋
    have hj : j ∈ J := hJcover t (by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2)
    have hv : ⌊b 4 / g⌋ ∈ V := hVcover _ (by simpa only [mul_assoc] using projected_velocity_error b hfit)
    have hleft : (j : ℝ) * q ∈ Icc (0 : ℝ) 1 :=
      timeCenter_mem_unit (χ := χ) (g := g) (m := m) hq b ht
    have hp : ⌊(b 1 + (j : ℝ) * q * b 4) / m⌋ ∈ P j := by
      apply hPcover j
      have h := hfit ((j : ℝ) * q) hleft
      convert h using 1
      congr 1
      ring
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_image.mpr ?_⟩
    refine ⟨(⌊b 4 / g⌋, ⌊(b 1 + (j : ℝ) * q * b 4) / m⌋),
      Finset.mem_product.mpr ⟨hv, hp⟩, ?_⟩
    ext i
    fin_cases i <;> simp [code, encode, j, htag₀, htag₁]

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
