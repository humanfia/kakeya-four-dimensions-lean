-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.CoveringStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric

theorem Covering.mono_scale {d e α C : ℝ} {B : Set ℝ} (h : Covering d α C B)
    (hde : d ≤ e) : Covering e α C B :=
  fun r R a her hrR => h r R a (hde.trans her) hrR

theorem Covering.mono_constant {d α C D : ℝ} {B : Set ℝ} (h : Covering d α C B)
    (hd : 0 < d) (hCD : C ≤ D) : Covering d α D B := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  refine ⟨m, c, hc, hm.trans ?_⟩
  have hr : 0 < r := hd.trans_le hdr
  exact mul_le_mul_of_nonneg_right hCD
    (Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) _)

theorem Covering.mono_exponent {d α β C : ℝ} {B : Set ℝ} (h : Covering d α C B)
    (hd : 0 < d) (hC : 0 ≤ C) (hαβ : α ≤ β) : Covering d β C B := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  refine ⟨m, c, hc, hm.trans ?_⟩
  have hr : 0 < r := hd.trans_le hdr
  have hratio : 1 ≤ R / r := (le_div_iff₀ hr).mpr (by simpa using hrR)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hratio hαβ) hC

/-- Moving every point by at most the resolution preserves the one-dimensional covering
condition at twice the resolution, with an explicit constant loss. -/
theorem Covering.of_close {d α C : ℝ} {A B : Set ℝ} (h : Covering d α C B)
    (hd : 0 < d) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hAB : ∀ x ∈ A, ∃ y ∈ B, dist x y ≤ d) :
    Covering (2 * d) α (4 ^ α * C) A := by
  intro r R a hdr hrR
  have hr : 0 < r := (by positivity : 0 < 2 * d).trans_le hdr
  have hR : 0 < R := hr.trans_le hrR
  obtain ⟨m, c, hc, hm⟩ := h (r / 2) (R + 2 * d) (a - d)
    (by linarith) (by linarith)
  refine ⟨m, c, ?_, hm.trans ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hAB x hx.1
    have habs : |x - y| ≤ d := by simpa only [Real.dist_eq] using hxy
    have hyI : y ∈ Icc (a - d) (a - d + (R + 2 * d)) := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp habs
      constructor <;> linarith [hx.2.1, hx.2.2]
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc ⟨hy, hyI⟩)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall] at hj ⊢
    exact (dist_triangle x y (c j)).trans (by linarith)
  · have hratio : (R + 2 * d) / (r / 2) ≤ 4 * (R / r) := by
      apply (div_le_iff₀ (by positivity : 0 < r / 2)).mpr
      have heq : 4 * (R / r) * (r / 2) = 2 * R := by field_simp; ring
      rw [heq]
      linarith
    calc
      C * ((R + 2 * d) / (r / 2)) ^ α ≤ C * (4 * (R / r)) ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hratio hα) hC
      _ = (4 ^ α * C) * (R / r) ^ α := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ R / r)]
        ring

theorem Covering.image_of_close {ι : Type*} {d α C : ℝ} {E : Set ι}
    {f g : ι → ℝ} (h : Covering d α C (g '' E))
    (hd : 0 < d) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hfg : ∀ p ∈ E, dist (f p) (g p) ≤ d) :
    Covering (2 * d) α (4 ^ α * C) (f '' E) := by
  apply h.of_close hd hα hC
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨g p, mem_image_of_mem g hp, hfg p hp⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
