/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/TrueDomainGeometry.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomains
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! Transverse position menus for a true tilted packet on the common time cells. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Set

noncomputable section

def rowError (c : Fin 5 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)

def trueMinorCenter (c : Fin 5 → ℝ) (χ : ℝ) (v z : ℤ) (t : ℝ) : ℝ :=
  c 2 + t * c 3 + c 4 * ((z : ℝ) * χ + t * ((v : ℝ) * χ))

/-- The row derivative estimate extrapolates the true packet's transverse fit to the
left endpoint of a shorter common time cell. The endpoint need not be in the true block. -/
theorem true_position_at_left {K Q q χ g m t₀ : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (hqQ : q ≤ Q) (hχ : 0 < χ) (hχQg : χ ≤ Q * g)
    (c : Fin 5 → ℝ) (hc₄ : |c 4| ≤ K) (b : Fin 6 → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htt₀ : |t - t₀| ≤ Q)
    (hposition : |rowError c b t₀| ≤ K * Q * g)
    (hslope : |b 4 - c 3 - c 4 * b 3| ≤ K * g) :
    |b 1 + timeCenter q (code q χ g m b t) * b 4 -
      trueMinorCenter c χ ⌊b 3 / χ⌋ ⌊b 0 / χ⌋ (timeCenter q (code q χ g m b t))| ≤
      5 * K * Q * g := by
  let r := timeCenter q (code q χ g m b t)
  have hr : r ∈ Icc (0 : ℝ) 1 := timeCenter_mem_unit hq b ht
  have htr : |t - r| ≤ q := time_error hq b t
  have hrt₀ : |r - t₀| ≤ 2 * Q := by
    have h := abs_sub_le r t t₀
    rw [abs_sub_comm r t] at h
    linarith
  have hid : rowError c b r = rowError c b t₀ + (r - t₀) * (b 4 - c 3 - c 4 * b 3) := by
    unfold rowError
    ring
  have hrow : |rowError c b r| ≤ 3 * K * Q * g := by
    rw [hid]
    calc
      _ ≤ |rowError c b t₀| + |(r - t₀) * (b 4 - c 3 - c 4 * b 3)| := abs_add_le _ _
      _ ≤ K * Q * g + (2 * Q) * (K * g) := by
        rw [abs_mul]
        exact add_le_add hposition (mul_le_mul hrt₀ hslope (abs_nonneg _) (by linarith))
      _ = _ := by ring
  have hmajor : |b 0 + r * b 3 - ((⌊b 0 / χ⌋ : ℝ) * χ + r * ((⌊b 3 / χ⌋ : ℝ) * χ))| ≤ 2 * χ := by
    simpa [point, majorCenter, code] using major_error (q := q) (g := g) (m := m) hχ b hr
  have hsplit : b 1 + r * b 4 - trueMinorCenter c χ ⌊b 3 / χ⌋ ⌊b 0 / χ⌋ r =
      rowError c b r + c 4 * (b 0 + r * b 3 -
        ((⌊b 0 / χ⌋ : ℝ) * χ + r * ((⌊b 3 / χ⌋ : ℝ) * χ))) := by
    unfold rowError trueMinorCenter
    ring
  change |b 1 + r * b 4 - trueMinorCenter c χ ⌊b 3 / χ⌋ ⌊b 0 / χ⌋ r| ≤ _
  rw [hsplit]
  calc
    _ ≤ |rowError c b r| + |c 4 * (b 0 + r * b 3 -
        ((⌊b 0 / χ⌋ : ℝ) * χ + r * ((⌊b 3 / χ⌋ : ℝ) * χ)))| := abs_add_le _ _
    _ ≤ 3 * K * Q * g + K * (2 * χ) := by rw [abs_mul]; gcongr
    _ ≤ 5 * K * Q * g := by nlinarith [mul_le_mul_of_nonneg_left hχQg hK]

/-- Only `O(K Q g / m)` common transverse position bins meet one true packet for
each fixed common time and major coefficient code. -/
theorem true_position_menus {K Q q χ g m t₀ : ℝ} (hK : 1 ≤ K) (hq : 0 < q)
    (hqQ : q ≤ Q) (hχ : 0 < χ) (hχQg : χ ≤ Q * g) (hm : 0 < m) (hmQg : m ≤ Q * g)
    (c : Fin 5 → ℝ) (hc₄ : |c 4| ≤ K) :
    ∃ P : ℤ → ℤ → ℤ → Finset ℤ,
      (∀ j v z, ((P j v z).card : ℝ) * m ≤ 22 * K * Q * g) ∧
      ∀ (b : Fin 6 → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → |t - t₀| ≤ Q →
        |rowError c b t₀| ≤ K * Q * g → |b 4 - c 3 - c 4 * b 3| ≤ K * g →
        (code q χ g m b t) 4 ∈ P ⌊t / q⌋ ⌊b 3 / χ⌋ ⌊b 0 / χ⌋ := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hQg : 0 < Q * g := hm.trans_le hmQg
  have hQ : 0 < Q := hq.trans_le hqQ
  have hg : 0 < g := by
    rcases mul_pos_iff.mp hQg with h | h
    · exact h.2
    · linarith [h.1]
  choose P hP hPcover using fun j v z : ℤ =>
    Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hm (by positivity : 0 ≤ 5 * K * Q * g)
      (trueMinorCenter c χ v z ((j : ℝ) * q))
  refine ⟨P, ?_, ?_⟩
  · intro j v z
    have h := mul_le_mul_of_nonneg_right (hP j v z) hm.le
    have heq : (4 * (5 * K * Q * g) / m + 2) * m = 20 * K * Q * g + 2 * m := by field_simp; ring
    rw [heq] at h
    have hmK : m ≤ K * (Q * g) := hmQg.trans (by nlinarith)
    nlinarith
  · intro b t ht htt₀ hposition hslope
    have h := true_position_at_left (m := m) hK0 hq hqQ hχ hχQg c hc₄ b ht htt₀ hposition hslope
    apply hPcover
    simpa [code, timeCenter, mul_assoc] using h

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
