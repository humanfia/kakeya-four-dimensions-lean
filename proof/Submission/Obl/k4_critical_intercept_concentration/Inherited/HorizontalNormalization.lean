/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/HorizontalNormalization.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/HorizontalNormalization.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_intercept_concentration.Inherited.EndpointSimulation

/-! The contact affine coordinates used to normalize a horizontal parent. -/

namespace Submission.Obl.k4_critical_intercept_concentration.Inherited

noncomputable section

/-- Normalize time and the horizontal position by H and the transverse
position by H squared, after a contact translation and a velocity shift. -/
def horizontalFrame (H t₀ z₀ y₀ v₀ : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(p 0 - t₀) / H,
    (p 1 - z₀ - v₀ * (p 0 - t₀)) / H,
    (p 2 - y₀ + z₀ * (p 0 - t₀) - t₀ * (p 1 - z₀)) / H ^ 2]

def horizontalUnframe (H t₀ z₀ y₀ v₀ : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t₀ + H * p 0,
    z₀ + v₀ * H * p 0 + H * p 1,
    y₀ + (-z₀ + t₀ * v₀) * H * p 0 + t₀ * H * p 1 + H ^ 2 * p 2]

theorem horizontalFrame_unframe (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0) (p : Fin 3 → ℝ) :
    horizontalFrame H t₀ z₀ y₀ v₀ (horizontalUnframe H t₀ z₀ y₀ v₀ p) = p := by
  ext i
  fin_cases i <;> simp [horizontalFrame, horizontalUnframe] <;> field_simp <;> ring

theorem horizontalUnframe_frame (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0) (p : Fin 3 → ℝ) :
    horizontalUnframe H t₀ z₀ y₀ v₀ (horizontalFrame H t₀ z₀ y₀ v₀ p) = p := by
  ext i
  fin_cases i <;> simp [horizontalFrame, horizontalUnframe] <;> field_simp <;> ring

/-- The normalization preserves the horizontal traversal law exactly. -/
theorem horizontalFrame_traverse
    (H t₀ z₀ y₀ v₀ c s : ℝ) (hH : H ≠ 0) (p : Fin 3 → ℝ) :
    horizontalFrame H t₀ z₀ y₀ v₀
        ![s, horizontalTraverse c (p 0) s ![p 1, p 2] 0,
          horizontalTraverse c (p 0) s ![p 1, p 2] 1] =
      let q := horizontalFrame H t₀ z₀ y₀ v₀ p
      let τ := (s - t₀) / H
      ![τ, horizontalTraverse (c - v₀) (q 0) τ ![q 1, q 2] 0,
        horizontalTraverse (c - v₀) (q 0) τ ![q 1, q 2] 1] := by
  ext i
  fin_cases i <;> simp [horizontalFrame, horizontalTraverse] <;> field_simp <;> ring

/-- The base coordinates of the native trajectory in the frozen model. -/
def nativeHorizontalLine (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

/-- The horizontal equation has precisely the defect b4+b0. -/
theorem nativeHorizontalLine_defect (b : Fin 6 → ℝ) (t s : ℝ) :
    nativeHorizontalLine b s 2 -
      horizontalTraverse (b 3) t s ![nativeHorizontalLine b t 1, nativeHorizontalLine b t 2] 1 =
        (b 4 + b 0) * (s - t) := by
  simp [nativeHorizontalLine, horizontalTraverse]
  ring

def normalizedHorizontalLine (H t₀ z₀ y₀ v₀ : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  horizontalFrame H t₀ z₀ y₀ v₀ (nativeHorizontalLine b (t₀ + H * t))

theorem normalizedHorizontalLine_time
    (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 0 = t := by
  simp [normalizedHorizontalLine, horizontalFrame, nativeHorizontalLine, hH]

theorem normalizedHorizontalLine_defect
    (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0) (b : Fin 6 → ℝ) (t s : ℝ) :
    normalizedHorizontalLine H t₀ z₀ y₀ v₀ b s 2 -
      horizontalTraverse (b 3 - v₀) t s
        ![normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 1,
          normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 2] 1 =
        (b 4 + b 0) / H * (s - t) := by
  simp [normalizedHorizontalLine, horizontalFrame, nativeHorizontalLine, horizontalTraverse]
  field_simp
  ring

/-- On the rescaled unit interval, an original horizontal defect E becomes
E/H. This is the fixed-power error needed before the endpoint simulation. -/
theorem normalizedHorizontalLine_traverse_error
    (H t₀ z₀ y₀ v₀ E : ℝ) (hH : 0 < H) (hE : 0 ≤ E)
    (b : Fin 6 → ℝ) (hb : |b 4 + b 0| ≤ E)
    (t s : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i : Fin 2,
      |normalizedHorizontalLine H t₀ z₀ y₀ v₀ b s i.succ -
        horizontalTraverse (b 3 - v₀) t s
          ![normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 1,
            normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 2] i| ≤ E / H := by
  have hst : |s - t| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  intro i
  fin_cases i
  · have heq : normalizedHorizontalLine H t₀ z₀ y₀ v₀ b s 1 -
        horizontalTraverse (b 3 - v₀) t s
          ![normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 1,
            normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 2] 0 = 0 := by
      simp [normalizedHorizontalLine, horizontalFrame, nativeHorizontalLine, horizontalTraverse]
      field_simp
      ring
    have hres : |normalizedHorizontalLine H t₀ z₀ y₀ v₀ b s 1 -
        horizontalTraverse (b 3 - v₀) t s
          ![normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 1,
            normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 2] 0| ≤ E / H := by
      rw [heq, abs_zero]
      exact div_nonneg hE hH.le
    simpa using hres
  · have hres : |normalizedHorizontalLine H t₀ z₀ y₀ v₀ b s 2 -
        horizontalTraverse (b 3 - v₀) t s
          ![normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 1,
            normalizedHorizontalLine H t₀ z₀ y₀ v₀ b t 2] 1| ≤ E / H := by
      rw [normalizedHorizontalLine_defect H t₀ z₀ y₀ v₀ hH.ne' b t s, abs_mul, abs_div,
        abs_of_pos hH]
      exact (mul_le_mul (div_le_div_of_nonneg_right hb hH.le) hst (abs_nonneg _)
        (div_nonneg hE hH.le)).trans_eq (mul_one _)
    simpa using hres

end

end Submission.Obl.k4_critical_intercept_concentration.Inherited
