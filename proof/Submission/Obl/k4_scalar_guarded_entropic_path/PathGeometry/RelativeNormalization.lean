/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/RelativeNormalization.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RemainingMaximizers

/-!
Buffered relative profiles remain buffered after an actual positive-length
normalization. This applies both to coarsened and remaining critical
problems, and uses each term's length rather than its limiting length.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology

/-- Relative profile errors that are little-o of a density buffer retain
that property under actual affine depth normalization. -/
theorem normalized_relative_buffer_limit
    (f g : ℕ → ℝ → ℝ) (shift length buffer : ℕ → ℝ) (dstar a : ℝ)
    (ha : 0 < a) (hbuffer : ∀ i, 0 < buffer i)
    (hlength : Tendsto length atTop (𝓝 a))
    (hwindow : ∀ᶠ i in atTop, 0 ≤ shift i ∧ shift i + length i ≤ 1)
    (hidentity : ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      g i s - g i 0 = (f i (shift i + length i * s) - f i (shift i)) / length i)
    (hscaled : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      |f i s - f i 0 - dstar * s| ≤ ε * buffer i) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      |g i s - g i 0 - dstar * s| ≤ ε * buffer i := by
  intro ε hε
  have hsmall : 0 < ε * a / 4 := by positivity
  have hlengthlo : ∀ᶠ i in atTop, a / 2 ≤ length i :=
    (hlength.eventually (Ioi_mem_nhds (show a / 2 < a by linarith))).mono
      (fun _ hi => hi.le)
  filter_upwards [hwindow, hidentity, hscaled (ε * a / 4) hsmall, hlengthlo]
    with i hwin heq hi hlen
  have hlen₀ : 0 < length i := lt_of_lt_of_le (half_pos ha) hlen
  intro s hs
  have hshift : shift i ∈ Icc (0 : ℝ) 1 :=
    ⟨hwin.1, by linarith [hwin.2]⟩
  have hpoint : shift i + length i * s ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg hwin.1 (mul_nonneg hlen₀.le hs.1)
    · have := mul_le_mul_of_nonneg_left hs.2 hlen₀.le
      linarith [hwin.2]
  have herr : |f i (shift i + length i * s) - f i (shift i) -
      dstar * length i * s| ≤ 2 * (ε * a / 4) * buffer i := by
    calc
      _ = |(f i (shift i + length i * s) - f i 0 -
          dstar * (shift i + length i * s)) -
          (f i (shift i) - f i 0 - dstar * shift i)| := by
        congr 1
        ring
      _ ≤ |f i (shift i + length i * s) - f i 0 -
          dstar * (shift i + length i * s)| +
          |f i (shift i) - f i 0 - dstar * shift i| := abs_sub _ _
      _ ≤ _ := by linarith [hi _ hpoint, hi _ hshift]
  rw [heq s hs]
  have halgebra : (f i (shift i + length i * s) - f i (shift i)) / length i - dstar * s =
      (f i (shift i + length i * s) - f i (shift i) - dstar * length i * s) / length i := by
    field_simp
  rw [halgebra, abs_div, abs_of_pos hlen₀]
  apply (div_le_iff₀ hlen₀).2
  have hmul := mul_le_mul_of_nonneg_left hlen
    (mul_nonneg hε.le (hbuffer i).le)
  nlinarith

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
