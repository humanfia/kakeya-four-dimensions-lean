/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeWidthCaps.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface
import Submission.Obl.k4_horizontal_strict_parameter_step.JitterGeometry
import Submission.Obl.k4_tempered_grid_selection.Exponents

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Every allowed physical width has an allowed real depth. The logarithmic
exponent identity is imported from the accepted tempered grid selection. -/
theorem exists_bounded_width_exponent {N R w : ℝ} (hN : 1 < N)
    (hw : N ^ (-R) ≤ w) (hw1 : w ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ R ∧ N ^ (-s) = w := by
  have hNp : 0 < N := by linarith
  have hwp : 0 < w := (Real.rpow_pos_of_pos hNp _).trans_le hw
  let s := Submission.Obl.k4_tempered_grid_selection.logarithmicExponent N w
  have hs : N ^ (-s) = w :=
    Submission.Obl.k4_tempered_grid_selection.rpow_neg_logarithmicExponent hN hwp
  have hlo : -s ≤ 0 := (Real.rpow_le_rpow_left_iff hN).mp (by simpa only [hs, Real.rpow_zero] using hw1)
  have hhi : -R ≤ -s := (Real.rpow_le_rpow_left_iff hN).mp (by simpa only [hs] using hw)
  exact ⟨s, by linarith, by linarith, hs⟩

/-- Frozen joint caps, expressed at every physical scalar width in the tested
range. Neither dyadic band widths nor child scalar widths need to be powers
chosen in advance. -/
def OriginalWidthCapsAt {α : Type} [MeasurableSpace α]
    (N K d R : ℝ) (μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) : Prop :=
  ∀ re v w : ℝ, R⁻¹ ≤ re → re ≤ R → R⁻¹ ≤ v → v ≤ R →
    N ^ (-R) ≤ w → w ≤ 1 →
    (∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j} ≤
          ENNReal.ofReal (K * (N ^ (-re)) ^ 3 * w ^ d)) ∧
    (∀ (q : Fin 3 → ℤ) (j z : ℤ),
      μ {p | baseMesh (N ^ (-re)) (physicalBase (b p.1) p.2) = q ∧
        ⌊(b p.1 2 + p.2 * b p.1 5) / w⌋ = j ∧ ⌊b p.1 3 / (N ^ (-v))⌋ = z} ≤
          ENNReal.ofReal (K * (N ^ (-re)) ^ 3 * w ^ d) *
            π {u | ⌊u / (N ^ (-v))⌋ = z})

theorem eventually_original_width_caps {α : Type} [MeasurableSpace α]
    {N K : ℕ → ℝ} {d S R : ℝ} {μ : ℕ → Measure (α × ℝ)}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ}
    {P : ℕ → MvPolynomial (Fin 4) ℝ}
    (hN : ∀ k, 1 < N k) (hcaps : Hyp2 N K d S μ π b P) (hR : 1 < R) :
    ∀ᶠ k in atTop, OriginalWidthCapsAt (N k) (K k) d R (μ k) (π k) (b k) := by
  filter_upwards [hcaps R hR] with k hk
  intro re v w hre hre' hv hv' hw hw1
  obtain ⟨s, hs, hsR, hsw⟩ := exists_bounded_width_exponent (hN k) hw hw1
  have hNp : 0 < N k := by linarith [hN k]
  have hpow : N k ^ (-3 * re - d * s) = (N k ^ (-re)) ^ 3 * w ^ d := by
    rw [← hsw, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le,
      ← Real.rpow_mul hNp.le, ← Real.rpow_add hNp]
    congr 1
    push_cast
    ring
  have hz : zc b k (N k) re =
      fun p : α × ℝ => baseMesh (N k ^ (-re)) (physicalBase (b k p.1) p.2) := by
    funext p
    ext i
    fin_cases i <;> rfl
  have hh := hk re s v hre hre' hs hsR hv hv'
  constructor
  · intro q j
    have hb := hh.2.1 false q j
    rw [hpow, hsw] at hb
    simpa only [Bool.false_eq_true, ↓reduceIte, mul_assoc, hz, xs, Matrix.cons_val] using hb
  · intro q j z
    have hb := hh.2.2 false q j z
    rw [hpow, hsw] at hb
    simpa only [Bool.false_eq_true, ↓reduceIte, mul_assoc, hz, xs, Matrix.cons_val] using hb

end

end Submission.Obl.k4_horizontal_strict_parameter_step
