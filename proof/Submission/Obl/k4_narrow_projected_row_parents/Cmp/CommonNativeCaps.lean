/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonNativeCaps.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomainCaps
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CoarserNativeCaps

/-! Primitive original native and velocity caps in the literal comparison frame. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open MeasureTheory Set
open Submission.Lib.K4MovingMeshBoxes
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
open scoped ENNReal

noncomputable section

/-- The frozen palette-joint native caps, rewritten as products of widths, give
all real coarser-width native caps in the common frame. The source law and the
original velocity palette are retained exactly. -/
theorem common_frame_native_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (signal velocity : Ω → ℝ)
    (π : Measure ℝ) [IsFiniteMeasure π]
    {N S d H C q χ g m δ σ : ℝ}
    (hN : 1 < N) (hS : 0 ≤ S) (hd : 0 ≤ d) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (hδ : 0 < δ) (hσ : 0 < σ)
    (c : Code) (hresolve : ∀ i, (∑ j, |coordMatrix q χ g m c i j| * δ) ≤ σ)
    (hbound : ∀ᵐ p ∂μ, |signal p| ≤ H)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ (z : Fin 3 → ℤ) (j v : ℤ),
      μ {p | baseMesh δ (Z p) = z ∧ ⌊signal p / N ^ (-s)⌋ = j ∧ ⌊velocity p / χ⌋ = v} ≤
        ENNReal.ofReal (C * δ ^ 3 * (N ^ (-s)) ^ d) * π {w : ℝ | ⌊w / χ⌋ = v})
    {R : ℝ} (hR : N ^ (-S) ≤ R) (z : Fin 3 → ℤ) (j : ℤ) :
    μ {p | baseMesh σ (coords q χ g m c (Z p)) = z ∧
      ⌊signal p / R⌋ = j ∧ ⌊velocity p / χ⌋ = c 1} ≤
      ENNReal.ofReal (27000000 * C * (2 * H + 5) * q * χ * m * R ^ d * σ ^ 3) *
        π {w : ℝ | ⌊w / χ⌋ = c 1} := by
  have hR0 : 0 ≤ R := (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _).le.trans hR
  let raw : Ω → (Fin 3 → ℤ) × ℤ := fun p => (baseMesh δ (Z p), ⌊velocity p / χ⌋)
  let A : ((Fin 3 → ℤ) × ℤ) → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (C * δ ^ 3) * π {w : ℝ | ⌊w / χ⌋ = u.2}
  have hraw (s : ℝ) (hs : 0 ≤ s) (hsS : s ≤ S) (u : (Fin 3 → ℤ) × ℤ) (j' : ℤ) :
      μ {p | raw p = u ∧ ⌊signal p / N ^ (-s)⌋ = j'} ≤
        ENNReal.ofReal ((N ^ (-s)) ^ d) * A u := by
    have h := hcap s hs hsS u.1 j' u.2
    have heq : {p | raw p = u ∧ ⌊signal p / N ^ (-s)⌋ = j'} =
        {p | baseMesh δ (Z p) = u.1 ∧ ⌊signal p / N ^ (-s)⌋ = j' ∧ ⌊velocity p / χ⌋ = u.2} := by
      ext p
      simp [raw, Prod.ext_iff, and_assoc, and_comm, and_left_comm]
    rw [heq]
    refine h.trans_eq ?_
    dsimp [A]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hN).le _) _)]
    congr 2
    ring
  have hcoarse (z' : Fin 3 → ℤ) := coarser_native_bin_cap μ raw signal hN hS hd hH A hbound hraw hR (z', c 1) j
  have hraw' (z' : Fin 3 → ℤ) :
      μ {p | baseMesh δ (Z p) = z' ∧ (⌊signal p / R⌋ = j ∧ ⌊velocity p / χ⌋ = c 1)} ≤
        ENNReal.ofReal ((C * (2 * H + 5) * R ^ d) * δ ^ 3) * π {w : ℝ | ⌊w / χ⌋ = c 1} := by
    have h := hcoarse z'
    have heq : {p | raw p = (z', c 1) ∧ ⌊signal p / R⌋ = j} =
        {p | baseMesh δ (Z p) = z' ∧ (⌊signal p / R⌋ = j ∧ ⌊velocity p / χ⌋ = c 1)} := by
      ext p
      simp [raw, and_assoc, and_comm, and_left_comm]
    rw [heq] at h
    refine h.trans_eq ?_
    dsimp [A]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  have h := common_frame_cell_cap μ Z (fun p => ⌊signal p / R⌋ = j ∧ ⌊velocity p / χ⌋ = c 1)
    hq hχ hm c hδ hσ (by positivity : 0 ≤ C * (2 * H + 5) * R ^ d)
    (π {w : ℝ | ⌊w / χ⌋ = c 1}) (measure_ne_top _ _) hresolve hraw' z
  convert h using 1
  congr 2
  ring

/-- Exact factorization of the frozen exponent numerator. -/
theorem native_cap_widths {N r s d : ℝ} (hN : 0 < N) :
    N ^ (-3 * r - d * s) = (N ^ (-r)) ^ 3 * (N ^ (-s)) ^ d := by
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 1
  ring

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
