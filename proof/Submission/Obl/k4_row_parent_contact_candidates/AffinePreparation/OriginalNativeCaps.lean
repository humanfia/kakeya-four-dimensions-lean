/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/OriginalNativeCaps.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedBaseCaps

/-! Read fixed source meshes and native widths directly from the frozen caps. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- The native source ceiling has its original width factor and its exact
original velocity weight, before restricting or conditioning any parent law. -/
theorem eventually_original_native_bin_caps {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcaps : a.Caps p)
    {D s v : ℝ} (hD : 0 < D) (hs : 0 ≤ s) (hv : 0 < v) :
    ∀ᶠ k in atTop,
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        a.mu k {z | baseMesh (p.N k ^ (-D)) (basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k s⌋ = j} ≤
          ENNReal.ofReal (p.K k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k s ^ p.d * (p.N k ^ (-D)) ^ 3)) ∧
      (∀ (q : Fin 3 → ℤ) (j l : ℤ),
        a.mu k {z | baseMesh (p.N k ^ (-D)) (basePoint (a.b k z.1) z.2) = q ∧
          ⌊eval (a.x k z.1 z.2) (a.P k) / Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k s⌋ = j ∧
          ⌊a.b k z.1 3 / p.N k ^ (-v)⌋ = l} ≤
          ENNReal.ofReal (p.K k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k s ^ p.d * (p.N k ^ (-D)) ^ 3) *
            a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = l}) ∧
      ∀ l : ℤ, a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = l} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-p.S * v)) := by
  let R : ℝ := 2 + D + D⁻¹ + s + v + v⁻¹
  have hDi : 0 < D⁻¹ := inv_pos.mpr hD
  have hvi : 0 < v⁻¹ := inv_pos.mpr hv
  have hR : 1 < R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hsR : s ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hRD : R⁻¹ ≤ D := by
    have h : D⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hDi h
  have hRv : R⁻¹ ≤ v := by
    have h : v⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hvi h
  filter_upwards [hcaps R hR] with k hk
  have hN : 0 < p.N k := by linarith [hp.1 k]
  have hpow : p.K k * p.N k ^ (-3 * D - p.d * s) =
      p.K k * Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width p k s ^ p.d * (p.N k ^ (-D)) ^ 3 := by
    rw [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width, ← Real.rpow_mul hN.le, ← Real.rpow_mul_natCast hN.le,
      mul_assoc, ← Real.rpow_add hN]
    congr 2
    ring
  have hraw := hk D s v hRD hDR hs hsR hRv hvR
  refine ⟨?_, ?_, hraw.1⟩
  · intro q j
    have h := hraw.2.1 true q j
    change a.mu k {z | a.cell (p.N k) D k z = q ∧
      ⌊eval (a.x k z.1 z.2) (a.P k) / p.N k ^ (-s)⌋ = j} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * D - p.d * s)) at h
    simpa only [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.cell_eq_baseMesh, hpow, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width] using h
  · intro q j l
    have h := hraw.2.2 true q j l
    change a.mu k {z | a.cell (p.N k) D k z = q ∧
      ⌊eval (a.x k z.1 z.2) (a.P k) / p.N k ^ (-s)⌋ = j ∧
      ⌊a.b k z.1 3 / p.N k ^ (-v)⌋ = l} ≤
        ENNReal.ofReal (p.K k * p.N k ^ (-3 * D - p.d * s)) *
          a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = l} at h
    simpa only [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.cell_eq_baseMesh, hpow, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width] using h

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
