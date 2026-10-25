-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/FixedNativeCaps.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales
import Submission.Lib.K4AffineMeshCaps

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory MvPolynomial Filter
open Submission.Lib.K4AffineMeshCaps (baseMesh)

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- The frozen native scalar ceiling at any fixed positive base depth and
nonnegative hidden depth, expressed in the exact cell-volume form. -/
theorem eventually_native_scalar_caps_at (hp : p.Valid) {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) :
    ∀ᶠ k in atTop, ∀ (q : Fin 3 → ℤ) (j : ℤ), p.μ k {u |
      baseMesh (p.N k ^ (-r)) (p.base k u) = q ∧
      ⌊eval (p.x k u.1 u.2) (p.P k) / p.a k s⌋ = j} ≤
      ENNReal.ofReal (p.K k * (p.N k ^ (-r)) ^ (3 : ℕ) * p.a k s ^ p.d) := by
  let R : ℝ := 2 + r + s + r⁻¹
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hrR : r ≤ R := by dsimp [R]; linarith
  have hsR : s ≤ R := by dsimp [R]; linarith
  have hr' : R⁻¹ ≤ r := (inv_le_comm₀ (by linarith : 0 < R) hr).mpr
    (by dsimp [R]; linarith)
  have hRinv : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (by linarith)
  filter_upwards [hp.caps R hR] with k hk
  intro q j
  have hN := Valid.N_pos p hp k
  have hpow : (p.N k ^ (-r)) ^ (3 : ℕ) = p.N k ^ (-3 * r) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  have heq : p.K k * (p.N k ^ (-r)) ^ (3 : ℕ) * p.a k s ^ p.d =
      p.K k * p.N k ^ (-3 * r - p.d * s) := by
    rw [hpow, a_rpow_eq p hp, mul_assoc, ← Real.rpow_add hN]
    congr 2
    ring
  rw [heq]
  change p.μ k {u | p.z k r u = q ∧
    ⌊eval (p.x k u.1 u.2) (p.P k) / (p.N k ^ (-s))⌋ = j} ≤ _
  simpa only [Bool.true_eq, ↓reduceIte] using
    (hk r s 1 hr' hrR hs hsR hRinv (by linarith)).2.1 true q j

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
