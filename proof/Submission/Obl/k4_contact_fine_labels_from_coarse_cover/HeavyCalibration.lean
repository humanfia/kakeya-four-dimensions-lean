-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HeavyCalibration.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.NativeCalibration
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ShallowLoss

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter MvPolynomial

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- Specialize the original coarse base ceilings at any fixed positive mesh
exponent, keeping the original measure throughout. -/
theorem eventually_base_caps_at (hp : p.Valid) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k in atTop, ∀ q : Fin 3 → ℤ,
      p.μ k {u | (fun i => ⌊p.base k u i / (p.N k ^ (-r))⌋) = q} ≤
        ENNReal.ofReal (((2 * p.K k + 5) * p.K k) *
          (p.N k ^ (-r)) ^ (3 : ℕ)) := by
  let R : ℝ := max 2 (max r r⁻¹)
  have hR2 : 2 ≤ R := le_max_left _ _
  have hR : 1 < R := by linarith
  have hrR : r ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hr' : R⁻¹ ≤ r := (inv_le_comm₀ (by linarith : 0 < R) hr).mpr
    ((le_max_right _ _).trans (le_max_right _ _))
  have hRinv : R⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (by linarith)
  filter_upwards [eventually_base_cell_caps p hp R hR] with k hk
  intro q
  have hpow : (p.N k ^ (-r)) ^ (3 : ℕ) = p.N k ^ (-3 * r) := by
    rw [← Real.rpow_mul_natCast (Valid.N_pos p hp k).le]
    congr 1
    ring
  rw [hpow]
  exact (hk r 1 hr' hrR hRinv (by linarith)).1 q

/-- Every quadratic observed on a heavy original sublaw can be calibrated
at once. The tested polynomial and the sublaw may depend on the true label. -/
theorem eventually_heavy_quadratic_calibration (hp : p.Valid) {C s : ℝ}
    (hC : 1 ≤ C) (hcal : MeshCalibration C) (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ τ : Measure (α × ℝ), τ ≤ p.μ k →
      ENNReal.ofReal (p.N k ^ (-6 * s)) ≤ τ univ →
      ∀ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 →
      (∀ᵐ u ∂τ, |eval (p.base k u) G| ≤ p.N k ^ (2 * s)) →
        ∀ e, |G.coeff e| ≤ p.N k ^ (39 * s) := by
  filter_upwards [eventually_base_caps_at p hp (show 0 < 100 * s by linarith),
    eventually_shallow_calibration_loss p hp hC hs,
    eventually_shallow_calibration_mesh p hp hC hs] with k hcaps hloss hmesh
  intro τ hτ hmass G hG hval e
  have := Valid.μ_finite p hp k
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  have hbound : ∀ᵐ u ∂p.μ k, ∀ i, |p.base k u i| ≤ 2 * p.K k := by
    filter_upwards [Valid.ae_good p hp k] with u hu
    exact GoodPoint.base_bounded p hp hu
  have h := calibrate_original_sublaw (p.μ k) (p.base k)
    (Valid.measurable_base p hp k) hcal (by linarith [hp.K_ge k])
    (by positivity : 0 < (2 * p.K k + 5) * p.K k)
    (Real.rpow_pos_of_pos hN (-6 * s)) (Real.rpow_nonneg hN.le (2 * s))
    (Real.rpow_pos_of_pos hN (-100 * s)) hmesh hbound
    (by simpa only [neg_mul] using hcaps) τ hτ hmass G hG hval e
  apply h.trans
  calc
    _ ≤ p.N k ^ (37 * s) * p.N k ^ (2 * s) :=
      mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg hN.le _)
    _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
