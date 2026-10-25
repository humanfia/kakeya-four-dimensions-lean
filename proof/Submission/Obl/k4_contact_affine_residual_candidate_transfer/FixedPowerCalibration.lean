/- Fixed-power-mass variant of the native calibration step of this LOT tree,
   obligation o200, session x0829, commit a965423f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ModelNativeCalibration.lean. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.NativeGridTransfer
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.NativeCalibrationNumerics
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.SourceBounds
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Obl.k4_quadratic_mesh_coefficient_calibration
open Submission.Obl.k4_critical_switching_state_preparation

/-- Uniform first calibration on every fixed-power-mass original sublaw.
This includes a single selected coarse parent, whose unnormalized mass
need not be inverse subpower. The affine predictor and the sublaw are both
chosen after the common eventual sample set. -/
theorem fixed_power_native_affine_calibration {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ k in atTop, ∀ (τ : Measure (α × ℝ)), τ ≤ D.μ k →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ τ univ → ∀ L : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (D.x k x.1 x.2) (affineBase L) -
        (D.x k x.1 x.2) 3| ≤ 1) →
      (∀ e, |(calibrationPolynomial (D.K k) (affineSheetRestriction L (D.P k))).coeff e| ≤
        D.N k ^ (6 * B + 1)) ∧
      (∀ e, |(affineSheetRestriction L (D.P k)).coeff e| ≤ 27 * D.N k ^ (6 * B + 1)) := by
  obtain ⟨C, Lip, hC, hLip, hcal⟩ := exists_native_affine_grid_calibration
  have hN₁ : ∀ k, 1 ≤ D.N k := fun k => by linarith [p.scale k]
  let R : ℝ := 6 * B + 3
  have hR : 1 < R := by dsimp [R]; linarith
  have hRinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR.le
  have hbudget := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ p.scale_limit p.subpower.1 p.subpower.2 31
    (a := 0) (b := 1) (by norm_num) (A := 162 * C * 344064 ^ 6) (by positivity)
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN₁ p.scale_limit p.subpower.1 p.subpower.2 30
    (a := -1) (b := 0) (by norm_num) (A := 108 * Lip * C * 344064 ^ 6) (by positivity)
  filter_upwards [h2 R hR, hbudget, hsmall] with k hcapk hbudgetk hsmallk
  intro τ hτ hmass L hfit
  have hN : 0 < D.N k := by linarith [p.scale k]
  have hK : 1 ≤ D.K k := p.subpower.1 k
  have hK₀ : 0 < D.K k := by linarith
  let m : ℝ := D.N k ^ (-B)
  let r : ℝ := 6 * B + 1
  let δ : ℝ := D.N k ^ (-r)
  have hm : 0 < m := Real.rpow_pos_of_pos hN _
  have hm₁ : m ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (by linarith)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrR : r ≤ R := by dsimp [r, R]; linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have hδK : δ ≤ D.K k :=
    (Real.rpow_le_one_of_one_le_of_nonpos (hN₁ k) (by linarith)).trans hK
  have hmb : m ≤ ((2 * D.K k + 5) * D.K k) * (8 * D.K k) ^ 3 := by
    apply hm₁.trans
    have hb : 1 ≤ (2 * D.K k + 5) * D.K k := by nlinarith [hK]
    have hp : 1 ≤ (8 * D.K k) ^ 3 := one_le_pow₀ (by linarith)
    simpa only [one_mul] using mul_le_mul hb hp (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ (2 * D.K k + 5) * D.K k)
  have hsmall' : (54 * Lip * C * 344064 ^ 6) * D.K k ^ 30 * D.N k ^ (-1 : ℝ) ≤ 1 / 2 := by
    have hh : 2 * ((54 * Lip * C * 344064 ^ 6) * D.K k ^ 30 * D.N k ^ (-1 : ℝ)) < 1 := by
      have hh := hsmallk
      rw [Real.rpow_zero] at hh
      convert hh using 1 <;> ring
    nlinarith only [hh]
  have habsorb : 54 * Lip * C *
      (96 / (m / (((2 * D.K k + 5) * D.K k) * (8 * D.K k) ^ 3))) ^ 6 *
        (δ / (8 * D.K k)) ≤ 1 / 2 := by
    apply (native_mesh_absorption_budget hK hm hC.le hLip.le hδ.le).trans
    change (54 * Lip * C * 344064 ^ 6) * D.K k ^ 30 * D.N k ^ (-r) /
      (D.N k ^ (-B)) ^ (6 : ℕ) ≤ _
    rw [fixed_mass_calibration_identity hN]
    simpa only [r, show 6 * B - (6 * B + 1) = -1 by ring] using hsmall'
  have hcell : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      τ {x | cell δ (D.x k x.1 x.2 ∘ Fin.castSucc) = q ∧
        ⌊eval (D.x k x.1 x.2) (D.P k)⌋ = j} ≤ ENNReal.ofReal (D.K k * δ ^ 3) := by
    intro q j
    have hh := (hcapk r 0 1 (hRinv.trans hr) hrR (by norm_num)
      (by linarith) hRinv hR.le).2.1 true q j
    have he : (D.N k ^ (-r)) ^ (3 : ℕ) = D.N k ^ (-3 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
      congr 1
      ring
    apply (hτ _).trans
    simpa [data_z_eq_cell, δ, he] using hh
  have hgood : ∀ᵐ x ∂τ, (∀ j : Fin 3, |D.x k x.1 x.2 j.castSucc| ≤ D.K k) ∧
      |eval (D.x k x.1 x.2) (D.P k)| ≤ D.K k ∧
      |eval (D.x k x.1 x.2) (pderiv 3 (D.P k))| ≤ D.K k ∧
      |eval (D.x k x.1 x.2) (pderiv 3 (pderiv 3 (D.P k)))| ≤ D.K k ∧
      |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ 1 := by
    filter_upwards [ae_mono hτ (basic_base_bound D p.subpower.1 h1 k),
      ae_mono hτ (basic_native_value_bounds D h1 k), hfit] with x hb hn hf
    exact ⟨hb, hn.1, hn.2.1, hn.2.2, hf⟩
  obtain ⟨hcn, hcr⟩ := hcal (α × ℝ) τ (fun x => D.x k x.1 x.2) (D.P k)
    (h1 k).2.2.2.2.2.2.2.1 L (D.K k) δ m (D.K k) (D.K k)
    hK hδ hδK hm hK₀ hK₀.le hmb hmass hcell hgood habsorb
  have hcoeff : 54 * C *
      (96 / (m / (((2 * D.K k + 5) * D.K k) * (8 * D.K k) ^ 3))) ^ 6 *
        (3 * D.K k) ≤ D.N k ^ (6 * B + 1) := by
    apply (native_mesh_coefficient_budget hK hm hC.le).trans
    have he : (162 * C * 344064 ^ 6) * D.K k ^ 31 / m ^ 6 =
        ((162 * C * 344064 ^ 6) * D.K k ^ 31) * D.N k ^ (6 * B) := by
      simpa only [m, neg_zero, Real.rpow_zero, mul_one, sub_zero] using
        fixed_mass_calibration_identity hN B 0 ((162 * C * 344064 ^ 6) * D.K k ^ 31)
    rw [he]
    calc
      _ ≤ D.N k * D.N k ^ (6 * B) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
        simpa only [Real.rpow_zero, mul_one, Real.rpow_one] using hbudgetk.le
      _ = _ := by
        calc
          _ = D.N k ^ (1 : ℝ) * D.N k ^ (6 * B) := by rw [Real.rpow_one]
          _ = D.N k ^ (1 + 6 * B) := (Real.rpow_add hN _ _).symm
          _ = _ := by congr 1; ring
  exact ⟨fun e => (hcn e).trans hcoeff,
    fun e => (hcr e).trans (mul_le_mul_of_nonneg_left hcoeff (by norm_num))⟩

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
