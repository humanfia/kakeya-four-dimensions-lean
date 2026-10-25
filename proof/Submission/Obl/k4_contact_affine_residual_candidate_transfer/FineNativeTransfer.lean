/- Fixed-power-mass version of this LOT tree's o200, session x0829,
   commit a965423f, ModelResidualCaps.lean, model_fine_affine_residual_caps.
   The source measure and affine predictor are quantified after the common
   eventual sample set. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FixedPowerCalibration

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Obl.k4_critical_switching_state_preparation

/-- A fixed-power-small source needs a finer preliminary grid, but the
native interval transfer still costs only the original subpower factor.
Every original ENNReal numerator, including a velocity palette bin, survives. -/
theorem fine_original_native_transfer {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ k in atTop, ∀ (τ : Measure (α × ℝ)), τ ≤ D.μ k →
      ENNReal.ofReal (D.N k ^ (-B)) ≤ τ univ → ∀ L : Fin 4 → ℝ,
      (∀ᵐ x ∂τ, |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ 1) →
      ∀ r s : ℝ, 0 ≤ s → s + (6 * B + 2) ≤ r →
      ∀ (G : Set (α × ℝ)) (q : Fin 3 → ℤ) (C : ENNReal),
      (∀ j : ℤ, D.μ k {x | x ∈ G ∧ D.z k (D.N k) r x = q ∧
        ⌊eval (D.x k x.1 x.2) (D.P k) / D.N k ^ (-s)⌋ = j} ≤ C) →
      τ {x | x ∈ G ∧ D.z k (D.N k) r x = q ∧
        |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ D.N k ^ (-s)} ≤
        ENNReal.ofReal (6 * D.K k + 5) * C := by
  obtain ⟨Lip, hLip, htransfer⟩ := exists_native_residual_original_grid_cap
  have hconst := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    p.scale_limit (a := 0) (b := 1) (by norm_num) (2 * Lip)
  filter_upwards [fixed_power_native_affine_calibration D p h1 h2 hB, hconst]
    with k hcal hconstk
  intro τ hτ hmass L hfit r s hs hrs G q C hcap
  have hK : 1 ≤ D.K k := p.subpower.1 k
  have hK₀ : 0 < D.K k := by linarith
  have hN : 0 < D.N k := lt_of_lt_of_le (by norm_num) (p.scale k)
  have hN₁ : 1 ≤ D.N k := le_trans (by norm_num) (p.scale k)
  have ha : 0 < D.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hδ : 0 < D.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have ha₁ : D.N k ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith)
  have hLipN : 2 * Lip ≤ D.N k := by
    simpa only [Real.rpow_zero, mul_one, Real.rpow_one] using hconstk.le
  have hsmall := fine_native_absorption hN₁ hK hLip.le hLipN hrs
  let baseEvent : Set (α × ℝ) := {x | x ∈ G ∧ D.z k (D.N k) r x = q}
  let fineEvent : Set (α × ℝ) := {x | x ∈ G ∧ D.z k (D.N k) r x = q ∧
    |eval (D.x k x.1 x.2) (affineBase L) - (D.x k x.1 x.2) 3| ≤ D.N k ^ (-s)}
  apply htransfer (α × ℝ) τ baseEvent fineEvent (fun x => D.x k x.1 x.2) (D.P k)
    (h1 k).2.2.2.2.2.2.2.1 L (D.K k) (D.N k ^ (-r)) (D.K k) (D.N k ^ (-s))
    (D.N k ^ (6 * B + 1)) q hK₀ hδ hK₀.le ha ha₁ (Real.rpow_nonneg hN.le _)
    (hcal τ hτ hmass L hfit).1 ?_ hsmall C ?_
  · filter_upwards [ae_mono hτ (basic_native_value_bounds D h1 k),
      ae_mono hτ (basic_base_bound D p.subpower.1 h1 k)] with x hn hb hxf
    refine ⟨⟨hxf.1, hxf.2.1⟩, hn.2.1, hn.2.2, hxf.2.2, hb, ?_⟩
    rw [← data_z_eq_cell]
    exact hxf.2.1
  · intro j
    have hh := (hτ _).trans (hcap j)
    simpa only [baseEvent, mem_setOf_eq, and_assoc] using hh

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
