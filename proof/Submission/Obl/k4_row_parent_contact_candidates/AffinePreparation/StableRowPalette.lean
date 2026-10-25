/- Adapted from: here:o222, session x0774, commit 0d01aa57.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/StableRowPalette.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.StableRowSource
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ContactSampleSequence

/-! One coarse palette budget for all dense stable row parents. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Lib.K4ContactAffine (NativeSample)

noncomputable section

/-- The original-law stable row sources all have a three-sheet cover with
one subpower budget. The test is the parent `F_Q/a_r` solely for this coarse
geometric call; the original native polynomial is unchanged elsewhere. -/
theorem exists_stable_row_palette {α : Type} [MeasurableSpace α]
    (p : Submission.Obl.k4_general_parent_projected_layers.Parameters) (hp : p.Valid) (a : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α) (hcommon : a.Common p)
    (hcaps : a.Caps p) (hatlases : a.Atlases p) {r e₀ B : ℝ}
    (hr : 0 < r) (hrU : r ≤ p.U) (he₀ : 0 < e₀) (hB : 0 ≤ B)
    (M : ℕ → ℝ) (hM : ∀ k, 1 ≤ M k)
    (hMsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, M k ≤ p.N k ^ ε) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε) ∧
      ∀ᶠ k in atTop, ∀ S : StableRowSource p a k r e₀ (M k) B, S.sample.Cover (H k) := by
  let K₀ : ℕ → ℝ := fun k => parentContactBudget (p.K k) (M k)
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hNp : ∀ k, 0 < p.N k := fun k => by linarith [hp.1 k]
  have hK₀ := parentContactBudget_subpower hN1 hp.2.1 hp.2.2.1 ⟨hM, hMsub⟩
  let R : ℝ := 2 + r + r⁻¹
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have hR : 1 < R := by dsimp [R]; linarith
  have hRr : R⁻¹ ≤ r := by
    have h : r⁻¹ ≤ R := by dsimp [R]; linarith
    simpa only [inv_inv] using inv_anti₀ hri h
  obtain ⟨C, hC, hmatrix⟩ := eventually_coarse_row_matrix_bound p hp a hr M hM hMsub
  have hS : 0 < p.S := hp.2.2.2.2.2.2.2.2.1
  apply exists_subpower_sample_palettes p.N K₀ hp.1 hp.2.1 hK₀.1 hK₀.2
    (fun k => StableRowSource p a k r e₀ (M k) B) (fun _ S => S.sample)
    (fun k _ => by
      letI : IsProbabilityMeasure (a.pi k) := (hcommon k).2.2.1
      change IsFiniteMeasure (a.pi k)
      exact inferInstance) hS (half_pos he₀)
  · filter_upwards [hatlases R hR,
      Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
        hN1 hp.2.1 hM hMsub 2 (show -e₀ < -(e₀ / 2) by linarith)
        (show (0 : ℝ) ≤ 1 by norm_num)] with k hka hkcontact
    simp only [one_mul] at hkcontact
    intro S
    have hNk : 0 < p.N k := hNp k
    have hMk : 0 < M k := zero_lt_one.trans_le (hM k)
    have hatr : a.AtlasAt p R k r := hka r hRr hrU
    have hbudget := parentContactBudget_bounds (hp.2.2.1.1 k) (hM k)
    refine ⟨?_, ?_, ?_⟩
    · exact (S.rowParent.chart.degree_test (a.F k r S.rowParent.Q)).trans
        (hatr.2.2.2.2.1 S.rowParent.Q).2.2.2.2.1
    · have hgood := S.rowParent.ae_sample_good hp hcommon hatr S.lam_ne S.inv_le
        hbudget.2.1 hbudget.2.2.2.1 S.law
      have hgood' := (Measure.absolutelyContinuous_of_le (S.source_le_mu hcommon)).ae_le hgood
      have hsrc : ∀ᵐ z ∂S.source, S.sample.Good (K₀ k) (p.N k ^ (-(e₀ / 2))) z := by
        filter_upwards [hgood', ae_restrict_mem S.measurable_keep] with z hz hzkeep
        obtain ⟨ht, hc, hf, hd, he⟩ := hz hzkeep.1
        refine ⟨ht, hc, hf, hd, he.trans ?_⟩
        calc
          _ ≤ (M k * p.N k ^ (-e₀)) * M k :=
            mul_le_mul_of_nonneg_left S.inv_le (by positivity)
          _ = M k ^ 2 * p.N k ^ (-e₀) := by ring
          _ ≤ p.N k ^ (-(e₀ / 2)) := hkcontact.le
      exact Measure.ae_smul_measure hsrc (ENNReal.ofReal S.weight)⁻¹
    · exact (ENNReal.ofReal_le_ofReal
        (inv_anti₀ (by positivity : 0 < 2 * M k) hbudget.2.2.1)).trans
          (S.law_mass hp hcommon hatr (zero_lt_one.trans_le (hM k)))
  · intro t v ht hv
    filter_upwards [eventually_parent_uniform_caps p hp a hcommon hcaps hatlases
      hr hrU hB hC M t v ht hv, hmatrix, hatlases R hR] with k hkcap hkm hka
    intro S
    have hNk : 0 < p.N k := hNp k
    have hMk : 0 < M k := zero_lt_one.trans_le (hM k)
    have hatr : a.AtlasAt p R k r := hka r hRr hrU
    have hbudget := parentContactBudget_bounds (hp.2.2.1.1 k) (hM k)
    have hcap := hkcap S.rowParent.Q S.groups S.oscillation S.source
      (S.source_le_mu hcommon) S.ae_source_groups S.rowParent.chart.baseMatrix
      S.rowParent.chart.baseShift S.rowParent.lam
      (hkm R hatr _ S.rowParent S.inv_le)
      (S.rowParent.chart.det_baseMatrix_ne (S.rowParent.chart_ok hp) S.lam_ne)
      (S.rowParent.chart_jacobian hp) S.rowParent.lam_le
    have hceil : ENNReal.ofReal
        (recoveredParentBaseConstant (p.K k) (M k) * (p.N k ^ (-t)) ^ 3) ≤
        ENNReal.ofReal (K₀ k * (p.N k ^ (-t)) ^ 3) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget.2.2.2.2 (by positivity))
    refine ⟨?_, ?_, ?_⟩
    · intro q
      change S.law {u | baseMesh (p.N k ^ (-t))
        (Submission.Lib.K4QuadraticSheetCore.lineP (S.rowParent.chart.coeff (a.b k u.1))
          (S.rowParent.chart.Z.time u.2)) = q} ≤ _
      simp_rw [S.rowParent.chart.base_coeff (S.rowParent.chart_ok hp) S.lam_ne]
      exact (hcap.1 q).trans hceil
    · intro q j
      change S.law {u | baseMesh (p.N k ^ (-t))
        (Submission.Lib.K4QuadraticSheetCore.lineP (S.rowParent.chart.coeff (a.b k u.1))
          (S.rowParent.chart.Z.time u.2)) = q ∧
            ⌊S.rowParent.chart.coeff (a.b k u.1) 3 / p.N k ^ (-v)⌋ = j} ≤ _
      simp_rw [S.rowParent.chart.base_coeff (S.rowParent.chart_ok hp) S.lam_ne,
        S.rowParent.chart.coeff_three]
      exact (hcap.2.1 q j).trans (mul_le_mul' hceil le_rfl)
    · intro j
      exact (hcap.2.2 j).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hbudget.2.1 (by positivity)))

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
