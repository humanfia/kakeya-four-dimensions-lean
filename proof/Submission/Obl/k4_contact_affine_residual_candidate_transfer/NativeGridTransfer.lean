/- Adapted from this LOT tree, obligation o200, session x0829, commit a965423f,
   Submission/Obl/k4_finite_projected_horizontal_candidates/NativeGridCalibration.lean.
   The discrete calibration and cell geometry are imported from accepted o242;
   native interval transfer uses this obligation's original-law kernel. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.NativeMeshCaps
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.RawGridCalibration
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Obl.k4_quadratic_mesh_coefficient_calibration

noncomputable section

/-- Calibrate the native polynomial on ANY affine predictor within distance
one of the original incidences. The output controls both the polynomial on
the unit cube and its coefficients in original base coordinates. -/
theorem exists_native_affine_grid_calibration :
    ∃ C Lip : ℝ, 0 < C ∧ 0 < Lip ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω → Fin 4 → ℝ)
        (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ (L : Fin 4 → ℝ) (H h m beta K : ℝ),
        1 ≤ H → 0 < h → h ≤ H → 0 < m → 0 < beta → 0 ≤ K →
        m ≤ ((2 * K + 5) * beta) * (8 * H) ^ 3 →
        ENNReal.ofReal m ≤ μ univ →
        (∀ (q : Fin 3 → ℤ) (j : ℤ),
          μ {p | cell h (x p ∘ Fin.castSucc) = q ∧ ⌊eval (x p) P⌋ = j} ≤
            ENNReal.ofReal (beta * h ^ 3)) →
        (∀ᵐ p ∂μ, (∀ j : Fin 3, |x p j.castSucc| ≤ H) ∧
          |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv 3 P)| ≤ K ∧
          |eval (x p) (pderiv 3 (pderiv 3 P))| ≤ K ∧
          |eval (x p) (affineBase L) - x p 3| ≤ 1) →
        54 * Lip * C * (96 / (m / (((2 * K + 5) * beta) * (8 * H) ^ 3))) ^ 6 *
          (h / (8 * H)) ≤ 1 / 2 →
        (∀ e, |(calibrationPolynomial H (affineSheetRestriction L P)).coeff e| ≤
          54 * C * (96 / (m / (((2 * K + 5) * beta) * (8 * H) ^ 3))) ^ 6 * (3 * K)) ∧
        (∀ e, |(affineSheetRestriction L P).coeff e| ≤
          27 * (54 * C * (96 / (m / (((2 * K + 5) * beta) * (8 * H) ^ 3))) ^ 6 * (3 * K))) := by
  obtain ⟨C, Lip, hC, hLip, hcal⟩ := exists_coefficient_bound_from_original_grid 2
  refine ⟨C, Lip, hC, hLip, ?_⟩
  intro Ω _ μ x P hP L H h m beta K hH hh hhH hm hbeta hK hmb hmass hcap hgood hsmall
  have hHp : 0 < H := zero_lt_one.trans_le hH
  let G := affineSheetRestriction L P
  have hG : G.totalDegree ≤ 2 := (affineSheetRestriction_degree L P).trans hP
  have hQ : (calibrationPolynomial H G).totalDegree ≤ 2 :=
    (calibrationPolynomial_degree H G).trans hG
  have hvalues : ∀ᵐ p ∂μ, (∀ j : Fin 3, |x p j.castSucc| ≤ H) ∧
      |eval (calibrationBase H (x p ∘ Fin.castSucc)) (calibrationPolynomial H G)| ≤ 3 * K := by
    filter_upwards [hgood] with p hp
    refine ⟨hp.1, ?_⟩
    rw [eval_calibrationPolynomial hHp]
    simpa only [mul_one] using
      affineSheetRestriction_value_bound L P hP (x p) (a := 1) zero_lt_one hK
        (by simpa only [mul_one] using hp.2.1) hp.2.2.1
        (by simpa only [div_one] using hp.2.2.2.1) hp.2.2.2.2
  have hbase (q : Fin 3 → ℤ) : μ {p | cell h (x p ∘ Fin.castSucc) = q} ≤
      ENNReal.ofReal (((2 * K + 5) * beta) * h ^ 3) := by
    have hc := original_base_cap_from_native_unit_bins μ
      (fun p => cell h (x p ∘ Fin.castSucc)) (fun p => eval (x p) P)
      hK (ENNReal.ofReal (beta * h ^ 3)) hcap (hgood.mono fun _ hp => hp.2.1) q
    apply hc.trans_eq
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * K + 5)]
    congr 1
    ring
  have hcoef := hcal Ω μ (fun p => x p ∘ Fin.castSucc) (calibrationPolynomial H G) hQ
    H h m ((2 * K + 5) * beta) (3 * K) hHp hh hhH hm (by positivity) hmb
    (by positivity) hmass hbase hvalues (by norm_num at hsmall ⊢; nlinarith [hsmall])
  have hc : ∀ e, |(calibrationPolynomial H G).coeff e| ≤
      54 * C * (96 / (m / (((2 * K + 5) * beta) * (8 * H) ^ 3))) ^ 6 * (3 * K) := by
    intro e
    convert hcoef e using 1 <;> norm_num <;> ring
  refine ⟨hc, fun e => ?_⟩
  have hnorm := Submission.Lib.K4ChartLifting.coeffL1_le_of_coeff_le
    (calibrationPolynomial H G) hQ _ hc
  exact (Submission.Lib.K4ChartLifting.abs_coeff_le_coeffL1 G e).trans
    ((coeffL1_le_calibrationPolynomial hH G).trans
      (by simpa using hnorm))

/-- The calibrated native polynomial controls oscillation on an ORIGINAL
base cell. The cell center is an actual good incidence, selected only after
checking that the fine event has positive mass. Any palette factor in `C`
is preserved. -/
theorem exists_native_residual_original_grid_cap :
    ∃ Lip : ℝ, 0 < Lip ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
        (baseEvent fineEvent : Set Ω) (x : Ω → Fin 4 → ℝ)
        (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
      ∀ (L : Fin 4 → ℝ) (H h K a M : ℝ) (q : Fin 3 → ℤ),
        0 < H → 0 < h → 0 ≤ K → 0 < a → a ≤ 1 → 0 ≤ M →
        (∀ e, |(calibrationPolynomial H (affineSheetRestriction L P)).coeff e| ≤ M) →
        (∀ᵐ p ∂μ, p ∈ fineEvent → p ∈ baseEvent ∧
          |eval (x p) (pderiv 3 P)| ≤ K ∧
          |eval (x p) (pderiv 3 (pderiv 3 P))| ≤ K ∧
          |eval (x p) (affineBase L) - x p 3| ≤ a ∧
          (∀ j : Fin 3, |x p j.castSucc| ≤ H) ∧
          cell h (x p ∘ Fin.castSucc) = q) →
        2 * Lip * M * (h / (8 * H)) ≤ K * a →
        ∀ C : ENNReal,
          (∀ j : ℤ, μ {p | p ∈ baseEvent ∧ ⌊eval (x p) P / a⌋ = j} ≤ C) →
          μ fineEvent ≤ ENNReal.ofReal (6 * K + 5) * C := by
  obtain ⟨Lip, hLip, hlip⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_degree 2
  refine ⟨Lip, hLip, ?_⟩
  intro Ω _ μ baseEvent fineEvent x P hP L H h K a M q hH hh hK ha ha1 hM
    hcoeff hgood hsmall C hcap
  by_cases hz : μ fineEvent = 0
  · rw [hz]
    exact zero_le
  obtain ⟨p0, hp0, hp0good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hz
    (ae_restrict_of_ae hgood)
  obtain ⟨_, _, _, _, hp0bound, hp0cell⟩ := hp0good hp0
  let G := affineSheetRestriction L P
  let center := x p0 ∘ Fin.castSucc
  apply affine_residual_original_cell_cap μ (fun p => p ∈ baseEvent) x True
    P hP L center ha ha1 hK C (by intro j; simpa using hcap j) fineEvent
  filter_upwards [hgood] with p hp hpf
  obtain ⟨hpbase, hd, hdd, hclose, hpbound, hpcell⟩ := hp hpf
  refine ⟨propext ⟨fun _ => trivial, fun _ => hpbase⟩, hclose, hd, hdd, ?_⟩
  have hnorm := calibrationBase_norm hH hpbound
  have hnorm0 := calibrationBase_norm hH hp0bound
  have hpc : calibrationBase H (x p ∘ Fin.castSucc) ∈ calibrationCell H h q := by
    rw [← hpcell]
    exact calibrationBase_mem_cell hH hh _
  have hdist := euclidean_dist_le_twice_coordinate_bound
    (calibrationBase H (x p ∘ Fin.castSucc)) (calibrationBase H center)
    (by positivity : 0 ≤ h / (8 * H))
    (fun j => calibrationCell_near_witness hH hh hp0cell hpc j)
  have hh := hlip (calibrationPolynomial H G)
    ((calibrationPolynomial_degree H G).trans ((affineSheetRestriction_degree L P).trans hP))
    M hM hcoeff (WithLp.toLp 2 (calibrationBase H (x p ∘ Fin.castSucc)))
      (WithLp.toLp 2 (calibrationBase H center)) hnorm hnorm0
  change |eval (calibrationBase H (x p ∘ Fin.castSucc)) (calibrationPolynomial H G) -
    eval (calibrationBase H center) (calibrationPolynomial H G)| ≤ _ at hh
  rw [eval_calibrationPolynomial hH, eval_calibrationPolynomial hH] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hLip.le hM)).trans
    (by nlinarith [hsmall]))


end
end Submission.Obl.k4_contact_affine_residual_candidate_transfer
