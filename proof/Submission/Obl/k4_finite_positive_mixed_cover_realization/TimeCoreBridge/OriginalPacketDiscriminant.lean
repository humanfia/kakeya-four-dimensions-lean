-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/OriginalPacketDiscriminant.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupSheetChoice
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.LargeBasePolynomialBounds
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CleanCaps
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.NormalizedBounds
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.DiscriminantRemez

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- Original incidence-law control bounds the discriminant of the packet-normalized
test with a universal coefficient constant and a fixed sixth power loss. -/
def PacketDiscriminantBound (Cdisc : ℝ) : Prop :=
  ∀ (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ),
    Q.det ≠ 0 → 0 < B →
  ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ 2 →
  ∀ (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H q S δfit U : ℝ),
    0 < H → 0 < q → q ≤ 1 → 1 ≤ S → 0 < δfit → 0 ≤ U →
    μ.map (fun p => normBase T j c u Q p.1 p.2) ≤ ENNReal.ofReal H • volume →
    ENNReal.ofReal (H * q) ≤ μ univ →
    (∀ᵐ p ∂μ, ‖normBase T j c u Q p.1 p.2‖ ≤ S / 8 ∧
      |eval (gx p.1 p.2) P| ≤ U * δfit ∧
      |eval (gx p.1 p.2) (pderiv 3 P)| ≤ U * B ∧
      |eval (gx p.1 p.2) (pderiv 3 (pderiv 3 P))| ≤ U * B ^ 2 / δfit) →
    ∀ d, |(packetDiscriminant T j c u Q B P).coeff d| ≤
      Cdisc * (96 / (q / S ^ 3)) ^ 6 * (3 * U ^ 2)

/-- The constant is fixed independently of the sample, old frame, witness mass,
and fine fit depth. The original observation-law floor is never renormalized. -/
theorem exists_packet_discriminant_bound :
    ∃ Cdisc : ℝ, 0 < Cdisc ∧ PacketDiscriminantBound Cdisc := by
  obtain ⟨Cdisc, hCdisc, hbound⟩ := exists_original_law_large_ball_coefficient_bound 2
  refine ⟨Cdisc, hCdisc, ?_⟩
  intro T j c u Q B hQ hB P hP μ H q S δfit U hH hq hq1 hS hδ hU hcap hmass htrace
  let Pb := normPoly T j c u Q B P
  let D := packetDiscriminant T j c u Q B P
  have hPb : Pb.totalDegree ≤ 2 := (normPoly_totalDegree_le T j c u Q B P).trans hP
  have hqb := totalDegree_qbPoly_le hPb
  have hD : D.totalDegree ≤ 2 := by
    change (qbPoly Pb * qbPoly Pb - MvPolynomial.C (2 * qc Pb) * qcPoly Pb).totalDegree ≤ 2
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by omega)
    · apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C, zero_add] using totalDegree_qcPoly_le hPb
  let base := fun p : (ℕ × (Fin 6 → ℝ)) × ℝ => normBase T j c u Q p.1 p.2
  have hbase : Measurable base := by
    have heq : base = (normBaseObs T j c u Q) ∘ obs 1 1 := by
      funext p
      exact (normBaseObs_obs T j c u Q 1 1 p).symm
    rw [heq]
    exact (continuous_normBaseObs T j c u Q).measurable.comp (measurable_obs 1 1)
  have hpoint : ∀ᵐ p ∂μ, ‖base p‖ ≤ S / 8 ∧ |eval (fun i => base p i) D| ≤ 3 * U ^ 2 := by
    filter_upwards [htrace] with p hp
    obtain ⟨hnorm, h0, h1, h2⟩ := hp
    obtain ⟨hv, hd, hqc⟩ := normalized_bounds (T := T) (j := j) (c := c) (u := u)
      hQ hB hP hδ h0 h1 h2
    have hsnoc : (Fin.snoc (fun z => base p z) (B * gx p.1 p.2 3) : Fin 4 → ℝ) =
        normPt T j c u Q B p.1 p.2 := by
      rw [show (fun z => base p z) = Fin.init (normPt T j c u Q B p.1 p.2) from
        normBase_eq_init T j c u Q B p.1 p.2]
      exact snoc_init_eq _
    change |eval (normPt T j c u Q B p.1 p.2) Pb| ≤ _ at hv
    change |eval (normPt T j c u Q B p.1 p.2) (pderiv 3 Pb)| ≤ _ at hd
    rw [← hsnoc, eval_snoc_quadratic' hPb] at hv
    rw [← hsnoc, eval_snoc_pderiv' hPb] at hd
    have hcurv : |2 * (qc Pb / 2)| ≤ U / δfit := by
      simpa only [show 2 * (qc Pb / 2) = qc Pb by ring] using hqc
    have hh := quadratic_discriminant_point_bound hδ hU hv hd hcurv
    refine ⟨hnorm, ?_⟩
    simpa only [D, packetDiscriminant, Pb, map_sub, map_mul, eval_C,
      show 4 * (qc Pb / 2) = 2 * qc Pb by ring, pow_two] using hh
  have hh := hbound D hD ((ℕ × (Fin 6 → ℝ)) × ℝ) μ base H q (3 * U ^ 2) S
    hbase hH hq hq1 (by positivity) hS hcap hmass hpoint
  norm_num at hh
  exact hh

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
