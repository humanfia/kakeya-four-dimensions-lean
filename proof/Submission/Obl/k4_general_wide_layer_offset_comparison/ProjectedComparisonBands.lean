import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonFrame
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.DyadicMatching

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonBands.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

/-- The raw comparison frame supplies every dyadic query-band bound used
by discrepancy matching, in the same fine original prior for both colors. -/
theorem band_ceiling (hp : p.Valid) {A : ProjectedLayer α} {s : ℝ}
    (q : A.SourceAtlas p k s m H h g b σ)
    (hcoeff : ∀ i e, |(A.G i).coeff e| ≤ f.B)
    {M₀ : ℝ} (hM₀ : 0 < M₀) (hmin : H * p.N k ^ (-sf) ≤ M₀)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 f.δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (i : q.Index) (n : ℕ) :
    f.coarseAtlas.matchingLaw f.δ Q {z | f.coarseAtlas.key (f.coarseAtlas.selector z.1) = q.key i ∧
      ‖q.sheet i (emb z.2) - (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * (M₀ * 2 ^ n)} ≤
      ENNReal.ofReal (p.projectedComparisonDensity k H * p.comparisonPrior k sf m h b (q.key i) *
        (M₀ / p.N k ^ (-sf)) ^ p.d * ((2 : ℝ) ^ p.d) ^ n) := by
  letI := f.finite_source hp
  have hN : 1 < p.N k := by linarith [hp.scale k]
  have haf : 0 < p.N k ^ (-sf) := Real.rpow_pos_of_pos (zero_lt_one.trans hN) _
  have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hW : 0 < M₀ * 2 ^ n := by positivity
  have hMW : M₀ ≤ M₀ * 2 ^ n := le_mul_of_one_le_right hM₀.le hn
  have hA : p.N k ^ (-sf) ≤ H * p.N k ^ (-sf) := by nlinarith [f.loss_one]
  have hresolved : p.N k ^ (-sf) ≤ 3 * (M₀ * 2 ^ n) := by
    have hl := hA.trans (hmin.trans hMW)
    linarith
  have hjitter : 54 * f.B * (p.K k + 1) ^ 4 * f.η ≤ M₀ * 2 ^ n :=
    f.jitter_resolution.trans (hmin.trans hMW)
  have hδscale (a : ℝ) (ha : 0 ≤ a) : (32 * a) * f.δ ≤ a := by
    calc
      _ ≤ (32 * a) * (1 / 32) := mul_le_mul_of_nonneg_left f.mesh_small (by positivity)
      _ = a := by ring
  have hdb : p.N k ^ (-f.r) ≤ 2 * b :=
    f.cap_transverse_width.trans ((hδscale b f.width_pos.le).trans (by linarith [f.width_pos]))
  have hmb : f.V * p.N k ^ (-f.r) ≤ 2 * b :=
    f.cap_transverse_motion.trans ((hδscale b f.width_pos.le).trans (by linarith [f.width_pos]))
  have hc := f.coarseAtlas.query_band_ceiling q (sf := sf) hp.basic f.le_mu hN (hp.subpower.1 k)
    hp.dimension_nonneg hp.dimension_lt_one.le f.loss_one f.fine_nonneg f.cap_mesh_nonneg f.coeff_nonneg
    f.time_pos f.slope_pos f.width_pos f.domain_motion f.mesh_pos f.physical_nonneg f.physical_small
    f.velocity_nonneg f.domain_velocity f.major_velocity f.jitter_time (f.query_transverse hp q)
    hcoeff f.cap_resolution (f.cap_time.trans (hδscale h f.time_pos.le))
    f.cap_major_width hdb f.cap_major_motion hmb hW hresolved hjitter Q hcover f.native_caps i
  have hdy : (M₀ * 2 ^ n / p.N k ^ (-sf)) ^ p.d =
      (M₀ / p.N k ^ (-sf)) ^ p.d * ((2 : ℝ) ^ p.d) ^ n := by
    have hd := dyadic_ratio_rpow hM₀ (show 0 < p.N k ^ (-sf) / 2 by positivity) n p.d
    simpa only [show 2 * (p.N k ^ (-sf) / 2) = p.N k ^ (-sf) by ring] using hd
  simpa only [hdy, mul_assoc] using hc

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
