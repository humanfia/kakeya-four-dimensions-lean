import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Decode
import Submission.Obl.k4_remainder_pure_profile_normalization.NativeDensities

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
open MeasureTheory Filter Set

/-- The native polynomial clauses imply the geometric clauses needed by encoding. -/
theorem tempered_of_sample {N K : ℝ} {M D W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Trajectory} {E : Fin W → Set Incidence}
    {P : Fin W → Test} {B : Fin W → ℝ}
    (hs : Normalization.SampleProblem N K M D W ω ν E P B) :
    Tempered N K M D W ω ν E B := by
  refine ⟨hs.card, hs.weight_nonneg, hs.weight_sum, hs.prob, hs.scale_pos,
    hs.scale_le, hs.scale_inv_le, hs.prior, hs.event_meas, hs.event_time,
    hs.event_bdd, hs.event_fmt, ?_, hs.mass⟩
  intro b
  filter_upwards [hs.native b] with l hl t ht
  exact (hl t ht).1

namespace Sample
namespace Hyp
variable {S : Sample} (h : S.Hyp)
include h

/-- Decoding only restricts incidences. It preserves the original native tests
and their almost everywhere bounds, after enlarging the common slack. -/
theorem decoded_sample {D : ℕ} {P : Fin S.W → Test}
    (hs : Normalization.SampleProblem S.N S.K S.M D S.W S.ω S.ν S.E P S.B)
    {E'' : Set Incidence} {K'' : ℝ} {M' D' : ℕ} (hE'' : MeasurableSet E'')
    (hsub : E'' ⊆ S.event)
    (hfmt : ∀ n : ℕ, fmt 7 (S.N ^ M') D'
      {x : Fin 7 → ℝ | ((n, fun j : Fin 6 => x j.castSucc), x 6) ∈ E''})
    (hmass : ENNReal.ofReal K''⁻¹ ≤ ((S.prior.prod volume).restrict E'') univ)
    (hK'' : 0 < K'') :
    Normalization.SampleProblem S.N (max S.K K'') (max S.M M') (max D D')
      S.W S.ω S.ν (S.decEvent E'') P S.B := by
  have T := h.decoded_tempered (tempered_of_sample hs) hE'' hsub hfmt hmass hK''
  have hM : S.N ^ S.M ≤ S.N ^ (max S.M M') :=
    pow_le_pow_right₀ h.one_le_N (le_max_left _ _)
  refine ⟨T.card, T.weight_nonneg, T.weight_sum, T.prob, T.scale_pos,
    T.scale_le, T.scale_inv_le, hs.deg, fun b e => (hs.coeff b e).trans hM,
    T.prior, T.event_meas, T.event_time, T.event_bdd, T.event_fmt, ?_, ?_, T.mass⟩
  · intro b
    filter_upwards [hs.native b] with l hl t ht
    obtain ⟨h1,h2,h3,h4⟩ := hl t ht
    exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _),
      h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (h.B_pos b).le),
      h4.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
  · intro b
    have hle : ((S.ν b).prod volume).restrict (S.decEvent E'' b) ≤
        ((S.ν b).prod volume).restrict (S.E b) :=
      Measure.restrict_mono (h.decEvent_subset hsub b) le_rfl
    filter_upwards [ae_mono hle (hs.lower b)] with z hz
    exact (div_le_div_of_nonneg_left (h.B_pos b).le h.K_pos (le_max_left _ _)).trans hz

end Hyp
end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
