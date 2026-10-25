import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.SampleBridge
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
open MeasureTheory Filter Set

/-- Each sample of the original family, with uniform encoding exponents. -/
def encodedSample (p : Data) (M M₀ : ℕ) (k : ℕ) : Sample :=
  ⟨p.N k, p.K k, M, M₀, p.W k, p.ω k, p.ν k, p.E k, p.B k⟩

theorem encodedSample_hyp {p : Data} {M D M₀ : ℕ} (k : ℕ)
    (hs : Normalization.SampleProblem (p.N k) (p.K k) M D (p.W k)
      (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k))
    (hN : 2 ≤ p.N k) (hK : 1 ≤ p.K k) (hKpow : p.K k ≤ p.N k ^ M₀) :
    (encodedSample p M M₀ k).Hyp := by
  classical
  have hW : 1 ≤ p.W k := by
    by_contra hW
    have : IsEmpty (Fin (p.W k)) := ⟨fun b => by have := b.isLt; omega⟩
    have H := hs.weight_sum
    simp at H
  refine ⟨hN,hK,hKpow,hW,hs.card,hs.weight_nonneg,?_,hs.scale_pos,
    hs.scale_le,hs.scale_inv_le⟩
  intro b
  calc p.ω k b ≤ ∑ b, p.ω k b :=
      Finset.single_le_sum (fun b _ => hs.weight_nonneg b) (Finset.mem_univ b)
    _ = 1 := hs.weight_sum

theorem encodedFamily_format {p : Data} {M D M₀ : ℕ}
    (hs : ∀ k, Normalization.SampleProblem (p.N k) (p.K k) M D (p.W k)
      (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k))
    (hS : ∀ k, (encodedSample p M M₀ k).Hyp) :
    Submission.Obl.k4_joint_homogenization.Format p.N (fun k => 2 * p.K k + 6)
      (fun k => (encodedSample p M M₀ k).prior)
      (fun k => (encodedSample p M M₀ k).event) := by
  refine ⟨11 * M + 12 * M₀ + 18, D, fun k => ?_⟩
  have T := tempered_of_sample (hs k)
  exact ⟨(hS k).prior_isProb T, (hS k).prior_pieces T,
    Sample.measurableSet_event T.event_meas, Sample.Hyp.event_time T,
    (hS k).event_bdd T, (hS k).event_fmt T,
    (hS k).prior_ae_bound T, (hS k).coverage T⟩

theorem encoding_subpower {N K : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (ht : Tendsto N atTop atTop)
    (hK : Submission.Obl.k4_joint_homogenization.Subpower N K) :
    Submission.Obl.k4_joint_homogenization.Subpower N (fun k => 2 * K k + 6) := by
  have H := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    hN ht hK (A := 8) (by norm_num) 1
  refine ⟨fun k => by linarith [hK.1 k], fun ε hε => ?_⟩
  filter_upwards [H.2 ε hε] with k hk
  simp only [pow_one] at hk
  linarith [hK.1 k]

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
