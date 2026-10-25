import Submission.Obl.k4_raw_localized_native_systems.SourceFrames
import Submission.Obl.k4_raw_localized_native_systems.Window.LongWitnesses
import Submission.Obl.k4_raw_localized_native_systems.Deletion.ShortMajor
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Window

noncomputable section

/-- The complete short-major loss on an actual earlier source layer is
power-small along the very same homogeneous source subsequence. -/
theorem source_short_major_powerSmall {p : Data} (hp : Valid p)
    {kr w ε q band : ℝ} {m M D : ℕ} {sd r : ℕ → ℝ}
    (src : HomogeneousSourceSequence p kr w ε q band m M D sd r)
    {i : ℕ} (hi : i < m) (hrL : r i ≤ p.L) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ p.η * p.L) :
    IsPowerSmall (fun n => p.N (src.index n)) (fun n =>
      ∑ γ, ENNReal.ofReal (p.ω (src.index n) γ) * selected p (src.index n) γ
        (shortWitnessEvent (sourceFrame (src.forest n) (src.core n) i)
          ((1 / (2 : ℝ) ^ (src.forest n).T i) * p.N (src.index n) ^ (-u)) γ)) := by
  obtain ⟨τ, c, hτ, -, hc, hbound⟩ := Deletion.uniform_short_major_labels hp hu huη
  refine ⟨c, hc, ?_⟩
  filter_upwards [src.mono.tendsto_atTop.eventually hbound, src.subpower τ hτ] with n hn hκ
  let a := src.forest n
  let W := sourceFrame a (src.core n) i
  have hW : ∀ e, WChart p (src.index n) W M D a.κ (r i) e :=
    sourceFrame_wchart hp a (src.core n) (src.prepared n) hi hrL
  have hh := hn M D a.κ (r i) W (by linarith [(src.core n).1]) hκ hW
    (sourceFrame_measurable a (src.core n) i)
    (sourceFrame_card hp a (src.core n) (src.prepared n) hi hrL)
    (sourceFrame_known hp a (src.core n) (src.prepared n) hi hrL)
  have heq (γ : Fin (p.W (src.index n))) :
      {z | ∃ e, W.γ e = γ ∧ z ∈ W.F e ∧
        ‖Pairing.longCol (W.Q e)‖ < (1 / (2 : ℝ) ^ W.T) * p.N (src.index n) ^ (-u)} =
      shortWitnessEvent W ((1 / (2 : ℝ) ^ W.T) * p.N (src.index n) ^ (-u)) γ := by
    ext z
    constructor
    · rintro ⟨e, hγ, hz, hm⟩
      exact ⟨e, hγ, hm, hz⟩
    · rintro ⟨e, hγ, hm, hz⟩
      exact ⟨e, hγ, hz, hm⟩
  change (∑ γ, ENNReal.ofReal (p.ω (src.index n) γ) * selected p (src.index n) γ
    (shortWitnessEvent W ((1 / (2 : ℝ) ^ W.T) * p.N (src.index n) ^ (-u)) γ)) ≤
      ENNReal.ofReal (p.N (src.index n) ^ (-c))
  simpa only [heq] using hh

end
end Submission.Obl.k4_raw_localized_native_systems
