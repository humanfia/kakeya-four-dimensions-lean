import Submission.Obl.k4_scalar_marked_terminal_support.Noise
import Submission.Obl.k4_scalar_marked_terminal_support.Geometry

namespace Submission.Obl.k4_scalar_marked_terminal_support

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_packet_recovery (MarkedLaw timeCell timeCell_subset_unit)

lemma support_transfer {K σ a δ : ℝ} (hK : 1 ≤ K) (hδσ : δ ≤ σ)
    (hσ : 0 < σ) (hσa : σ ≤ a) {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)) (hb : ∀ l i, |b l i| ≤ K)
    {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) (hJ : 1 ≤ J) (hJσ : 1 ≤ (J : ℝ) * σ)
    (hw : ∀ j, 0 ≤ w j) (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ δ)
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    (F : Finset ((Fin 2 → ℤ) × ℤ))
    (hF : ∀ᵐ p ∂μ,
      ((![(⌊p.2 / σ⌋ : ℤ), ⌊evalY (b p.1) p.2 / σ⌋] : Fin 2 → ℤ),
        (⌊evalX (b p.1) p.2 / a⌋ : ℤ)) ∈ F) :
    ∀ᵐ p ∂MarkedLaw σ H J b₀ w mark,
      ((![p.2, evalY p.1.2 p.2] : Fin 2 → ℝ), (⌊evalX p.1.2 p.2 / a⌋ : ℤ)) ∈
        observationCover K σ F := by
  apply noisyMarkedLaw_ae hσ b₀ w mark hw
  intro j hj c hc z hm t ht
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hKpos : 0 < K := by linarith
  have hfloor : 0 < ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) :=
    ENNReal.ofReal_pos.mpr (div_pos hj (by positivity))
  have hpos : μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z} ≠ 0 :=
    ne_of_gt (hfloor.trans_le (hmark j z hm))
  obtain ⟨p, ⟨htag, hpt⟩, hpf⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hF)
  have hnear : ∀ i, |c i - b p.1 i| ≤ 2 * σ :=
    rounded_noisy_near hδσ (fun i => by simpa [htag] using hround p.1 i) hc
  have htime : |t - p.2| ≤ σ := same_timeCell_dist hJ hJσ ht hpt
  have htunit := timeCell_subset_unit (show 0 < J by omega) z ht
  have hpunit := timeCell_subset_unit (show 0 < J by omega) z hpt
  obtain ⟨htnear, hynear, hxnear⟩ := observations_near_original hK hσ hσa
    (hb p.1) hnear htunit hpunit htime
  exact mem_observationCover hpf htnear hynear hxnear

end Submission.Obl.k4_scalar_marked_terminal_support
