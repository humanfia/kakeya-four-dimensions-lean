import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Models
import Submission.Obl.k4_dyadic_crop_worlds.Assembly
import Submission.Lib.K4XInterface.Charts

/-! Preserve the raw predicate after selecting incidences in fixed format. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_dyadic_crop_worlds (EventFormat)

noncomputable def selectIncidences (p : Data) (K' : ℕ → ℝ)
    (E' : (k : ℕ) → Fin (p.W k) → Set Incidence) : Data :=
  { p with K := K', E := E' }

/-- A fixed-format incidence selection keeps the full prior in each world. -/
theorem RawValid.select_incidences {p : Data} (hp : RawValid p)
    (K' : ℕ → ℝ) (E' : (k : ℕ) → Fin (p.W k) → Set Incidence)
    (hK' : (∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K' k ≤ p.N k ^ ε)
    (hKK' : ∀ k, p.K k ≤ K' k) (hsub : ∀ k b, E' k b ⊆ p.E k b)
    (hEfmt : ∃ M D : ℕ, ∀ k b, EventFormat (p.N k ^ M) D (E' k b))
    (hmass : ∀ k, ENNReal.ofReal ((K' k)⁻¹) ≤
      ∑ b, ENNReal.ofReal (p.ω k b) * ((p.ν k b).prod volume) (E' k b)) :
    RawValid (selectIncidences p K' E') := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩
  obtain ⟨M', D', hEf⟩ := hEfmt
  refine ⟨hN, hNt, hK', hL, hd, hd1, hS, hη, max M M', max D D', fun k => ?_⟩
  have hN1 : 1 ≤ p.N k := by linarith [hN k]
  have hpM : p.N k ^ M ≤ p.N k ^ max M M' := pow_le_pow_right₀ hN1 (le_max_left _ _)
  have hpM' : p.N k ^ M' ≤ p.N k ^ max M M' := pow_le_pow_right₀ hN1 (le_max_right _ _)
  have hK0 : 0 < p.K k := by linarith [hK.1 k]
  refine ⟨(hfmt k).1.trans hpM, (hfmt k).2.1, (hfmt k).2.2.1, ?_, ?_⟩
  · intro b
    rcases (hfmt k).2.2.2.1 b with
      ⟨hν, hB, hBle, hBi, hP, hc, hprior, -, -, -, -, hnat, hlow⟩
    obtain ⟨hEm, hEt, hEb, hEformat⟩ := hEf k b
    refine ⟨hν, hB, hBle.trans hpM, hBi.trans hpM, hP,
      (fun e => (hc e).trans hpM), ?_, hEm, hEt, ?_, ?_, ?_, ?_⟩
    · obtain ⟨m, hm, c, i, A, hA, heq⟩ := hprior
      refine ⟨m, hm.trans hpM, c, i, A, ?_, heq⟩
      intro j
      obtain ⟨hc0, hc1, hi, hAf, hAb⟩ := hA j
      exact ⟨hc0, hc1.trans hpM, hi.trans hpM,
        Submission.Lib.K4XInterface.gfmt_mono hpM (le_max_left _ _) hAf,
        fun z hz e => (hAb z hz e).trans hpM⟩
    · intro z hz
      exact ⟨(hEb z hz).1.trans hpM', fun e => ((hEb z hz).2 e).trans hpM'⟩
    · intro i
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono
        (hEformat i) hpM' (le_max_right _ _)
    · filter_upwards [hnat] with l hl t ht
      obtain ⟨hy, hpv, hpd, hpdd⟩ := hl t ht
      exact ⟨hy.trans (hKK' k), hpv.trans (hKK' k),
        hpd.trans (mul_le_mul_of_nonneg_right (hKK' k) hB.le),
        hpdd.trans (mul_le_mul_of_nonneg_right (hKK' k) (sq_nonneg _))⟩
    · have hle : ((p.ν k b).prod volume).restrict (E' k b) ≤ selected p k b :=
        Measure.restrict_mono_set _ (hsub k b)
      have hlow' := (Measure.absolutelyContinuous_of_le hle).ae_le hlow
      filter_upwards [hlow'] with z hz
      exact (div_le_div_of_nonneg_left hB.le hK0 (hKK' k)).trans hz
  · change ENNReal.ofReal ((K' k)⁻¹) ≤
      ∑ b, ENNReal.ofReal (p.ω k b) *
        (((p.ν k b).prod volume).restrict (E' k b)) univ
    simpa only [Measure.restrict_apply_univ] using hmass k

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
