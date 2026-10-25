import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Params

/-!
# The encoded single world of one sample

Membership in the encoded event, measurability, and the identity expressing the encoded
product law as the weighted sum of the world laws pulled back by the encodings.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

namespace Sample

variable {S : Sample}

theorem measurable_enc (γ : Fin S.W) : Measurable (S.enc γ) :=
  measurable_encLine _ _ _ _ _ _

theorem measurable_encInc (γ : Fin S.W) : Measurable (S.encInc γ) :=
  ((measurable_enc γ).comp measurable_fst).prodMk measurable_snd

namespace Hyp

variable (h : S.Hyp)
include h

theorem a_ne : S.a ≠ 0 := h.a_pos.ne'

theorem b_ne (γ : Fin S.W) : S.b γ ≠ 0 := (h.b_pos γ).ne'

theorem θ_ne (γ : Fin S.W) : S.θ γ ≠ 0 := (h.θ_pos γ).ne'

theorem dec_enc (γ : Fin S.W) (x : Fin 6 → ℝ) :
    decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) (encCoeff S.a (S.b γ) (S.θ γ) (S.o γ) x) = x :=
  decCoeff_encCoeff h.a_ne (h.b_ne γ) (h.θ_ne γ) _ x

theorem enc_dec (γ : Fin S.W) (x : Fin 6 → ℝ) :
    encCoeff S.a (S.b γ) (S.θ γ) (S.o γ) (decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) x) = x :=
  encCoeff_decCoeff h.a_ne (h.b_ne γ) (h.θ_ne γ) _ x

/-- The encoded incidence of a retained world lies in the encoded event exactly when the
incidence lies in the world's event. -/
theorem encInc_mem_event (γ : Fin S.W) (hγ : S.Retained γ) (p : Incidence) :
    S.encInc γ p ∈ S.event ↔ p ∈ S.E γ := by
  constructor
  · rintro ⟨γ', -, hmod, hmem⟩
    have hγ' : γ' = γ := by
      apply Fin.ext
      rw [← hmod]
      exact encIdx_mod γ p.1.1
    subst hγ'
    have hdiv : encIdx S.W γ' p.1.1 / S.W = p.1.1 := encIdx_div γ' p.1.1
    simp only [Sample.encInc, Sample.enc, encLine] at hmem
    rw [hdiv, h.dec_enc] at hmem
    exact hmem
  · intro hp
    refine ⟨γ, hγ, encIdx_mod γ p.1.1, ?_⟩
    have hdiv : encIdx S.W γ p.1.1 / S.W = p.1.1 := encIdx_div γ p.1.1
    simp only [Sample.encInc, Sample.enc, encLine]
    rw [hdiv, h.dec_enc]
    exact hp

omit h in
/-- Incidences of worlds which are not retained are never in the encoded event. -/
theorem encInc_not_mem_event (γ : Fin S.W) (hγ : ¬ S.Retained γ) (p : Incidence) :
    S.encInc γ p ∉ S.event := by
  rintro ⟨γ', hγ', hmod, -⟩
  have : γ' = γ := by
    apply Fin.ext
    rw [← hmod]
    exact encIdx_mod γ p.1.1
  subst this
  exact hγ hγ'

theorem preimage_encInc_event (γ : Fin S.W) :
    S.encInc γ ⁻¹' S.event = {_p | S.Retained γ} ∩ S.E γ := by
  ext p
  by_cases hγ : S.Retained γ
  · simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hγ, true_and]
    exact h.encInc_mem_event γ hγ p
  · simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hγ, false_and, iff_false]
    exact encInc_not_mem_event γ hγ p

end Hyp

theorem measurableSet_event (hE : ∀ γ, MeasurableSet (S.E γ)) : MeasurableSet S.event := by
  have : S.event = ⋃ γ : Fin S.W, ({p : Incidence | S.Retained γ} ∩
      ({p : Incidence | p.1.1 % S.W = (γ : ℕ)} ∩
        (fun p : Incidence => ((p.1.1 / S.W, decCoeff S.a (S.b γ) (S.θ γ) (S.o γ) p.1.2), p.2)) ⁻¹'
          S.E γ)) := by
    ext p
    simp only [Sample.event, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  rw [this]
  have hfst : Measurable (fun p : Incidence => p.1.1) := measurable_fst.comp measurable_fst
  have hmod : Measurable (fun p : Incidence => p.1.1 % S.W) :=
    (measurable_from_top (f := fun n : ℕ => n % S.W)).comp hfst
  have hdiv : Measurable (fun p : Incidence => p.1.1 / S.W) :=
    (measurable_from_top (f := fun n : ℕ => n / S.W)).comp hfst
  refine MeasurableSet.iUnion fun γ => ?_
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter ?_ ?_)
  · exact hmod (measurableSet_singleton _)
  · refine (hE γ).preimage ?_
    refine Measurable.prodMk (Measurable.prodMk hdiv ?_) measurable_snd
    exact (continuous_decCoeff _ _ _ _).measurable.comp (measurable_snd.comp measurable_fst)

/-- The encoded product law is the weighted sum of the world laws pulled back by the
encodings. -/
theorem prior_prod_apply [∀ γ, SFinite (S.ν γ)] {X : Set Incidence} (hX : MeasurableSet X) :
    (S.prior.prod volume) X =
      ∑ γ, ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) (S.encInc γ ⁻¹' X) := by
  rw [Measure.prod_apply hX, Sample.prior, lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [lintegral_smul_measure, lintegral_map (measurable_measure_prodMk_left hX) (measurable_enc γ),
    Measure.prod_apply (hX.preimage (measurable_encInc γ))]
  rfl

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
