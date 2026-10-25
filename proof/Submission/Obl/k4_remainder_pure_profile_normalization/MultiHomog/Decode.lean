import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.OneWorld

/-!
# Decoding a selection of the encoded world

A measurable selection `E''` of the encoded event, in Boolean polynomial format, pulls back
to the world events `encInc γ ⁻¹' E''`. They keep every tempered condition, and their
weighted mass is the encoded mass; the encoded law is the weighted sum of the pushed
forward world laws.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

namespace Sample

variable {S : Sample}

/-- The decoded world events of an encoded selection. -/
def decEvent (S : Sample) (E'' : Set Incidence) (γ : Fin S.W) : Set Incidence :=
  S.encInc γ ⁻¹' E''

/-- The decoded world laws. -/
noncomputable def decLaw (S : Sample) (E'' : Set Incidence) (γ : Fin S.W) : Measure Incidence :=
  ((S.ν γ).prod volume).restrict (S.decEvent E'' γ)

namespace Hyp

variable (h : S.Hyp)
include h

theorem decEvent_subset {E'' : Set Incidence} (hsub : E'' ⊆ S.event) (γ : Fin S.W) :
    S.decEvent E'' γ ⊆ S.E γ := by
  intro p hp
  have : p ∈ S.encInc γ ⁻¹' S.event := hsub hp
  rw [h.preimage_encInc_event] at this
  exact this.2

theorem decEvent_empty {E'' : Set Incidence} (hsub : E'' ⊆ S.event) (γ : Fin S.W)
    (hγ : ¬ S.Retained γ) : S.decEvent E'' γ = ∅ := by
  ext p
  simp only [mem_empty_iff_false, iff_false]
  intro hp
  exact encInc_not_mem_event γ hγ p (hsub hp)

/-- The weighted mass of the decoded selection is the encoded mass. -/
theorem decoded_mass {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') :
    ∑ γ, ENNReal.ofReal (S.ω γ) * ((S.ν γ).prod volume) (S.decEvent E'' γ) =
      ((S.prior.prod volume).restrict E'') univ := by
  have := hT.prob
  rw [Measure.restrict_apply_univ, prior_prod_apply hE'']
  rfl

/-- The encoded selected law is the weighted sum of the pushed forward decoded laws. -/
theorem law_decomposition {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') :
    (S.prior.prod volume).restrict E'' =
      ∑ γ, ENNReal.ofReal (S.ω γ) • (S.decLaw E'' γ).map (S.encInc γ) := by
  have := hT.prob
  ext X hX
  rw [Measure.restrict_apply hX, prior_prod_apply (hX.inter hE''), Measure.coe_finsetSum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_encInc γ) hX,
    Sample.decLaw, Measure.restrict_apply (hX.preimage (measurable_encInc γ))]
  rfl

/-- The decoded selection keeps every tempered condition. -/
theorem decoded_tempered {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} {K'' : ℝ} {M' D' : ℕ} (hE'' : MeasurableSet E'')
    (hsub : E'' ⊆ S.event)
    (hfmt : ∀ n : ℕ, fmt 7 (S.N ^ M') D'
      {x : Fin 7 → ℝ | ((n, fun j : Fin 6 => x j.castSucc), x 6) ∈ E''})
    (hmass : ENNReal.ofReal K''⁻¹ ≤ ((S.prior.prod volume).restrict E'') univ)
    (hK'' : 0 < K'') :
    Tempered S.N (max S.K K'') (max S.M M') (max D D') S.W S.ω S.ν (S.decEvent E'') S.B := by
  have hN1 := h.one_le_N
  have hMle : S.N ^ S.M ≤ S.N ^ (max S.M M') := pow_le_pow_right₀ hN1 (le_max_left _ _)
  have hM'le : S.N ^ M' ≤ S.N ^ (max S.M M') := pow_le_pow_right₀ hN1 (le_max_right _ _)
  refine
    { card := hT.card.trans hMle
      weight_nonneg := hT.weight_nonneg
      weight_sum := hT.weight_sum
      prob := hT.prob
      scale_pos := hT.scale_pos
      scale_le := fun γ => (hT.scale_le γ).trans hMle
      scale_inv_le := fun γ => (hT.scale_inv_le γ).trans hMle
      prior := fun γ => ?_
      event_meas := fun γ => hE''.preimage (measurable_encInc γ)
      event_time := fun γ => (h.decEvent_subset hsub γ).trans (hT.event_time γ)
      event_bdd := fun γ p hp => ?_
      event_fmt := fun γ i => ?_
      native := fun γ => ?_
      mass := ?_ }
  · obtain ⟨m, hm, c, i, A, hA, hν⟩ := hT.prior γ
    refine ⟨m, hm.trans hMle, c, i, A, fun j => ?_, hν⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hA j
    exact ⟨h1, h2.trans hMle, h3.trans hMle, fmt_mono h4 hMle (le_max_left _ _),
      fun x hx b => (h5 x hx b).trans hMle⟩
  · obtain ⟨h1, h2⟩ := hT.event_bdd γ p (h.decEvent_subset hsub γ hp)
    exact ⟨h1.trans hMle, fun e => (h2 e).trans hMle⟩
  · have hset : {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ S.decEvent E'' γ} =
        {x : Fin 7 → ℝ | ((encIdx S.W γ i, encCoeff S.a (S.b γ) (S.θ γ) (S.o γ)
          (fun j : Fin 6 => x j.castSucc)), x 6) ∈ E''} := by
      ext x
      rfl
    rw [hset, encCoeff_eq_diagAffine]
    exact fmt_mono (fmt_slice_diagAffine (hfmt (encIdx S.W γ i)) _ _) hM'le (le_max_right _ _)
  · filter_upwards [hT.native γ] with l hl t ht
    exact (hl t ht).trans (le_max_left _ _)
  · rw [h.decoded_mass hT hE'']
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    exact inv_anti₀ hK'' (le_max_right _ _)

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
