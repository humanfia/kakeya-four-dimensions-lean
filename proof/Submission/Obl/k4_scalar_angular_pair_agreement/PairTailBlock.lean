import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open Set MeasureTheory
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- In one time block, either bad marginal costs at most twice the original
bad incidence mass times the unnormalized length of the other time. -/
theorem pair_tail_block_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (Q : Set (X × ℝ)) (hQ : MeasurableSet Q)
    (T₁ : ℕ) (b : Fin (2 ^ T₁)) :
    (ν.prod (volume.prod volume))
      {z : X × (ℝ × ℝ) | z.2.1 ∈ I T₁ b ∧ z.2.2 ∈ I T₁ b ∧
        ((z.1, z.2.1) ∈ Q ∨ (z.1, z.2.2) ∈ Q)} ≤
      2 * ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) *
        (ν.prod volume) (Q ∩ univ ×ˢ I T₁ b) := by
  let Qb : Set (X × ℝ) := Q ∩ univ ×ˢ I T₁ b
  let E₁ : Set (X × (ℝ × ℝ)) := {z | (z.1, z.2.1) ∈ Qb ∧ z.2.2 ∈ I T₁ b}
  let E₂ : Set (X × (ℝ × ℝ)) := {z | z.2.1 ∈ I T₁ b ∧ (z.1, z.2.2) ∈ Qb}
  have hQb : MeasurableSet Qb := hQ.inter (MeasurableSet.univ.prod (measurableSet_I _ _))
  have hE₁ : MeasurableSet E₁ :=
    (hQb.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).inter
      ((measurableSet_I _ _).preimage (measurable_snd.comp measurable_snd))
  have hmass₁ : (ν.prod (volume.prod volume)) E₁ =
      (ν.prod volume) Qb * ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) := by
    rw [← Measure.prodAssoc_prod, Measure.map_apply MeasurableEquiv.prodAssoc.measurable hE₁]
    have he : MeasurableEquiv.prodAssoc ⁻¹' E₁ = Qb ×ˢ I T₁ b := by
      ext z
      rfl
    rw [he, Measure.prod_prod, volume_I]
  have hswap : MeasurePreserving
      (fun z : X × (ℝ × ℝ) => (z.1, (z.2.2, z.2.1)))
      (ν.prod (volume.prod volume)) (ν.prod (volume.prod volume)) :=
    (MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  have hmass₂ : (ν.prod (volume.prod volume)) E₂ =
      (ν.prod volume) Qb * ENNReal.ofReal (((2 : ℝ) ^ T₁)⁻¹) := by
    have he : E₂ = (fun z : X × (ℝ × ℝ) => (z.1, (z.2.2, z.2.1))) ⁻¹' E₁ := by
      ext z
      simp only [E₁, E₂, mem_ofPred_eq, mem_preimage, and_comm]
    rw [he, hswap.measure_preimage hE₁.nullMeasurableSet, hmass₁]
  calc
    _ ≤ (ν.prod (volume.prod volume)) (E₁ ∪ E₂) := by
      apply measure_mono
      rintro z ⟨hs, ht, hbad⟩
      rcases hbad with hsQ | htQ
      · exact Or.inl ⟨⟨hsQ, trivial, hs⟩, ht⟩
      · exact Or.inr ⟨hs, htQ, trivial, ht⟩
    _ ≤ (ν.prod (volume.prod volume)) E₁ + (ν.prod (volume.prod volume)) E₂ := measure_union_le _ _
    _ = _ := by rw [hmass₁, hmass₂]; dsimp [Qb]; ring

end Submission.Obl.k4_scalar_angular_pair_agreement
