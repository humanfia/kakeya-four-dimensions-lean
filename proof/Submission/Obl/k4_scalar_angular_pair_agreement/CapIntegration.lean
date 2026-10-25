import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Set

/-- A uniformly bounded fiber is charged to its base support. -/
theorem prod_mass_le_fiber_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν] (S : Set X) (U : Set (X × Y))
    (C : ENNReal) (hU : MeasurableSet U)
    (hsub : ∀ p ∈ U, p.1 ∈ S)
    (hsec : ∀ x ∈ S, ν {y | (x, y) ∈ U} ≤ C) :
    (μ.prod ν) U ≤ C * μ S := by
  classical
  rw [Measure.prod_apply hU]
  calc
    _ ≤ ∫⁻ x, S.indicator (fun _ => C) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact hsec x hx
      · have he : Prod.mk x ⁻¹' U = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          exact fun y hy => hx (hsub (x, y) hy)
        simp only [he, measure_empty, Set.indicator_of_notMem hx, le_refl]
    _ ≤ C * μ S := lintegral_indicator_const_le S C

/-- The accepted density-cap estimate pulled back along the original observation law. -/
theorem capped_observation_mass_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (obs : X → Y) (hobs : Measurable obs)
    (ρ : Y → ENNReal) (hρ : Measurable ρ)
    (hmap : μ.map obs = ν.withDensity ρ)
    (U : Set Y) (hU : MeasurableSet U) (C B : ENNReal) (hbase : ν U ≤ B) :
    μ {x | obs x ∈ U ∧ ρ (obs x) ≤ C} ≤ C * B := by
  have he : {x | obs x ∈ U ∧ ρ (obs x) ≤ C} =
      (obs ⁻¹' U) \ {x | C < ρ (obs x)} := by
    ext x
    simp only [mem_ofPred_eq, mem_sdiff, mem_preimage, not_lt]
  rw [he]
  have h := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.mass_le_of_density_le
    hobs hρ hmap hU C (P := obs ⁻¹' U) Subset.rfl
  exact h.trans (by gcongr)

/-- Two counting coordinates multiply their fiber bounds without conditioning the base. -/
theorem joint_reference_mass_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (U : Set ((X × ℤ) × ℤ)) (C D : ENNReal)
    (hU : MeasurableSet U) (hsub : ∀ p ∈ U, p.1.1 ∈ S)
    (hfirst : ∀ x ∈ S,
      Measure.count {j : ℤ | ∃ k : ℤ, ((x, j), k) ∈ U} ≤ C)
    (hsecond : ∀ x : X, ∀ j : ℤ,
      Measure.count {k : ℤ | ((x, j), k) ∈ U} ≤ D) :
    ((μ.prod Measure.count).prod Measure.count) U ≤ C * D * μ S := by
  let V : Set (X × ℤ) := {p | ∃ k : ℤ, (p, k) ∈ U}
  have hV : MeasurableSet V := by
    have he : V = ⋃ k : ℤ, (fun p : X × ℤ => (p, k)) ⁻¹' U := by
      ext p
      simp only [V, mem_ofPred_eq, mem_iUnion, mem_preimage]
    rw [he]
    exact MeasurableSet.iUnion (fun k => hU.preimage (measurable_id.prodMk measurable_const))
  have hUV : ((μ.prod Measure.count).prod Measure.count) U ≤
      D * (μ.prod Measure.count) V := by
    apply prod_mass_le_fiber_bound (μ.prod Measure.count) Measure.count V U D hU
    · exact fun p hp => ⟨p.2, hp⟩
    · intro p _
      exact hsecond p.1 p.2
  have hVS : (μ.prod Measure.count) V ≤ C * μ S := by
    apply prod_mass_le_fiber_bound μ Measure.count S V C hV
    · rintro ⟨x, j⟩ ⟨k, hk⟩
      exact hsub ((x, j), k) hk
    · exact hfirst
  calc
    _ ≤ D * (μ.prod Measure.count) V := hUV
    _ ≤ D * (C * μ S) := by gcongr
    _ = C * D * μ S := by ring

/-- A list of at most `K` labels, each admitting at most `D` angular bins,
adds only the product `K * D` to the reference-measure budget. -/
theorem listed_angular_reference_bound {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (H : Set (X × ℤ)) (hH : MeasurableSet H)
    (Λ : X × ℤ → Finset ι) (hΛ : ∀ i, MeasurableSet {p | i ∈ Λ p})
    (V : ι → Finset ℤ) (M K D : ENNReal)
    (hfirst : ∀ x ∈ S, Measure.count {j : ℤ | (x, j) ∈ H} ≤ M)
    (hlist : ∀ p, ((Λ p).card : ENNReal) ≤ K)
    (hbins : ∀ i, ((V i).card : ENNReal) ≤ D) :
    ((μ.prod Measure.count).prod Measure.count)
      {z : (X × ℤ) × ℤ | z.1.1 ∈ S ∧ z.1 ∈ H ∧
        ∃ i, i ∈ Λ z.1 ∧ z.2 ∈ V i} ≤ M * (K * D) * μ S := by
  classical
  let U : Set ((X × ℤ) × ℤ) := {z | z.1.1 ∈ S ∧ z.1 ∈ H ∧
    ∃ i, i ∈ Λ z.1 ∧ z.2 ∈ V i}
  have hU : MeasurableSet U := by
    have hangular : MeasurableSet {z : (X × ℤ) × ℤ | ∃ i, i ∈ Λ z.1 ∧ z.2 ∈ V i} := by
      have he : {z : (X × ℤ) × ℤ | ∃ i, i ∈ Λ z.1 ∧ z.2 ∈ V i} =
          ⋃ i, {z : (X × ℤ) × ℤ | i ∈ Λ z.1 ∧ z.2 ∈ V i} := by ext z; simp
      rw [he]
      exact MeasurableSet.iUnion (fun i =>
        ((hΛ i).preimage measurable_fst).inter
          ((V i).countable_toSet.measurableSet.preimage measurable_snd))
    exact (hS.preimage (measurable_fst.comp measurable_fst)).inter
      ((hH.preimage measurable_fst).inter hangular)
  apply joint_reference_mass_le μ S U M (K * D) hU
  · exact fun z hz => hz.1
  · intro x hx
    exact (measure_mono (fun j hj => by obtain ⟨k, hk⟩ := hj; exact hk.2.1)).trans (hfirst x hx)
  · intro x j
    have hcount : Measure.count {k : ℤ | ((x, j), k) ∈ U} ≤
        (((Λ (x, j)).biUnion V).card : ENNReal) := by
      rw [← Measure.count_apply_finset]
      apply measure_mono
      intro k hk
      obtain ⟨i, hi, hik⟩ := hk.2.2
      exact Finset.mem_biUnion.mpr ⟨i, hi, hik⟩
    apply hcount.trans
    calc
      (((Λ (x, j)).biUnion V).card : ENNReal) ≤
          ((∑ i ∈ Λ (x, j), (V i).card : ℕ) : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i ∈ Λ (x, j), ((V i).card : ENNReal) := by simp only [Nat.cast_sum]
      _ ≤ ∑ i ∈ Λ (x, j), D := Finset.sum_le_sum (fun i _ => hbins i)
      _ = ((Λ (x, j)).card : ENNReal) * D := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * D := by gcongr; exact hlist (x, j)

end Submission.Obl.k4_scalar_angular_pair_agreement
