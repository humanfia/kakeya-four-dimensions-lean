import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ListDensity

/-! The arbitrary-list refinement estimate summed in original world weights. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal

/-- A bounded pointwise list controls the mass of all its measurable event
restrictions, even when the list itself is not measurable. -/
theorem listed_restriction_mass {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (lst : Ω → Finset I) (hlist : ∀ i z, z ∈ E i → i ∈ lst z)
    (K : ENNReal) (hK : ∀ z, ((lst z).card : ENNReal) ≤ K)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∑ i, (μ.restrict (E i)) A) ≤ K * μ A := by
  classical
  have hpoint (z : Ω) : (∑ i, (E i).indicator (fun _ => (1 : ENNReal)) z) ≤ K := by
    let S : Finset I := Finset.univ.filter (fun i => z ∈ E i)
    have hcard : S.card ≤ (lst z).card := by
      apply Finset.card_le_card
      intro i hi
      exact hlist i z (Finset.mem_filter.mp hi).2
    calc
      _ = (S.card : ENNReal) := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
      _ ≤ ((lst z).card : ENNReal) := Nat.cast_le.mpr hcard
      _ ≤ K := hK z
  calc
    _ = ∫⁻ z, ∑ i, (E i).indicator (fun _ => (1 : ENNReal)) z ∂μ.restrict A := by
      rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hE i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [lintegral_indicator (hE i), lintegral_one,
        Measure.restrict_apply_univ, Measure.restrict_apply (hE i), Measure.restrict_apply hA]
      rw [inter_comm]
    _ ≤ ∫⁻ _z, K ∂μ.restrict A := lintegral_mono hpoint
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

theorem weighted_listed_restriction_mass
    {Ω W I : Type*} [MeasurableSpace Ω] [Fintype W] [Fintype I] [DecidableEq W]
    (μ : W → Measure Ω) (γ : I → W) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (lst : W → Ω → Finset I) (hlist : ∀ i z, z ∈ E i → i ∈ lst (γ i) z)
    (ω : W → ENNReal) (K : ENNReal) (hK : ∀ a z, ((lst a z).card : ENNReal) ≤ K)
    (A : W → Set Ω) (hA : ∀ a, MeasurableSet (A a)) :
    (∑ i, ω (γ i) * (μ (γ i)).restrict (E i) (A (γ i))) ≤
      K * ∑ a, ω a * μ a (A a) := by
  classical
  have hlocal (a : W) : (∑ i : {i // γ i = a}, (μ a).restrict (E i) (A a)) ≤ K * μ a (A a) := by
    apply listed_restriction_mass (μ a) (fun i : {i // γ i = a} => E i) (fun i => hE i)
      (fun z => (lst a z).subtype (fun i => γ i = a))
      (fun i z hz => Finset.mem_subtype.mpr (by simpa only [i.property] using hlist i z hz)) K
    · intro z
      have hc : ((lst a z).subtype (fun i => γ i = a)).card ≤ (lst a z).card := by
        rw [Finset.card_subtype]
        exact Finset.card_filter_le _ _
      exact (Nat.cast_le.mpr hc).trans (hK a z)
    · exact hA a
  calc
    _ = ∑ a, ∑ i : {i // γ i = a}, ω (γ i) * (μ (γ i)).restrict (E i) (A (γ i)) :=
      (Fintype.sum_fiberwise γ _).symm
    _ = ∑ a, ω a * ∑ i : {i // γ i = a}, (μ a).restrict (E i) (A a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ ≤ ∑ a, ω a * (K * μ a (A a)) := Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (hlocal a)
    _ = _ := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

theorem weighted_observation_list_lowDensity_mass
    {Ω Y W I : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Y] [MeasurableEq Y] [Fintype W] [Fintype I] [DecidableEq W]
    (μ : W → Measure Ω) [∀ a, IsFiniteMeasure (μ a)]
    (obs : W → Ω → Y) (hobs : ∀ a, Measurable (obs a))
    (ρ : Measure Y) [SigmaFinite ρ] (g : W → Y → ENNReal)
    (hg : ∀ a, Measurable (g a)) (hlaw : ∀ a, (μ a).map (obs a) = ρ.withDensity (g a))
    (γ : I → W) (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (H : I → Y → ENNReal) (hH : ∀ i, Measurable (H i))
    (hrestrict : ∀ i, ((μ (γ i)).restrict (E i)).map (obs (γ i)) = ρ.withDensity (H i))
    (lst : W → Y → Finset I)
    (hlist : ∀ i z, z ∈ E i → i ∈ lst (γ i) (obs (γ i) z))
    (ω : W → ENNReal) (ε K : ENNReal)
    (hK : ∀ a y, ((lst a y).card : ENNReal) ≤ K) :
    (∑ i, ω (γ i) * (μ (γ i)).restrict (E i)
      {z | H i (obs (γ i) z) < ε * g (γ i) (obs (γ i) z)}) ≤
        ε * K * ∑ a, ω a * μ a univ := by
  classical
  have hlocal (a : W) :
      (∑ i : {i // γ i = a}, (μ a).restrict (E i)
        {z | H i (obs a z) < ε * g a (obs a z)}) ≤ ε * K * μ a univ := by
    apply observation_list_lowDensity_mass (μ a) (obs a) (hobs a) ρ (g a) (hg a)
      (hlaw a) (fun i : {i // γ i = a} => E i) (fun i => hE i)
      (fun i => H i) (fun i => hH i)
      (fun i => by simpa only [i.property] using hrestrict i)
      (fun y => (lst a y).subtype (fun i => γ i = a))
      (fun i z hz => Finset.mem_subtype.mpr (by
        simpa only [i.property] using hlist i z hz)) ε K
    intro y
    have hc : ((lst a y).subtype (fun i => γ i = a)).card ≤ (lst a y).card := by
      rw [Finset.card_subtype]
      exact Finset.card_filter_le _ _
    exact (Nat.cast_le.mpr hc).trans (hK a y)
  calc
    _ = ∑ a, ∑ i : {i // γ i = a}, ω (γ i) * (μ (γ i)).restrict (E i)
        {z | H i (obs (γ i) z) < ε * g (γ i) (obs (γ i) z)} :=
      (Fintype.sum_fiberwise γ _).symm
    _ = ∑ a, ω a * ∑ i : {i // γ i = a}, (μ a).restrict (E i)
        {z | H i (obs a z) < ε * g a (obs a z)} := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ ≤ ∑ a, ω a * (ε * K * μ a univ) :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (hlocal a)
    _ = _ := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
