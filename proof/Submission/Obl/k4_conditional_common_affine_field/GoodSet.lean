import Submission.Obl.k4_conditional_common_affine_field.Geometry

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory

def chartFits {α : Type*} (b v : α → ℝ) (χb χv K e : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ))
    (p : α × ℝ) : Prop :=
  ∃ a ∈ L (⌊b p.1/χb⌋,⌊v p.1/χv⌋),
    |f p 0-a 0-a 1*p.2| ≤ K*e ∧ |f p 1-a 2| ≤ K*e

theorem measurableSet_chartFits {α : Type*} [MeasurableSpace α]
    {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) (χb χv K e : ℝ)
    {f : α × ℝ → Fin 2 → ℝ} (hf : Measurable f)
    (L : ℤ × ℤ → Finset (Fin 3 → ℝ)) :
    MeasurableSet {p | chartFits b v χb χv K e f L p} := by
  classical
  let code : α × ℝ → ℤ × ℤ := fun p => (⌊b p.1/χb⌋,⌊v p.1/χv⌋)
  have hcode : Measurable code :=
    (((hb.comp measurable_fst).div_const χb).floor).prodMk
      (((hv.comp measurable_fst).div_const χv).floor)
  let fit (a : Fin 3 → ℝ) : Set (α × ℝ) :=
    {p | |f p 0-a 0-a 1*p.2| ≤ K*e ∧ |f p 1-a 2| ≤ K*e}
  have hfit (a : Fin 3 → ℝ) : MeasurableSet (fit a) :=
    (measurableSet_le
      ((((measurable_pi_apply 0).comp hf).sub_const (a 0)).sub
        (measurable_const.mul measurable_snd)).abs measurable_const).inter
      (measurableSet_le (((measurable_pi_apply 1).comp hf).sub_const (a 2)).abs
        measurable_const)
  have heq : {p | chartFits b v χb χv K e f L p} =
      ⋃ q : ℤ × ℤ, {p | code p=q} ∩ ⋃ a ∈ L q, fit a := by
    ext p
    simp only [mem_setOf_eq,mem_iUnion,mem_inter_iff]
    constructor
    · rintro ⟨a,ha,hfit⟩
      exact ⟨code p,rfl,a,ha,hfit⟩
    · rintro ⟨q,hq,a,ha,hfit⟩
      refine ⟨a,?_,hfit⟩
      change a ∈ L (code p)
      rw [hq]
      exact ha
  rw [heq]
  exact MeasurableSet.iUnion fun q =>
    ((measurableSet_singleton q).preimage hcode).inter
      (MeasurableSet.biUnion (L q).countable_toSet (fun a _ => hfit a))

def goodSet {α : Type*} (b v : α → ℝ) (χb χv K e : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ)) : Set (α × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ (∀ i, |f p i| ≤ K) ∧ chartFits b v χb χv K e f L p}

theorem measurableSet_goodSet {α : Type*} [MeasurableSpace α]
    {b v : α → ℝ} (hb : Measurable b) (hv : Measurable v) (χb χv K e : ℝ)
    {f : α × ℝ → Fin 2 → ℝ} (hf : Measurable f)
    (L : ℤ × ℤ → Finset (Fin 3 → ℝ)) :
    MeasurableSet (goodSet b v χb χv K e f L) := by
  have hbound : MeasurableSet {p | ∀ i : Fin 2, |f p i| ≤ K} := by
    have heq : {p | ∀ i : Fin 2, |f p i| ≤ K} =
        ⋂ i : Fin 2, {p | |f p i| ≤ K} := by ext p; simp
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (((measurable_pi_apply i).comp hf).abs) measurable_const
  exact (measurableSet_Icc.preimage measurable_snd).inter
    (hbound.inter (measurableSet_chartFits hb hv χb χv K e hf L))

theorem ae_goodSet {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b v : α → ℝ) (χb χv K e : ℝ)
    (f : α × ℝ → Fin 2 → ℝ) (L : ℤ × ℤ → Finset (Fin 3 → ℝ))
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ᵐ p ∂μ, ∀ i, |f p i| ≤ K)
    (hfit : ∀ᵐ p ∂μ, chartFits b v χb χv K e f L p) :
    ∀ᵐ p ∂μ, p ∈ goodSet b v χb χv K e f L := by
  have ht : ∀ᵐ p ∂μ, p ∈ univ ×ˢ Icc (0 : ℝ) 1 := ae_iff.mpr htime
  filter_upwards [ht,hbound,hfit] with p hp hb hf
  exact ⟨hp.2,hb,hf⟩

end Submission.Obl.k4_conditional_common_affine_field
