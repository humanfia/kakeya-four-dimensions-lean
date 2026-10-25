-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TimeSampling.lean;
-- only the namespace was renamed into o230's.
/- Original independent-time sampling and finite first-moment counts. -/

import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.StarSelection
import Submission.Obl.k4_scalar_true_terminal_lifting.ListMultiplicity

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem pi_pair_coordinates_preserving {n : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (i j : Fin n) (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin n → X => (x i, x j))
      (Measure.pi (fun _ : Fin n => ν)) (ν.prod ν) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hind : iIndepFun (fun i (x : Fin n → X) => x i)
      (Measure.pi (fun _ : Fin n => ν)) :=
    iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)
  rw [(hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
    (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => ν) j).map_eq]

theorem independent_tuple_collision_le {n : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (v : X → ℝ) (hv : Measurable v) (gap : ℝ) (B : ℝ≥0∞)
    (hpair : (ν.prod ν) {p | |v p.1 - v p.2| < gap} ≤ B) :
    (Measure.pi (fun _ : Fin n => ν))
      {x | ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap} ≤ (n : ℝ≥0∞)^2 * B := by
  classical
  let E : Fin n → Fin n → Set (Fin n → X) :=
    fun i j => {x | i ≠ j ∧ |v (x i) - v (x j)| < gap}
  have heq : {x : Fin n → X | ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap} =
      ⋃ i, ⋃ j, E i j := by ext x; simp [E]
  rw [heq]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (Measure.pi (fun _ : Fin n => ν)) (E i j) := by
      apply (measure_iUnion_fintype_le _ _).trans
      exact Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp [E, hij]
      · have hmp := pi_pair_coordinates_preserving ν i j hij
        have hm : MeasurableSet {p : X × X | |v p.1 - v p.2| < gap} :=
          measurableSet_lt ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).abs
            measurable_const
        have heq : E i j = (fun x : Fin n → X => (x i, x j)) ⁻¹'
            {p : X × X | |v p.1 - v p.2| < gap} := by
          ext x
          simp [E, hij]
        rw [heq, ← Measure.map_apply hmp.measurable hm, hmp.map_eq]
        exact hpair
    _ = _ := by simp [pow_two]; ring

theorem original_separated_tuple_budget {n : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (v : X → ℝ) (hv : Measurable v) (gap : ℝ) (B : ℝ≥0∞)
    (hpair : (ν.prod ν) {p | |v p.1 - v p.2| < gap} ≤ B)
    (A : Set X) (_hA : MeasurableSet A) :
    (ν A)^n ≤ (Measure.pi (fun _ : Fin n => ν))
      {x | (∀ i, x i ∈ A) ∧ Pairwise (fun i j => gap ≤ |v (x i) - v (x j)|)} +
      (n : ℝ≥0∞)^2 * B := by
  classical
  let μ := Measure.pi (fun _ : Fin n => ν)
  let bad : Set (Fin n → X) := {x | ∃ i j, i ≠ j ∧ |v (x i) - v (x j)| < gap}
  let allA : Set (Fin n → X) := {x | ∀ i, x i ∈ A}
  have hAprod : μ allA = (ν A)^n := by
    have heq : allA = univ.pi (fun _ : Fin n => A) := by
      ext x
      simp [allA]
    rw [heq, Measure.pi_pi]
    simp
  have hsub : allA ⊆ (allA \ bad) ∪ bad := by intro x hx; by_cases hb : x ∈ bad <;> simp_all
  have hb := independent_tuple_collision_le (n := n) ν v hv gap B hpair
  have heq : allA \ bad = {x | (∀ i, x i ∈ A) ∧
      Pairwise (fun i j => gap ≤ |v (x i) - v (x j)|)} := by
    ext x
    simp [allA, bad, Pairwise]
  calc
    (ν A)^n = μ allA := hAprod.symm
    _ ≤ μ (allA \ bad) + μ bad := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ _ := by rw [heq]; exact add_le_add le_rfl hb

theorem unit_time_pencil_le (gap : ℝ) (w : ℝ) :
    (volume : Measure ℝ) {t | |t - w| < gap} ≤ ENNReal.ofReal (2 * gap) := by
  have hs : {t : ℝ | |t - w| < gap} ⊆ Ioo (w - gap) (w + gap) := by
    intro t ht
    change |t - w| < gap at ht
    have h := abs_lt.mp ht
    constructor <;> linarith
  apply (measure_mono hs).trans
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem original_uniform_time_tuple_budget (n : ℕ) (gap : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Icc (0 : ℝ) 1) :
    (volume A)^n ≤
      (Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)))
        {x | (∀ i, x i ∈ A) ∧ Pairwise (fun i j => gap ≤ |x i - x j|)} +
      (n : ℝ≥0∞)^2 * ENNReal.ofReal (2 * gap) := by
  let ν := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  have hpalette : ν.map id ≤ (1 : ℝ≥0∞) • (volume : Measure ℝ) := by
    simpa using (Measure.restrict_le_self : ν ≤ (volume : Measure ℝ))
  have hp := pair_pencil_mass_le ν id measurable_id volume 1
    (ENNReal.ofReal (2 * gap)) gap hpalette (unit_time_pencil_le gap)
  have hpair : (ν.prod ν) {p | |p.1 - p.2| < gap} ≤ ENNReal.ofReal (2 * gap) := by
    simpa only [controlPencil, id_eq, one_mul] using hp
  have h := original_separated_tuple_budget (n := n) ν id measurable_id gap
    (ENNReal.ofReal (2 * gap)) hpair A hA
  have hνA : ν A = volume A := by
    rw [Measure.restrict_apply hA, inter_eq_left.mpr hsub]
  simpa only [hνA, id_eq] using h

theorem original_uniform_time_separated_lower (n : ℕ) (gap η : ℝ)
    (hη : 0 ≤ η) (hgap : 0 ≤ gap)
    (A : Set ℝ) (hA : MeasurableSet A) (hsub : A ⊆ Icc (0 : ℝ) 1)
    (hlength : ENNReal.ofReal η ≤ volume A)
    (hcollision : (n : ℝ)^2 * (2 * gap) ≤ η^n / 2) :
    ENNReal.ofReal (η^n / 2) ≤
      (Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)))
        {x | (∀ i, x i ∈ A) ∧ Pairwise (fun i j => gap ≤ |x i - x j|)} := by
  let ν := (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  let μ := Measure.pi (fun _ : Fin n => ν)
  let good : Set (Fin n → ℝ) :=
    {x | (∀ i, x i ∈ A) ∧ Pairwise (fun i j => gap ≤ |x i - x j|)}
  have hAfin : volume A ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono hsub)
    simp [Real.volume_Icc]
  have hηreal : η ≤ (volume A).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hAfin).mp hlength
  have hbudget := original_uniform_time_tuple_budget n gap A hA hsub
  change (volume A)^n ≤ μ good + (n : ℝ≥0∞)^2 * ENNReal.ofReal (2 * gap) at hbudget
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, by finiteness⟩) hbudget
  rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness), ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ good)).mpr
  have hpower := pow_le_pow_left₀ hη hηreal n
  linarith

def separatedTimeEvent (n : ℕ) (A : Set ℝ) (gap : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ A) ∧ Pairwise (fun i j => gap ≤ |x i - x j|)}

theorem measurableSet_separatedTimeEvent (n : ℕ) (A : Set ℝ)
    (hA : MeasurableSet A) (gap : ℝ) : MeasurableSet (separatedTimeEvent n A gap) := by
  classical
  have hall : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ A} := by
    have heq : {x : Fin n → ℝ | ∀ i, x i ∈ A} = univ.pi (fun _ => A) := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.univ_pi (fun _ => hA)
  have hsep : MeasurableSet {x : Fin n → ℝ | Pairwise (fun i j => gap ≤ |x i - x j|)} := by
    have heq : {x : Fin n → ℝ | Pairwise (fun i j => gap ≤ |x i - x j|)} =
        ⋂ i, ⋂ j, {x | i ≠ j → gap ≤ |x i - x j|} := by
      ext x
      simp [Pairwise]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simpa only [hij, ne_eq, false_implies, not_false_eq_true, true_implies, Pi.sub_apply] using
        measurableSet_le measurable_const
          ((measurable_pi_apply i).sub (measurable_pi_apply j)).abs
  exact hall.inter hsep

open Classical in
theorem finite_sampling_count {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (q B : ℝ) (_hq : 0 ≤ q) (hB : 0 ≤ B)
    (hlower : ∀ i, ENNReal.ofReal q ≤ μ (E i))
    (hcount : ∀ x, ((Finset.univ.filter (fun i => x ∈ E i)).card : ℝ) ≤ B) :
    (Fintype.card I : ℝ) * q ≤ B := by
  classical
  let L : Ω → Finset I := fun x => Finset.univ.filter (fun i => x ∈ E i)
  have hknown (i : I) : ∀ᵐ x ∂μ.restrict (E i), i ∈ L x := by
    filter_upwards [ae_restrict_mem (hE i)] with x hx
    simp [L, hx]
  have hcard (x : Ω) : ((L x).card : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    simpa using ENNReal.ofReal_le_ofReal (hcount x)
  have hbound := Submission.Obl.k4_scalar_true_terminal_lifting.sum_restrict_le_smul_of_list
    μ E hE L hknown (ENNReal.ofReal B) hcard
  have hu := Measure.le_iff.mp hbound univ MeasurableSet.univ
  have hupper : (∑ i, μ (E i)) ≤ ENNReal.ofReal B := by
    simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one] using hu
  have hlow : (Fintype.card I : ℝ≥0∞) * ENNReal.ofReal q ≤ ∑ i, μ (E i) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlower i)
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simpa using hlow.trans hupper

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
