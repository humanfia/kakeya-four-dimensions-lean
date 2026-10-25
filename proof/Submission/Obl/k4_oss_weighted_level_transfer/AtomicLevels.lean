import Submission.Obl.k4_oss_weighted_level_transfer.Atomic
import Submission.Obl.k4_oss_weighted_level_transfer.Interface

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable
attribute [local instance] counting_finite

lemma ofReal_dirac_finite {X : Type*} [MeasurableSpace X] (p : ℝ) (x : X) :
    IsFiniteMeasure (ENNReal.ofReal p • Measure.dirac x) :=
  (Measure.dirac x).smul_finite ENNReal.ofReal_ne_top

attribute [local instance] ofReal_dirac_finite

lemma atomic_finite {X : Type*} [MeasurableSpace X] (S : Finset X) (p : X → ℝ) :
    IsFiniteMeasure (atomic S p) := by unfold atomic; infer_instance

attribute [local instance] atomic_finite

lemma atomic_apply {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (E : Set X) :
    atomic S p E = ENNReal.ofReal (∑ x ∈ S, if x ∈ E then p x else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun x hx => by split; exact hp x; exact le_refl 0)]
  simp only [atomic, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero,
    apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]

lemma atomic_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (S : Finset X) (T : Finset Y) (p : X → ℝ) (q : Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) :
    (atomic S p).prod (atomic T q) = atomic (S ×ˢ T) (fun z => p z.1 * q z.2) := by
  classical
  simp only [atomic, prod_finset_left, prod_finset_right,
    Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
    Finset.smul_sum, smul_smul, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [ENNReal.ofReal_mul (hp x), mul_comm (ENNReal.ofReal (q y)) (ENNReal.ofReal (p x))]

lemma counting_as_sum (S A : Finset ℝ) (hA : A ⊆ S) :
    counting A = ∑ x ∈ S, if x ∈ A then Measure.dirac x else 0 := by
  have heq : S.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hx => hA hx
  calc
    _ = counting (S.filter (fun x => x ∈ A)) := congrArg counting heq.symm
    _ = _ := by simp only [counting, Finset.sum_filter]

lemma atomic_le_level_sum {I : Type*} [Fintype I] (S : Finset ℝ) (p : ℝ → ℝ)
    (A : I → Finset ℝ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hA : ∀ i, A i ⊆ S)
    (hcover : ∀ x ∈ S, p x ≤ ∑ i, if x ∈ A i then w i else 0) :
    atomic S p ≤ ∑ i, ENNReal.ofReal (w i) • counting (A i) := by
  have hsum : (∑ i, ENNReal.ofReal (w i) • counting (A i)) =
      ∑ x ∈ S, (∑ i, if x ∈ A i then ENNReal.ofReal (w i) else 0) • Measure.dirac x := by
    simp_rw [counting_as_sum S _ (hA _), Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [hsum, atomic]
  apply Finset.sum_le_sum
  intro x hx
  apply Measure.le_iff.mpr
  intro E hE
  simp only [Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ENNReal.ofReal (∑ i, if x ∈ A i then w i else 0) :=
      ENNReal.ofReal_le_ofReal (hcover x hx)
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => by split; exact hw i; exact le_refl 0)]
      simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero]

lemma map_counting (S : Finset ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hinj : Function.Injective f) :
    (counting S).map f = counting (S.image f) := by
  classical
  simp only [counting, map_finset _ _ f hf, Measure.map_dirac]
  rw [Finset.sum_image]
  exact fun x hx y hy h => hinj h

lemma atomic_collision_formula {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (S : Finset X) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → ℝ) (hf : Measurable f) (r : ℝ) :
    collision r ((atomic S p).map f) = ENNReal.ofReal
      (∑ x ∈ S, ∑ y ∈ S, p x * p y * (if |f x - f y| ≤ r then (1 : ℝ) else 0)) := by
  rw [collision, Measure.map_prod_map _ _ hf hf,
    Measure.map_apply (hf.prodMap hf) (measurableSet_le (by fun_prop) measurable_const),
    atomic_prod S S p p hp hp]
  rw [atomic_apply (S ×ˢ S) (fun z : X × X => p z.1 * p z.2)
    (fun z => mul_nonneg (hp z.1) (hp z.2))]
  congr 1
  simp only [Finset.sum_product, Set.mem_preimage, Set.mem_setOf_eq, Prod.map_fst,
    Prod.map_snd, mul_ite, mul_one, mul_zero]

noncomputable abbrev minusProjected (t : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - 2 * t * p.2)

lemma minusProjected_eq (t : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    minusProjected t μ = projected t μ (μ.map (fun x : ℝ => -2 * x)) := by
  have hm : Measurable (fun x : ℝ => -2 * x) := by fun_prop
  have h := Measure.map_prod_map μ μ measurable_id hm
  simp only [Measure.map_id] at h
  unfold minusProjected projected
  rw [h, Measure.map_map (by fun_prop) (measurable_id.prodMap hm)]
  congr 1
  ext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  ring

lemma collisionSum_eq (S : Finset ℝ) (p : ℝ → ℝ) (hp : ∀ x, 0 ≤ p x) (δ t : ℝ) :
    ENNReal.ofReal (collisionSum S p δ t) = collision (7 * δ) (minusProjected t (atomic S p)) := by
  rw [minusProjected, atomic_prod S S p p hp hp,
    atomic_collision_formula (S ×ˢ S) (fun z : ℝ × ℝ => p z.1 * p z.2)
      (fun z => mul_nonneg (hp z.1) (hp z.2))
      (fun z : ℝ × ℝ => z.1 - 2 * t * z.2) (by fun_prop)]
  congr 1
  simp only [collisionSum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  apply Finset.sum_congr rfl
  intro x₃ hx₃
  apply Finset.sum_congr rfl
  intro x₄ hx₄
  have heq : (x₁ - 2 * t * x₂) - (x₃ - 2 * t * x₄) =
      (x₁ - x₃) - 2 * t * (x₂ - x₄) := by ring
  rw [heq]
  ring

lemma collisionSum_le_projected (S : Finset ℝ) (p : ℝ → ℝ) (hp : ∀ x, 0 ≤ p x)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ENNReal.ofReal (collisionSum S p δ t) ≤
      collision (16 * δ) (projected t (atomic S p) ((atomic S p).map (fun x : ℝ => -2 * x))) := by
  rw [collisionSum_eq S p hp, ← minusProjected_eq]
  apply measure_mono
  intro z hz
  change |z.1 - z.2| ≤ 16 * δ
  exact (show |z.1 - z.2| ≤ 7 * δ from hz).trans (by linarith)

end Submission.Obl.k4_oss_weighted_level_transfer
