import Submission.Obl.k4_oss_weighted_level_transfer.Finite

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

attribute [local instance] Classical.propDecidable

noncomputable def counting {X : Type*} [MeasurableSpace X] (A : Finset X) : Measure X :=
  ∑ x ∈ A, Measure.dirac x

noncomputable def atomic {X : Type*} [MeasurableSpace X] (A : Finset X)
    (p : X → ℝ) : Measure X := ∑ x ∈ A, ENNReal.ofReal (p x) • Measure.dirac x

theorem counting_finite {X : Type*} [MeasurableSpace X] (A : Finset X) :
    IsFiniteMeasure (counting A) := by unfold counting; infer_instance

attribute [local instance] counting_finite

lemma prod_finset_left {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset I) (μ : I → Measure X) (ν : Measure Y) [IsFiniteMeasure ν]
    [∀ i, IsFiniteMeasure (μ i)] :
    (∑ i ∈ s, μ i).prod ν = ∑ i ∈ s, (μ i).prod ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Measure.add_prod, ih]

lemma prod_finset_right {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset I) (μ : Measure X) (ν : I → Measure Y) [IsFiniteMeasure μ]
    [∀ i, IsFiniteMeasure (ν i)] :
    μ.prod (∑ i ∈ s, ν i) = ∑ i ∈ s, μ.prod (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Measure.prod_add, ih]

lemma map_finset {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset I) (μ : I → Measure X) (f : X → Y) (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Measure.map_add _ _ hf, ih]

lemma counting_apply {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Finset X) (E : Set X) :
    counting A E = ((A.filter (fun x => x ∈ E)).card : ℝ≥0∞) := by
  classical
  simp only [counting, Measure.finsetSum_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma counting_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (A : Finset X) (B : Finset Y) :
    (counting A).prod (counting B) = counting (A ×ˢ B) := by
  classical
  simp only [counting, prod_finset_left, prod_finset_right, Measure.dirac_prod_dirac,
    Finset.sum_product]
  exact Finset.sum_comm

noncomputable abbrev projected (t : ℝ) (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + t * p.2)

lemma projected_mono (t : ℝ) {μ μ' ν ν' : Measure ℝ} [SFinite ν] [SFinite ν']
    (hμ : μ ≤ μ') (hν : ν ≤ ν') : projected t μ ν ≤ projected t μ' ν' :=
  Measure.map_mono (Measure.prod_mono hμ hν) (by fun_prop)

lemma collision_mono {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (h : μ ≤ ν) (r : ℝ) : collision r μ ≤ collision r ν :=
  (Measure.prod_mono h h) _

lemma projected_smul (t : ℝ) (a b : ℝ≥0∞) (μ ν : Measure ℝ) [SFinite ν] :
    projected t (a • μ) (b • ν) = (a * b) • projected t μ ν := by
  rw [projected, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_smul _ (by fun_prop), Measure.map_smul _ (by fun_prop), smul_smul]

lemma collision_smul (r : ℝ) (a : ℝ≥0∞) (μ : Measure ℝ) [SFinite μ] :
    collision r (a • μ) = (a * a) * collision r μ := by
  simp only [collision, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.smul_apply, smul_eq_mul]
  ring

lemma projected_finset {I J : Type*} (s : Finset I) (v : Finset J)
    (t : ℝ) (μ : I → Measure ℝ) (ν : J → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    projected t (∑ i ∈ s, μ i) (∑ j ∈ v, ν j) =
      ∑ q ∈ s ×ˢ v, projected t (μ q.1) (ν q.2) := by
  classical
  simp only [projected, prod_finset_left, prod_finset_right, map_finset _ _ (fun p : ℝ × ℝ => p.1 + t * p.2) (by fun_prop),
    Finset.sum_product]
  exact Finset.sum_comm

lemma projected_counting_collision (δ t : ℝ) (A B : Finset ℝ) :
    collision (16 * δ) (projected t (counting A) (counting B)) =
      ENNReal.ofReal (finiteEnergy δ t A B) := by
  classical
  let f : ℝ × ℝ → ℝ := fun p => p.1 + t * p.2
  have hf : Measurable f := by fun_prop
  change ((Measure.map f ((counting A).prod (counting B))).prod
    (Measure.map f ((counting A).prod (counting B))))
      {p : ℝ × ℝ | |p.1 - p.2| ≤ 16 * δ} = _
  rw [Measure.map_prod_map _ _ hf hf, Measure.map_apply (hf.prodMap hf) (measurableSet_le (by fun_prop) measurable_const),
    counting_prod, counting_prod, counting_apply]
  simp only [finiteEnergy, ENNReal.ofReal_natCast, f, Set.preimage_setOf_eq, Set.mem_setOf_eq, Prod.map_fst, Prod.map_snd]

/-- Collision of a sum of rectangular atomic laws reduces to uniform finite energies. -/
lemma collision_level_sum {I J : Type*} [Fintype I] [Fintype J]
    (t δ : ℝ) (hδ : 0 < δ) (A : I → Finset ℝ) (B : J → Finset ℝ)
    (a : I → ℝ≥0∞) (b : J → ℝ≥0∞) (ha : ∀ i, a i ≠ ∞) (hb : ∀ j, b j ≠ ∞) :
    collision (16 * δ)
        (projected t (∑ i, a i • counting (A i)) (∑ j, b j • counting (B j))) ≤
      3 * (Fintype.card I * Fintype.card J : ℝ≥0∞) *
        ∑ i, ∑ j, (a i * b j) * (a i * b j) * ENNReal.ofReal (finiteEnergy δ t (A i) (B j)) := by
  classical
  letI (i : I) : IsFiniteMeasure (a i • counting (A i)) := by
    exact (counting (A i)).smul_finite (ha i)
  letI (j : J) : IsFiniteMeasure (b j • counting (B j)) := by
    exact (counting (B j)).smul_finite (hb j)
  rw [projected_finset]
  simp only [Finset.univ_product_univ]
  have h := collision_sum_le (fun q : I × J =>
    projected t (a q.1 • counting (A q.1)) (b q.2 • counting (B q.2)))
    (show 0 < 16 * δ by positivity)
  simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    projected_smul, collision_smul, projected_counting_collision] using h

end Submission.Obl.k4_oss_weighted_level_transfer
