/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open Set MeasureTheory ProbabilityTheory

namespace Submission.Lib.K4PolynomialNorming

/-- Two distinct coordinates in a finite product have the product law. -/
theorem pi_pair_measure_preimage {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (i j : ι) (hij : i ≠ j) (S : Set (α × α)) (hS : MeasurableSet S) :
    Measure.pi μ {a | (a i, a j) ∈ S} = (μ i |>.prod (μ j)) S := by
  have hind : iIndepFun (fun i (a : ι → α) => a i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hmap := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval μ i).map_eq, (measurePreserving_eval μ j).map_eq] at hmap
  rw [← hmap, Measure.map_apply (by fun_prop) hS]
  rfl

/-- A uniform small-ball cap bounds the law of a close independent pair. -/
theorem close_pair_measure_le {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [BorelSpace α] [SecondCountableTopology α] (μ : Measure α) [IsProbabilityMeasure μ]
    (r : ℝ) (τ : ENNReal) (hcap : ∀ x, μ (Metric.ball x r) ≤ τ) :
    (μ.prod μ) {p : α × α | dist p.1 p.2 < r} ≤ τ := by
  have hS : MeasurableSet {p : α × α | dist p.1 p.2 < r} := measurableSet_lt (measurable_fst.dist measurable_snd) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ _x, τ ∂μ := lintegral_mono fun x => by
      simpa only [Set.preimage_ofPred_eq, Metric.ball, dist_comm] using hcap x
    _ = τ := by simp

/-- The probability that some two coordinates violate a relation is at most
quadratic in the tuple length. -/
theorem pi_bad_pairs_measure_le {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Set (α × α))
    (hS : MeasurableSet S) (τ : ENNReal) (hpair : (μ.prod μ) S ≤ τ) :
    Measure.pi (fun _ : ι => μ) {a | ∃ i j, i ≠ j ∧ (a i, a j) ∈ S} ≤
      (Fintype.card ι : ENNReal) ^ 2 * τ := by
  classical
  let E (i j : ι) : Set (ι → α) := {a | i ≠ j ∧ (a i, a j) ∈ S}
  have hE (i j : ι) : Measure.pi (fun _ : ι => μ) (E i j) ≤ τ := by
    by_cases hij : i = j
    · simp [E, hij]
    · simpa [E, hij] using
        (pi_pair_measure_preimage (fun _ : ι => μ) i j hij S hS).le.trans hpair
  have hset : {a : ι → α | ∃ i j, i ≠ j ∧ (a i, a j) ∈ S} = ⋃ i, ⋃ j, E i j := by
    ext a; simp [E]
  rw [hset]
  calc
    _ ≤ ∑ i, Measure.pi (fun _ : ι => μ) (⋃ j, E i j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑ j, Measure.pi (fun _ : ι => μ) (E i j) :=
      Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι, τ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hE i j
    _ = _ := by simp [pow_two, mul_assoc]



/-- Collision exclusion for independently sampled anchors on each Cartesian
axis. Only the one-axis close-pair budget is needed. -/
theorem cartesian_bad_pairs_measure_le {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (S : ι → Set (α × α)) (hS : ∀ i, MeasurableSet (S i))
    (τ : ENNReal) (hpair : ∀ i, ((μ i).prod (μ i)) (S i) ≤ τ) :
    Measure.pi (fun i => Measure.pi (fun _ : κ => μ i))
      {a | ∃ i j k, j ≠ k ∧ (a i j, a i k) ∈ S i} ≤
        (Fintype.card ι : ENNReal) * (Fintype.card κ : ENNReal) ^ 2 * τ := by
  classical
  let B (i : ι) : Set (κ → α) := {a | ∃ j k, j ≠ k ∧ (a j, a k) ∈ S i}
  have hB (i : ι) : MeasurableSet (B i) := by
    simp only [B, ofPred_exists]
    apply MeasurableSet.iUnion; intro j
    apply MeasurableSet.iUnion; intro k
    by_cases hjk : j = k
    · simp [hjk]
    · have heq : {a : κ → α | j ≠ k ∧ (a j, a k) ∈ S i} =
          (fun a : κ → α => (a j, a k)) ⁻¹' S i := by ext a; simp [hjk]
      rw [heq]
      exact (hS i).preimage ((measurable_pi_apply j).prodMk (measurable_pi_apply k))
  have hE (i : ι) :
      Measure.pi (fun i => Measure.pi (fun _ : κ => μ i)) {a | a i ∈ B i} ≤
        (Fintype.card κ : ENNReal) ^ 2 * τ := by
    change Measure.pi (fun i => Measure.pi (fun _ : κ => μ i)) (Function.eval i ⁻¹' B i) ≤ _
    rw [(measurePreserving_eval (fun i => Measure.pi (fun _ : κ => μ i)) i).measure_preimage
      (hB i).nullMeasurableSet]
    exact pi_bad_pairs_measure_le (μ i) (S i) (hS i) τ (hpair i)
  have hset : {a : ι → κ → α | ∃ i j k, j ≠ k ∧ (a i j, a i k) ∈ S i} =
      ⋃ i, {a | a i ∈ B i} := by ext a; simp [B]
  rw [hset]
  calc
    _ ≤ ∑ i, Measure.pi (fun i => Measure.pi (fun _ : κ => μ i)) {a | a i ∈ B i} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, (Fintype.card κ : ENNReal) ^ 2 * τ :=
      Finset.sum_le_sum fun i _ => hE i
    _ = _ := by simp [mul_assoc]

/-- Small-ball caps supply the close-pair budget for real Cartesian anchors. -/
theorem cartesian_close_pairs_measure_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) (τ : ENNReal) (hcap : ∀ i x, μ i (Metric.ball x r) ≤ τ) :
    Measure.pi (fun i => Measure.pi (fun _ : κ => μ i))
      {a | ∃ i j k, j ≠ k ∧ |a i j - a i k| < r} ≤
        (Fintype.card ι : ENNReal) * (Fintype.card κ : ENNReal) ^ 2 * τ := by
  have h := cartesian_bad_pairs_measure_le (κ := κ) μ
    (fun _ => {p : ℝ × ℝ | dist p.1 p.2 < r})
    (fun _ => measurableSet_lt (measurable_fst.dist measurable_snd) measurable_const)
    τ (fun i => close_pair_measure_le (μ i) r τ (hcap i))
  simpa only [Real.dist_eq, Set.mem_ofPred_eq] using h

end Submission.Lib.K4PolynomialNorming
