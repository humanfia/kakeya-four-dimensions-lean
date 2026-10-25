import Submission.Lib.K4ContinuousKakeya.Continuous

set_option linter.unusedVariables false

/-!
# Incidence form of continuous multilinear Kakeya

Section 6 applies multilinear Kakeya to tubes about lines attached to trajectories (tangent lines
at a cube's central time for the velocity graph; the exact base lines for strip filling and heavy
intercept groups), weighted by the trajectory prior, while the masses it controls are incidence
masses in cells. `incidence_kakeya` packages that step: if the trajectories of `Λ` meeting a cell
have tubes containing the cell, the incidences of a cell push forward to at most `c • θ|Λ`
(`map_fst_restrict_le` derives this from `inc ≤ K • θ × time` and a time-section bound `b`), and
the `n`-fold incidence tuples of a cell with line determinant `≥ β` carry mass `≥ q j`, then
`∑ j vol(E j) (β q j / c^n)^(1/(n-1)) ≤ 2^n C r^n θ(Λ)^(n/(n-1))`.

Also: monotonicity and scaling of finite product measures (`pi_mono`, `pi_smul`), the
orthogonal-projection description of tubes (`mem_tube_iff`) and its measurability.
-/

namespace Submission.Lib.K4ContinuousKakeya

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

/-- Monotonicity of finite product measures. -/
lemma pi_mono {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {ν μ : (i : ι) → Measure (α i)} (h : ∀ i, ν i ≤ μ i) :
    Measure.pi ν ≤ Measure.pi μ := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have hle : OuterMeasure.pi (fun i => (ν i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (μ i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro t _
    refine (OuterMeasure.pi_pi_le _ t).trans ?_
    exact Finset.prod_le_prod fun i _ => h i (t i)
  exact hle s

/-- Scaling every factor of a finite product measure scales the product. -/
lemma pi_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ℝ≥0) :
    Measure.pi (fun i => c • μ i) = (c : ℝ≥0∞) ^ Fintype.card ι • Measure.pi μ := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Squared distance from a point to a point of a line with unit direction. -/
lemma norm_sub_smul_sq {n : ℕ} (v e : EuclideanSpace ℝ (Fin n)) (c : ℝ) (he : ‖e‖ = 1) :
    ‖v - c • e‖ ^ 2 = ‖v‖ ^ 2 - 2 * c * inner ℝ e v + c ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, real_inner_comm]
  simp only [Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- The orthogonal projection is the closest point of the line. -/
lemma norm_sub_proj_le {n : ℕ} (v e : EuclideanSpace ℝ (Fin n)) (t : ℝ) (he : ‖e‖ = 1) :
    ‖v - (inner ℝ e v) • e‖ ≤ ‖v - t • e‖ := by
  have hsq : ‖v - (inner ℝ e v) • e‖ ^ 2 ≤ ‖v - t • e‖ ^ 2 := by
    rw [norm_sub_smul_sq v e _ he, norm_sub_smul_sq v e _ he]
    nlinarith [sq_nonneg (t - inner ℝ e v)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Membership in a tube about a line with unit direction, via the orthogonal projection. -/
lemma mem_tube_iff {n : ℕ} {r : ℝ} {a e x : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) :
    x ∈ tube r a e ↔ ‖(x - a) - (inner ℝ e (x - a)) • e‖ < r := by
  constructor
  · intro hx
    obtain ⟨y, ⟨t, rfl⟩, hxy⟩ := Metric.mem_thickening_iff.mp hx
    rw [dist_eq_norm] at hxy
    have h1 : ‖(x - a) - t • e‖ = ‖x - (a + t • e)‖ := by
      congr 1; abel
    exact lt_of_le_of_lt ((norm_sub_proj_le (x - a) e t he).trans h1.le) hxy
  · intro hx
    apply Metric.mem_thickening_iff.mpr
    refine ⟨a + (inner ℝ e (x - a)) • e, ⟨inner ℝ e (x - a), rfl⟩, ?_⟩
    rw [dist_eq_norm]
    have : x - (a + (inner ℝ e (x - a)) • e) = (x - a) - (inner ℝ e (x - a)) • e := by abel
    rw [this]
    exact hx

/-- For measurable base points and unit directions, membership of a fixed point in the tubes is
a measurable condition on the parameter. -/
lemma measurableSet_mem_tube {n : ℕ} {α : Type*} [MeasurableSpace α] (r : ℝ)
    (a e : α → EuclideanSpace ℝ (Fin n)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet {l | x ∈ tube r (a l) (e l)} := by
  have : {l | x ∈ tube r (a l) (e l)} =
      {l | ‖(x - a l) - (inner ℝ (e l) (x - a l)) • e l‖ < r} := by
    ext l
    exact mem_tube_iff (he1 l)
  rw [this]
  apply measurableSet_lt _ measurable_const
  apply Measurable.norm
  apply Measurable.sub (measurable_const.sub ha)
  have hin : Measurable fun l => inner ℝ (e l) (x - a l) :=
    Measurable.inner (𝕜 := ℝ) he (measurable_const.sub ha)
  exact hin.smul he

/-- The pushforward to trajectories of an incidence measure dominated by `K • (θ × time)`,
restricted to a set whose time sections over `Λ` have length at most `b` and which lies over
`Λ`, is dominated by `(K * b) • θ|Λ`. -/
lemma map_fst_restrict_le {α : Type*} [MeasurableSpace α] (θ : Measure α) [SFinite θ]
    (inc : Measure (α × ℝ)) (K b : ℝ≥0) (hinc : inc ≤ K • θ.prod volume)
    (S : Set (α × ℝ)) (hS : MeasurableSet S) (Λ : Set α) (hΛ : MeasurableSet Λ)
    (hSΛ : ∀ ω ∈ S, ω.1 ∈ Λ) (hb : ∀ l ∈ Λ, volume {t : ℝ | (l, t) ∈ S} ≤ b) :
    (inc.restrict S).map Prod.fst ≤ (K * b) • θ.restrict Λ := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  calc inc (Prod.fst ⁻¹' A ∩ S) ≤ (K • θ.prod volume) (Prod.fst ⁻¹' A ∩ S) := hinc _
    _ = K * ∫⁻ l, volume (Prod.mk l ⁻¹' (Prod.fst ⁻¹' A ∩ S)) ∂θ := by
        rw [Measure.smul_apply, Measure.prod_apply ((measurable_fst hA).inter hS),
          ENNReal.smul_def, smul_eq_mul]
    _ ≤ K * ∫⁻ l, (Λ ∩ A).indicator (fun _ => (b : ℝ≥0∞)) l ∂θ := by
        gcongr with l
        by_cases hl : l ∈ Λ ∩ A
        · rw [Set.indicator_of_mem hl]
          refine (measure_mono ?_).trans (hb l hl.1)
          intro t ht
          exact ht.2
        · rw [Set.indicator_of_notMem hl]
          have : Prod.mk l ⁻¹' (Prod.fst ⁻¹' A ∩ S) = ∅ := by
            ext t
            simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
              not_and]
            intro hlA htS
            exact hl ⟨hSΛ _ htS, hlA⟩
          rw [this, measure_empty]
    _ = (K * b) * θ (Λ ∩ A) := by
        rw [lintegral_indicator_const (hΛ.inter hA), mul_assoc]
    _ = ((K * b) • θ.restrict Λ) A := by
        rw [Measure.smul_apply, Measure.restrict_apply hA, Set.inter_comm, ENNReal.smul_def,
          smul_eq_mul]
        push_cast
        ring

/-- **Incidence form of continuous multilinear Kakeya.** Let `inc` be an incidence measure on
trajectories × time, `Φ` its physical position in `ℝⁿ`, and `a`, `e` measurable lines (unit
directions, bounded base points) attached to the trajectories. On disjoint cells `E j` in a
ball, suppose that the trajectories of `Λ` meeting `E j` have tubes containing all of `E j`,
that the pushforward of the incidences in `E j` (over `Λ`) to trajectories is at most `c • θ|Λ`,
and that the `n`-fold incidence tuples in `E j` whose lines have determinant at least `β` carry
mass at least `q j`. Then `∑ j vol (E j) (β q j / c^n)^(1/(n-1))` is at most the Kakeya bound for
`θ(Λ)`. -/
theorem incidence_kakeya {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK n C)
    {α : Type*} [MeasurableSpace α] (θ : Measure α) [IsFiniteMeasure θ]
    (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin n)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) {B : ℝ} (hB : ∀ l, ‖a l‖ ≤ B) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (Λ : Set α) (hΛ : MeasurableSet Λ)
    {ι : Type*} (s : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin n)))
    (hEm : ∀ j ∈ s, MeasurableSet (E j)) (hEd : (s : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ s, E j ⊆ Metric.closedBall 0 R)
    (c : ℝ≥0) (hc : 0 < c)
    (hpush : ∀ j ∈ s, (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤ c • θ.restrict Λ)
    (htube : ∀ j ∈ s, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ x ∈ E j,
      x ∈ tube r (a ω.1) (e ω.1))
    (β : ℝ) (q : ι → ℝ≥0∞)
    (hsucc : ∀ j ∈ s, q j ≤ Measure.pi (fun _ : Fin n => inc)
      {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (ω i).1 k)|}) :
    ∑ j ∈ s, volume (E j) * (ENNReal.ofReal β * q j / (c : ℝ≥0∞) ^ n) ^
        ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ _i : Fin n, θ Λ ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  classical
  have hcn : ((c : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
  have hcn' : ((c : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hmain := sum_volume_mul_rpow_le hn hC0 hC (fun _ : Fin n => θ.restrict Λ)
    (fun _ => a) (fun _ => e) (fun _ => ha) (fun _ => he) (fun _ => he1) (fun _ => hB) hr R s E
    (fun j => ENNReal.ofReal β * q j / (c : ℝ≥0∞) ^ n) hEm hEd hER ?_
  · simpa [Measure.restrict_apply_univ] using hmain
  intro j hj x hx
  -- the trajectory measure of the incidences in the cell
  set Sj : Set (α × ℝ) := {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} with hSj
  have hSjm : MeasurableSet Sj := (measurable_fst hΛ).inter (hΦ (hEm j hj))
  set νj : Measure α := (inc.restrict Sj).map Prod.fst with hνj
  -- the set of good line tuples at `x`
  set G : Set (Fin n → α) := {l | β ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| ∧
    ∀ i, x ∈ tube r (a (l i)) (e (l i))} with hG
  have hdet : Measurable fun l : Fin n → α =>
      |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| := by
    have h1 : Measurable fun l : Fin n → α => (Matrix.of fun i k : Fin n => e (l i) k) := by
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro k
      have hk : Measurable fun v : EuclideanSpace ℝ (Fin n) => v k :=
        (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.measurable
      exact (hk.comp he).comp (measurable_pi_apply i)
    exact continuous_abs.measurable.comp ((Continuous.matrix_det continuous_id).measurable.comp h1)
  have hGm : MeasurableSet G := by
    have : G = {l : Fin n → α | β ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)|} ∩
        ⋂ i, (fun l : Fin n → α => l i) ⁻¹' {l | x ∈ tube r (a l) (e l)} := by
      ext l
      simp [hG]
    rw [this]
    exact (measurableSet_le measurable_const hdet).inter (MeasurableSet.iInter fun i =>
      (measurableSet_mem_tube r a e ha he he1 x).preimage (measurable_pi_apply i))
  set F : (Fin n → α × ℝ) → (Fin n → α) := fun ω i => (ω i).1 with hF
  have hFm : Measurable F := Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)
  -- successful incidence tuples land in good line tuples
  have hsub : {ω : Fin n → α × ℝ | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
      β ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (ω i).1 k)|} ⊆
      F ⁻¹' G ∩ Set.univ.pi (fun _ => Sj) := by
    intro ω hω
    refine ⟨⟨hω.2, fun i => htube j hj (ω i) (hω.1 i).1 (hω.1 i).2 x hx⟩, ?_⟩
    intro i _
    exact hω.1 i
  have hpi : Measure.pi (fun _ : Fin n => inc) (F ⁻¹' G ∩ Set.univ.pi (fun _ => Sj)) =
      Measure.pi (fun _ : Fin n => νj) G := by
    rw [← Measure.restrict_apply (hFm hGm), Measure.restrict_pi_pi, hνj,
      ← Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable), Measure.map_apply hFm hGm]
  have hle_pi : Measure.pi (fun _ : Fin n => νj) ≤
      ((c : ℝ≥0∞) ^ n) • Measure.pi (fun _ : Fin n => θ.restrict Λ) := by
    calc Measure.pi (fun _ : Fin n => νj) ≤ Measure.pi (fun _ : Fin n => c • θ.restrict Λ) :=
          pi_mono fun _ => hpush j hj
      _ = ((c : ℝ≥0∞) ^ n) • Measure.pi (fun _ : Fin n => θ.restrict Λ) := by
          rw [pi_smul, Fintype.card_fin]
  -- the tube sum integrand dominates `β` on good tuples
  have hint : ENNReal.ofReal β * Measure.pi (fun _ : Fin n => νj) G ≤
      ∫⁻ l, ENNReal.ofReal |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| *
        ∏ i, (tube r (a (l i)) (e (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(Measure.pi fun _ : Fin n => νj) := by
    rw [← lintegral_indicator_const hGm]
    apply lintegral_mono
    intro l
    by_cases hl : l ∈ G
    · rw [Set.indicator_of_mem hl]
      have hprod : ∏ i, (tube r (a (l i)) (e (l i))).indicator
          (fun _ => (1 : ℝ≥0∞)) x = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [Set.indicator_of_mem (hl.2 i)]
      show ENNReal.ofReal β ≤ ENNReal.ofReal |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| *
        ∏ i, (tube r (a (l i)) (e (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [hprod, mul_one]
      exact ENNReal.ofReal_le_ofReal hl.1
    · rw [Set.indicator_of_notMem hl]
      exact zero_le
  have hchain : ENNReal.ofReal β * q j ≤
      contTubeSum (fun _ : Fin n => θ.restrict Λ) (fun _ => a) (fun _ => e) r x * (c : ℝ≥0∞) ^ n := by
    calc ENNReal.ofReal β * q j
        ≤ ENNReal.ofReal β * Measure.pi (fun _ : Fin n => inc)
            (F ⁻¹' G ∩ Set.univ.pi (fun _ => Sj)) := by
          gcongr
          exact (hsucc j hj).trans (measure_mono hsub)
      _ = ENNReal.ofReal β * Measure.pi (fun _ : Fin n => νj) G := by rw [hpi]
      _ ≤ ∫⁻ l, ENNReal.ofReal |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| *
          ∏ i, (tube r (a (l i)) (e (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(Measure.pi fun _ : Fin n => νj) := hint
      _ ≤ ∫⁻ l, ENNReal.ofReal |Matrix.det (Matrix.of fun i k : Fin n => e (l i) k)| *
          ∏ i, (tube r (a (l i)) (e (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(((c : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => θ.restrict Λ) :=
          lintegral_mono' hle_pi le_rfl
      _ = contTubeSum (fun _ : Fin n => θ.restrict Λ) (fun _ => a) (fun _ => e) r x *
            (c : ℝ≥0∞) ^ n := by
          rw [lintegral_smul_measure, contTubeSum, smul_eq_mul, mul_comm]
  exact ENNReal.div_le_of_le_mul hchain

end

end Submission.Lib.K4ContinuousKakeya
