import Submission.Lib.K4ContinuousKakeya

set_option linter.unusedVariables false

/-!
# Bad physical cells carry little mass

The Kakeya contradiction of the paper's physical velocity graph (`a05:velocity-graph`): a fine
physical cell is *bad* when the lifted directions of its incidences span `n` dimensions, i.e.
its `n`-tuples of incidences have determinant at least `β` with probability at least `p₀`.
Inside each coarse cube, trajectories spending less than `τ₀` in the bad cells are discarded
(`measure_short_le`), cells losing more than a fraction `η` are discarded, the remaining long
trajectories have prior mass at most `K M / τ₀` (`measure_long_le`), and the bad incidence tuples
survive (`pi_le_retained_add`). The incidence form of multilinear Kakeya
(`Submission.Lib.K4ContinuousKakeya.incidence_kakeya`, real form `kakeya_real_of_incidence`)
and the power mean then contradict the support count `S₀` unless the bad mass is controlled by
the discarded mass: `cube_bad_mass_le` (one cube) and `bad_mass_le` (all cubes, each trajectory
spending positive time in at most `mc` cubes). The constants enter only through the explicit
inequality `hcontr`.
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Submission.Lib.K4ContinuousKakeya
open scoped ENNReal NNReal

noncomputable section

/-- The time duration of a trajectory in a set of incidences. -/
def duration {α : Type*} [MeasurableSpace α] (S : Set (α × ℝ)) (l : α) : ℝ≥0∞ :=
  volume {t : ℝ | (l, t) ∈ S}

lemma measurable_duration {α : Type*} [MeasurableSpace α] {S : Set (α × ℝ)}
    (hS : MeasurableSet S) : Measurable (duration S) :=
  measurable_measure_prodMk_left hS

lemma lintegral_duration {α : Type*} [MeasurableSpace α] (θ : Measure α) [SFinite θ]
    {S : Set (α × ℝ)} (hS : MeasurableSet S) :
    ∫⁻ l, duration S l ∂θ = θ.prod volume S :=
  (Measure.prod_apply hS).symm

/-- Long trajectories (duration at least `τ₀`) have prior mass at most `(θ × time)(S) / τ₀`. -/
lemma measure_long_le {α : Type*} [MeasurableSpace α] (θ : Measure α) [SFinite θ]
    {S : Set (α × ℝ)} (hS : MeasurableSet S) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) :
    θ {l | (τ₀ : ℝ≥0∞) ≤ duration S l} ≤ θ.prod volume S / τ₀ := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hτ₀.ne'))
    (Or.inl ENNReal.coe_ne_top), mul_comm]
  calc (τ₀ : ℝ≥0∞) * θ {l | (τ₀ : ℝ≥0∞) ≤ duration S l} ≤ ∫⁻ l, duration S l ∂θ :=
        mul_meas_ge_le_lintegral₀ (measurable_duration hS).aemeasurable _
    _ = θ.prod volume S := lintegral_duration θ hS

/-- Incidences on short trajectories (duration below `τ₀`) of an incidence measure dominated by
`K • (θ × time)|E₀` have mass at most `K τ₀ θ{duration > 0}`. -/
lemma measure_short_le {α : Type*} [MeasurableSpace α] (θ : Measure α) [SFinite θ]
    (inc : Measure (α × ℝ)) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) (K : ℝ≥0)
    (hle : inc ≤ K • (θ.prod volume).restrict E₀) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (τ₀ : ℝ≥0) :
    inc {ω | ω ∈ S ∧ duration (S ∩ E₀) ω.1 < τ₀} ≤
      K * τ₀ * θ {l | 0 < duration (S ∩ E₀) l} := by
  have hSE : MeasurableSet (S ∩ E₀) := hS.inter hE₀
  have hD := measurable_duration (α := α) hSE
  set A : Set (α × ℝ) := {ω | ω ∈ S ∧ duration (S ∩ E₀) ω.1 < τ₀} with hA
  have hAm : MeasurableSet A :=
    hS.inter (measurableSet_lt (hD.comp measurable_fst) measurable_const)
  calc inc A ≤ (K • (θ.prod volume).restrict E₀) A := hle A
    _ = K * θ.prod volume (A ∩ E₀) := by
        rw [Measure.smul_apply, Measure.restrict_apply hAm, ENNReal.smul_def, smul_eq_mul]
    _ = K * ∫⁻ l, volume (Prod.mk l ⁻¹' (A ∩ E₀)) ∂θ := by
        rw [Measure.prod_apply (hAm.inter hE₀)]
    _ ≤ K * ∫⁻ l, {l | 0 < duration (S ∩ E₀) l}.indicator (fun _ => (τ₀ : ℝ≥0∞)) l ∂θ := by
        gcongr with l
        by_cases hl : duration (S ∩ E₀) l < τ₀
        · by_cases hpos : 0 < duration (S ∩ E₀) l
          · rw [Set.indicator_of_mem (show l ∈ {l | 0 < duration (S ∩ E₀) l} from hpos)]
            refine le_trans (measure_mono ?_) hl.le
            intro t ht
            exact ⟨ht.1.1, ht.2⟩
          · have h0 : duration (S ∩ E₀) l = 0 := by simpa using hpos
            have : volume (Prod.mk l ⁻¹' (A ∩ E₀)) = 0 := by
              apply measure_mono_null _ h0
              intro t ht
              exact ⟨ht.1.1, ht.2⟩
            rw [this]; exact zero_le
        · have : Prod.mk l ⁻¹' (A ∩ E₀) = ∅ := by
            ext t
            simp only [Set.mem_preimage, Set.mem_inter_iff, hA, Set.mem_ofPred_eq,
              Set.mem_empty_iff_false, iff_false]
            intro h; exact hl h.1.2
          rw [this, measure_empty]; exact zero_le
    _ = K * τ₀ * θ {l | 0 < duration (S ∩ E₀) l} := by
        rw [lintegral_indicator_const (measurableSet_lt measurable_const hD), mul_assoc]

/-- Union bound for the retained part of a set of `n`-tuples of incidences in `X`: the tuples
having some entry outside `R` carry at most `n inc(X \ R) inc(X)^(n-1)`. -/
lemma pi_le_retained_add {β : Type*} [MeasurableSpace β] (inc : Measure β) [IsFiniteMeasure inc]
    {n : ℕ} {X R : Set β} (hX : MeasurableSet X) (hR : MeasurableSet R)
    (Succ : Set (Fin n → β)) (hSucc : Succ ⊆ {ω | ∀ i, ω i ∈ X}) :
    Measure.pi (fun _ : Fin n => inc) Succ ≤
      Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ R}) +
        n * (inc (X \ R) * inc X ^ (n - 1)) := by
  classical
  have hcover : Succ ⊆ (Succ ∩ {ω | ∀ i, ω i ∈ R}) ∪
      ⋃ i : Fin n, Set.univ.pi (fun j => if j = i then X \ R else X) := by
    intro ω hω
    by_cases hret : ∀ i, ω i ∈ R
    · exact Or.inl ⟨hω, hret⟩
    · right
      simp only [not_forall] at hret
      obtain ⟨i, hi⟩ := hret
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      intro j _
      by_cases hj : j = i
      · subst hj; simp only [ite_true]; exact ⟨hSucc hω j, hi⟩
      · simp only [hj, ite_false]; exact hSucc hω j
  have hbox : ∀ i : Fin n, Measure.pi (fun _ : Fin n => inc)
      (Set.univ.pi (fun j => if j = i then X \ R else X)) = inc (X \ R) * inc X ^ (n - 1) := by
    intro i
    rw [Measure.pi_pi]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    rw [Finset.prod_congr rfl (g := fun _ => inc X) (fun j hj => by
      simp [Finset.ne_of_mem_erase hj]), Finset.prod_const, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  calc Measure.pi (fun _ : Fin n => inc) Succ
      ≤ Measure.pi (fun _ : Fin n => inc) ((Succ ∩ {ω | ∀ i, ω i ∈ R}) ∪
          ⋃ i : Fin n, Set.univ.pi (fun j => if j = i then X \ R else X)) := measure_mono hcover
    _ ≤ Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ R}) +
          Measure.pi (fun _ : Fin n => inc)
            (⋃ i : Fin n, Set.univ.pi (fun j => if j = i then X \ R else X)) :=
        measure_union_le _ _
    _ ≤ Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ R}) +
          ∑ i : Fin n, Measure.pi (fun _ : Fin n => inc)
            (Set.univ.pi (fun j => if j = i then X \ R else X)) := by
        gcongr
        exact measure_iUnion_fintype_le _ _
    _ = Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ R}) +
          n * (inc (X \ R) * inc X ^ (n - 1)) := by
        simp only [hbox, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Real form of the per-cell Kakeya bound: from `incidence_kakeya` on the good cells. -/
lemma kakeya_real_of_incidence {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK n C)
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
    {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ) (v₀ : ℝ) (hv₀ : 0 ≤ v₀)
    (hvol : ∀ j ∈ s, ENNReal.ofReal v₀ ≤ volume (E j))
    (hsucc : ∀ j ∈ s, ENNReal.ofReal κ * inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} ^ n ≤
      Measure.pi (fun _ : Fin n => inc)
      {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (ω i).1 k)|}) :
    ∑ j ∈ s, v₀ * (β * κ * (inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).toReal ^ n / (c : ℝ) ^ n) ^
        ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      2 ^ n * C * r ^ n * ((θ Λ).toReal) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  set p : ℝ := (1 : ℝ) / ((n : ℝ) - 1) with hp_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by rw [hp_def]; apply div_pos one_pos; linarith
  have hk := incidence_kakeya hn hC0 hC θ inc Φ hΦ a e ha he he1 hB hr R Λ hΛ s E hEm hEd hER
    c hc hpush htube β (fun j => ENNReal.ofReal κ * inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} ^ n) hsucc
  have hRtop : ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ _i : Fin n, θ Λ ^ p ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.prod_ne_top
    intro i _
    exact ENNReal.rpow_ne_top_of_nonneg hp0.le (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hRtop hk
  have hcR : (0 : ℝ) < c := hc
  have hrhs : (ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ _i : Fin n, θ Λ ^ p).toReal =
      2 ^ n * C * r ^ n * ((θ Λ).toReal) ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_prod]
    congr 1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.toReal_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    rw [hp_def]; field_simp
  rw [hrhs] at hreal
  refine le_trans ?_ hreal
  rw [ENNReal.toReal_sum (fun j hj => ?_)]
  · apply Finset.sum_le_sum
    intro j hj
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    have hvj : v₀ ≤ (volume (E j)).toReal := by
      have hfin : volume (E j) ≠ ⊤ :=
        (measure_mono (hER j hj)).trans_lt measure_closedBall_lt_top |>.ne
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hvol j hj)
    have hbase : (ENNReal.ofReal β * (ENNReal.ofReal κ * inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} ^ n) /
        (c : ℝ≥0∞) ^ n).toReal =
        β * κ * (inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).toReal ^ n / (c : ℝ) ^ n := by
      rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ,
        ENNReal.toReal_ofReal hκ, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.coe_toReal]
      ring
    rw [hbase]
    gcongr
  · apply ENNReal.mul_ne_top
    · exact (measure_mono (hER j hj)).trans_lt measure_closedBall_lt_top |>.ne
    · apply ENNReal.rpow_ne_top_of_nonneg hp0.le
      apply ENNReal.div_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (measure_ne_top _ _)))
      · exact pow_ne_zero _ (by exact_mod_cast hc.ne')

/-- **Bad cells of one coarse cube carry little mass.** Inside one coarse cube, consider disjoint
fine cells `Ec c` (in a ball, with time sections at most `b` and volume at least `v₀`) whose
incidences are bad: their `n`-tuples have lifted-direction determinant at least `β` with
probability at least `p₀`. Attach to each trajectory one line (`a`, unit `e`) whose `r`-tube
contains every cell the trajectory meets, with directions within `δu` of the incidences'. If the
Kakeya constant inequality `hcontr` holds, then the cells' total mass is at most
`3/η` times the mass `K τ₀ θ{duration > 0}` of incidences on trajectories spending less than
`τ₀` there (paper `a05:velocity-graph`: long portions, fractional loss, Kakeya, power mean). -/
theorem cube_bad_mass_le {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK n C)
    {α : Type*} [MeasurableSpace α] (θ : Measure α) [IsFiniteMeasure θ]
    (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) (K : ℝ≥0)
    (hle : inc ≤ K • (θ.prod volume).restrict E₀) (hge : (θ.prod volume).restrict E₀ ≤ K • inc)
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    (u : α × ℝ → EuclideanSpace ℝ (Fin n)) (hu1 : ∀ ω, ‖u ω‖ ≤ 1)
    {ιC : Type*} (cells : Finset ιC) (Ec : ιC → Set (EuclideanSpace ℝ (Fin n)))
    (hEm : ∀ c, MeasurableSet (Ec c)) (hdisj : (cells : Set ιC).PairwiseDisjoint Ec)
    (R : ℝ) (hER : ∀ c ∈ cells, Ec c ⊆ Metric.closedBall 0 R)
    (b : ℝ≥0) (hb0 : 0 < b) (hb : ∀ c ∈ cells, ∀ l, volume {t : ℝ | Φ (l, t) ∈ Ec c} ≤ b)
    (a e : α → EuclideanSpace ℝ (Fin n)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) {B : ℝ} (hB : ∀ l, ‖a l‖ ≤ B) {r : ℝ} (hr : 0 < r)
    (htube : ∀ c ∈ cells, ∀ ω : α × ℝ, Φ ω ∈ Ec c → ∀ x ∈ Ec c, x ∈ tube r (a ω.1) (e ω.1))
    (δu : ℝ) (hdir : ∀ c ∈ cells, ∀ ω : α × ℝ, Φ ω ∈ Ec c → ‖u ω - e ω.1‖ ≤ δu)
    (S₀ : ℕ) (hS₀ : cells.card ≤ S₀) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvol : ∀ c ∈ cells, ENNReal.ofReal v₀ ≤ volume (Ec c))
    (β p₀ η : ℝ) (τ₀ : ℝ≥0) (hτ₀ : 0 < τ₀) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hp₀ : 2 * n * η ≤ p₀) (hK : 0 < K)
    (hβ' : 0 < β - n.factorial * n * δu)
    (hbad : ∀ c ∈ cells, ENNReal.ofReal p₀ * inc (Φ ⁻¹' Ec c) ^ n ≤
      Measure.pi (fun _ : Fin n => inc) {ω | (∀ i, Φ (ω i) ∈ Ec c) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin n => u (ω i) k)|})
    (hcontr : (S₀ : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
        (2 ^ n * C * r ^ n / v₀ * ((K * b : ℝ≥0) : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) /
          ((β - n.factorial * n * δu) * (p₀ - n * η)) ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
          ((K : ℝ) / τ₀) ^ ((n : ℝ) / ((n : ℝ) - 1))) ≤
        (1 / 2) ^ ((n : ℝ) / ((n : ℝ) - 1))) :
    ∑ c ∈ cells, (inc (Φ ⁻¹' Ec c)).toReal ≤
      3 / η * (K * τ₀ * (θ {l | 0 < duration (Φ ⁻¹' (⋃ c ∈ cells, Ec c) ∩ E₀) l}).toReal) := by
  classical
  set p : ℝ := (1 : ℝ) / ((n : ℝ) - 1) with hp_def
  set q : ℝ := (n : ℝ) / ((n : ℝ) - 1) with hq_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hp0 : 0 < p := div_pos one_pos hn1
  have hq0 : 0 < q := div_pos (by linarith) hn1
  have hq1 : 1 ≤ q := by rw [hq_def, le_div_iff₀ hn1]; linarith
  have hqp : q - 1 = p := by rw [hq_def, hp_def]; field_simp; ring
  have hqnp : (n : ℝ) * p = q := by rw [hq_def, hp_def]; field_simp
  set U : Set (EuclideanSpace ℝ (Fin n)) := ⋃ c ∈ cells, Ec c with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion cells (fun c _ => hEm c)
  set Sset : Set (α × ℝ) := Φ ⁻¹' U with hSset
  have hSm : MeasurableSet Sset := hΦ hUm
  set Λ : Set α := {l | (τ₀ : ℝ≥0∞) ≤ duration (Sset ∩ E₀) l} with hΛ
  have hΛm : MeasurableSet Λ :=
    measurableSet_le measurable_const (measurable_duration (hSm.inter hE₀))
  have hXm : ∀ c, MeasurableSet (Φ ⁻¹' Ec c) := fun c => hΦ (hEm c)
  have hRm : MeasurableSet (Prod.fst ⁻¹' Λ : Set (α × ℝ)) := measurable_fst hΛm
  -- real masses
  set m : ιC → ℝ := fun c => (inc (Φ ⁻¹' Ec c)).toReal with hm
  set m' : ιC → ℝ := fun c => (inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ Ec c}).toReal with hm'
  set loss : ιC → ℝ := fun c => (inc {ω | Φ ω ∈ Ec c ∧ ω.1 ∉ Λ}).toReal with hloss
  have hset1 : ∀ c, {ω : α × ℝ | ω.1 ∈ Λ ∧ Φ ω ∈ Ec c} = Φ ⁻¹' Ec c ∩ Prod.fst ⁻¹' Λ := by
    intro c; ext ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]; tauto
  have hset2 : ∀ c, {ω : α × ℝ | Φ ω ∈ Ec c ∧ ω.1 ∉ Λ} = Φ ⁻¹' Ec c \ Prod.fst ⁻¹' Λ := by
    intro c; ext ω; simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_preimage]
  have hsplit : ∀ c, m c = m' c + loss c := by
    intro c
    simp only [hm, hm', hloss, hset1, hset2]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_inter_add_sdiff _ hRm]
  have hm0 : ∀ c, 0 ≤ m c := fun c => ENNReal.toReal_nonneg
  have hm'0 : ∀ c, 0 ≤ m' c := fun c => ENNReal.toReal_nonneg
  have hloss0 : ∀ c, 0 ≤ loss c := fun c => ENNReal.toReal_nonneg
  set M : ℝ := ∑ c ∈ cells, m c with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun c _ => hm0 c
  -- the incidence mass of all the cells
  have hdisjX : (cells : Set ιC).PairwiseDisjoint (fun c => Φ ⁻¹' Ec c) := by
    intro c hc c' hc' hcc'
    exact (hdisj hc hc' hcc').preimage Φ
  have hincS : inc Sset = ∑ c ∈ cells, inc (Φ ⁻¹' Ec c) := by
    rw [hSset, hU, Set.preimage_iUnion₂]
    exact measure_biUnion_finset hdisjX (fun c _ => hXm c)
  have hincS_real : (inc Sset).toReal = M := by
    rw [hincS, ENNReal.toReal_sum (fun c _ => measure_ne_top _ _)]
  -- (1) the long trajectories
  have hΛmass : (θ Λ).toReal ≤ K * M / τ₀ := by
    have h1 := measure_long_le θ (hSm.inter hE₀) hτ₀
    have h2 : θ.prod volume (Sset ∩ E₀) ≤ K * inc Sset := by
      have := hge Sset
      rw [Measure.restrict_apply hSm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
      exact this
    have h3 : θ Λ ≤ K * inc Sset / τ₀ := h1.trans (ENNReal.div_le_div_right h2 _)
    have hfin : (K : ℝ≥0∞) * inc Sset / τ₀ ≠ ⊤ :=
      ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
        (by exact_mod_cast hτ₀.ne')
    have h4 := ENNReal.toReal_mono hfin h3
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
      hincS_real] at h4
    exact h4
  -- (2) the total loss
  set Lθ : ℝ := (θ {l | 0 < duration (Sset ∩ E₀) l}).toReal with hLθ
  have hlossTot : ∑ c ∈ cells, loss c ≤ K * τ₀ * Lθ := by
    have h1 := measure_short_le θ inc hE₀ K hle hSm τ₀
    have hset : {ω : α × ℝ | ω ∈ Sset ∧ duration (Sset ∩ E₀) ω.1 < τ₀} =
        ⋃ c ∈ cells, (Φ ⁻¹' Ec c \ Prod.fst ⁻¹' Λ) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_sdiff, Set.mem_preimage, hSset, hU,
        hΛ, not_le, exists_prop]
      constructor
      · rintro ⟨⟨c, hc, hω⟩, hlt⟩; exact ⟨c, hc, hω, hlt⟩
      · rintro ⟨c, hc, hω, hlt⟩; exact ⟨⟨c, hc, hω⟩, hlt⟩
    have hdisjD : (cells : Set ιC).PairwiseDisjoint (fun c => Φ ⁻¹' Ec c \ Prod.fst ⁻¹' Λ) := by
      intro c hc c' hc' hcc'
      exact (hdisjX hc hc' hcc').mono Set.sdiff_subset Set.sdiff_subset
    rw [hset, measure_biUnion_finset hdisjD (fun c _ => (hXm c).diff hRm)] at h1
    have hfin : (K : ℝ≥0∞) * τ₀ * θ {l | 0 < duration (Sset ∩ E₀) l} ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
        (measure_ne_top _ _)
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_sum (fun c _ => measure_ne_top _ _), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at h2
    simpa [hloss, hset2] using h2
  -- (3) good cells and their retained success
  set G := cells.filter (fun c => loss c ≤ η * m c) with hG
  set β' : ℝ := β - n.factorial * n * δu with hβ'_def
  set κ : ℝ := p₀ - n * η with hκ_def
  have hnη : 0 ≤ (n : ℝ) * η := by positivity
  have hκ0 : 0 ≤ κ := by rw [hκ_def]; nlinarith
  have hsucc : ∀ c ∈ G, ENNReal.ofReal κ * inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ Ec c} ^ n ≤
      Measure.pi (fun _ : Fin n => inc)
      {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ Ec c) ∧
        β' ≤ |Matrix.det (Matrix.of fun i k : Fin n => e (ω i).1 k)|} := by
    intro c hcG
    have hc : c ∈ cells := (Finset.mem_filter.mp hcG).1
    have hlc : loss c ≤ η * m c := (Finset.mem_filter.mp hcG).2
    set X : Set (α × ℝ) := Φ ⁻¹' Ec c with hX
    set Succ : Set (Fin n → α × ℝ) := {ω | (∀ i, Φ (ω i) ∈ Ec c) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin n => u (ω i) k)|} with hSucc
    have hret := pi_le_retained_add inc (hXm c) hRm Succ (fun ω hω => hω.1)
    have hlossE : inc (X \ Prod.fst ⁻¹' Λ) ≤ ENNReal.ofReal η * inc X := by
      have h1 : (inc (X \ Prod.fst ⁻¹' Λ)).toReal ≤ η * (inc X).toReal := by
        have := hlc; simp only [hloss, hm, hset2] at this; exact this
      rw [← ENNReal.ofReal_toReal (measure_ne_top inc (X \ Prod.fst ⁻¹' Λ)),
        ← ENNReal.ofReal_toReal (measure_ne_top inc X), ← ENNReal.ofReal_mul hη.le]
      exact ENNReal.ofReal_le_ofReal h1
    have hpow : (n : ℝ≥0∞) * (inc (X \ Prod.fst ⁻¹' Λ) * inc X ^ (n - 1)) ≤
        ENNReal.ofReal ((n : ℝ) * η) * inc X ^ n := by
      calc (n : ℝ≥0∞) * (inc (X \ Prod.fst ⁻¹' Λ) * inc X ^ (n - 1))
          ≤ (n : ℝ≥0∞) * (ENNReal.ofReal η * inc X * inc X ^ (n - 1)) := by gcongr
        _ = ENNReal.ofReal ((n : ℝ) * η) * inc X ^ n := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
          have hpowX : inc X * inc X ^ (n - 1) = inc X ^ n := by
            rw [← pow_succ']; congr 1; omega
          rw [← hpowX]
          ring
    have hsplitP : ENNReal.ofReal p₀ = ENNReal.ofReal κ + ENNReal.ofReal ((n : ℝ) * η) := by
      rw [← ENNReal.ofReal_add hκ0 hnη, hκ_def, sub_add_cancel]
    have hmain : ENNReal.ofReal κ * inc X ^ n + ENNReal.ofReal ((n : ℝ) * η) * inc X ^ n ≤
        Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ Prod.fst ⁻¹' Λ}) +
          ENNReal.ofReal ((n : ℝ) * η) * inc X ^ n := by
      rw [← add_mul, ← hsplitP]
      exact (hbad c hc).trans (hret.trans (add_le_add_right hpow _))
    have hcancel := ENNReal.le_of_add_le_add_right
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (measure_ne_top _ _))) hmain
    calc ENNReal.ofReal κ * inc {ω | ω.1 ∈ Λ ∧ Φ ω ∈ Ec c} ^ n
        ≤ ENNReal.ofReal κ * inc X ^ n := by
          gcongr
          intro ω hω; exact hω.2
      _ ≤ Measure.pi (fun _ : Fin n => inc) (Succ ∩ {ω | ∀ i, ω i ∈ Prod.fst ⁻¹' Λ}) := hcancel
      _ ≤ _ := by
          apply measure_mono
          rintro ω ⟨⟨hωX, hdet⟩, hωR⟩
          refine ⟨fun i => ⟨hωR i, hωX i⟩, ?_⟩
          have hd := abs_det_sub_le (fun i => u (ω i)) (fun i => e (ω i).1) δu
            (fun i => hu1 _) (fun i => (he1 _).le) (fun i => hdir c hc (ω i) (hωX i))
          have h2 := abs_sub_abs_le_abs_sub
            (Matrix.det (Matrix.of fun i k : Fin n => u (ω i) k))
            (Matrix.det (Matrix.of fun i k : Fin n => e (ω i).1 k))
          rw [hβ'_def]
          linarith
  -- (4) multilinear Kakeya on the good cells
  have hGsub : G ⊆ cells := Finset.filter_subset _ _
  have hinc : inc ≤ K • θ.prod volume := by
    rw [Measure.le_iff']
    intro A
    refine (hle A).trans ?_
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    gcongr
    exact Measure.restrict_le_self
  have hpush : ∀ j ∈ G, (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ Ec j}).map Prod.fst ≤
      (K * b) • θ.restrict Λ := by
    intro j hj
    apply map_fst_restrict_le θ inc K b hinc _ (hRm.inter (hXm j) |>.congr (by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]; try tauto)) Λ hΛm
      (fun ω hω => hω.1)
    intro l _
    refine le_trans (measure_mono ?_) (hb j (hGsub hj) l)
    intro t ht; exact ht.2
  have hβ'0 : 0 ≤ β' := hβ'.le
  have hKb : (0 : ℝ≥0) < K * b := mul_pos hK hb0
  have hkak := kakeya_real_of_incidence hn hC0 hC θ inc Φ hΦ a e ha he he1 hB hr R Λ hΛm G Ec
    (fun j _ => hEm j) (hdisj.subset (by exact_mod_cast hGsub)) (fun j hj => hER j (hGsub hj))
    (K * b) hKb hpush (fun j hj ω _ hωE x hx => htube j (hGsub hj) ω hωE x hx) hβ'0 hκ0 v₀
    hv₀.le (fun j hj => hvol j (hGsub hj)) hsucc
  -- (5) algebra: the good retained masses obey a power-mean bound
  have hKbR : (0 : ℝ) < ((K * b : ℝ≥0) : ℝ) := by exact_mod_cast hKb
  have hβκ : 0 < β' * κ := by
    have : 0 < κ := by rw [hκ_def]; nlinarith
    positivity
  have hterm : ∀ j ∈ G, v₀ * (β' * κ * m' j ^ n / ((K * b : ℝ≥0) : ℝ) ^ n) ^ p =
      v₀ * (β' * κ) ^ p / ((K * b : ℝ≥0) : ℝ) ^ q * m' j ^ q := by
    intro j _
    have hm'j := hm'0 j
    rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hβκ.le (by positivity),
      ← Real.rpow_natCast_mul hm'j, ← Real.rpow_natCast_mul hKbR.le, hqnp]
    ring
  set A : ℝ := 2 ^ n * C * r ^ n / v₀ * ((K * b : ℝ≥0) : ℝ) ^ q / (β' * κ) ^ p *
    ((K : ℝ) / τ₀) ^ q with hA
  have hθΛ : ((θ Λ).toReal) ^ q ≤ ((K : ℝ) / τ₀) ^ q * M ^ q := by
    rw [← Real.mul_rpow (by positivity) hM0]
    apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ hq0.le
    calc (θ Λ).toReal ≤ K * M / τ₀ := hΛmass
      _ = (K : ℝ) / τ₀ * M := by ring
  have hsumq : ∑ j ∈ G, m' j ^ q ≤ A * M ^ q := by
    have h1 : v₀ * (β' * κ) ^ p / ((K * b : ℝ≥0) : ℝ) ^ q * ∑ j ∈ G, m' j ^ q ≤
        2 ^ n * C * r ^ n * (((K : ℝ) / τ₀) ^ q * M ^ q) := by
      rw [Finset.mul_sum, ← Finset.sum_congr rfl hterm]
      refine hkak.trans ?_
      gcongr
    have hpos : 0 < v₀ * (β' * κ) ^ p / ((K * b : ℝ≥0) : ℝ) ^ q := by positivity
    rw [hA]
    have h2 := (le_div_iff₀' hpos).mpr h1
    calc ∑ j ∈ G, m' j ^ q ≤ 2 ^ n * C * r ^ n * (((K : ℝ) / τ₀) ^ q * M ^ q) /
          (v₀ * (β' * κ) ^ p / ((K * b : ℝ≥0) : ℝ) ^ q) := h2
      _ = 2 ^ n * C * r ^ n / v₀ * ((K * b : ℝ≥0) : ℝ) ^ q / (β' * κ) ^ p *
          ((K : ℝ) / τ₀) ^ q * M ^ q := by
          field_simp
  have hGcard : ((G.card : ℕ) : ℝ) ^ (q - 1) ≤ (S₀ : ℝ) ^ p := by
    rw [hqp]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hp0.le
    exact_mod_cast (Finset.card_le_card hGsub).trans hS₀
  have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := G) (f := m') hq1
    (fun j _ => hm'0 j)
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ 2 ^ n * C * r ^ n := by positivity
    positivity
  have hhalf : (∑ j ∈ G, m' j) ^ q ≤ (M / 2) ^ q := by
    calc (∑ j ∈ G, m' j) ^ q ≤ ((G.card : ℕ) : ℝ) ^ (q - 1) * ∑ j ∈ G, m' j ^ q := hpm
      _ ≤ (S₀ : ℝ) ^ p * (A * M ^ q) := by
          gcongr
      _ = ((S₀ : ℝ) ^ p * A) * M ^ q := by ring
      _ ≤ (1 / 2) ^ q * M ^ q := by
          gcongr
      _ = (M / 2) ^ q := by
          rw [← Real.mul_rpow (by norm_num) hM0]; ring_nf
  have hGhalf : ∑ j ∈ G, m' j ≤ M / 2 :=
    (Real.rpow_le_rpow_iff (Finset.sum_nonneg fun j _ => hm'0 j) (by positivity) hq0).mp hhalf
  -- (6) conclusion
  have hgood : ∀ c ∈ G, (1 - η) * m c ≤ m' c := by
    intro c hc
    have hlc := (Finset.mem_filter.mp hc).2
    have h1 := hsplit c
    have h2 : (1 - η) * m c = m c - η * m c := by ring
    linarith
  have hbadc : ∀ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), m c ≤ loss c / η := by
    intro c hc
    have hlc := (Finset.mem_filter.mp hc).2
    rw [le_div_iff₀ hη]
    have hlc' := not_le.mp hlc
    linarith
  have hsplitM : M = ∑ c ∈ G, m c + ∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), m c :=
    (Finset.sum_filter_add_sum_filter_not cells _ m).symm
  have hG1 : (1 - η) * ∑ c ∈ G, m c ≤ M / 2 := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum hgood).trans hGhalf
  have hG2 : ∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), m c ≤ (K * τ₀ * Lθ) / η := by
    calc ∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), m c
        ≤ ∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), loss c / η := Finset.sum_le_sum hbadc
      _ = (∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), loss c) / η := by
          rw [Finset.sum_div]
      _ ≤ (∑ c ∈ cells, loss c) / η := by
          gcongr
          exact Finset.filter_subset (fun c => ¬ loss c ≤ η * m c) cells
      _ ≤ (K * τ₀ * Lθ) / η := by gcongr
  have hGsum0 : 0 ≤ ∑ c ∈ G, m c := Finset.sum_nonneg fun c _ => hm0 c
  have hfinal : M ≤ 3 / η * (K * τ₀ * Lθ) := by
    have h34 : (3 / 4) * ∑ c ∈ G, m c ≤ (1 - η) * ∑ c ∈ G, m c :=
      mul_le_mul_of_nonneg_right (by linarith) hGsum0
    have hGle : ∑ c ∈ G, m c ≤ 2 / 3 * M := by linarith only [h34, hG1, hM0]
    set Y : ℝ := K * τ₀ * Lθ / η with hY
    have hG2' : ∑ c ∈ cells.filter (fun c => ¬ loss c ≤ η * m c), m c ≤ Y := hG2
    have h4 : M ≤ 2 / 3 * M + Y := by linarith only [hsplitM, hGle, hG2']
    have h5 : 3 / η * (K * τ₀ * Lθ) = 3 * Y := by rw [hY]; ring
    rw [h5]
    linarith only [h4]
  exact hfinal

/-- **Bad cells carry little mass (all coarse cubes).** Summing `cube_bad_mass_le` over coarse
cubes `Q` of a family in which each trajectory spends positive time in at most `mc` cubes, the
bad cells carry at most `3/η · K τ₀ mc θ(univ)`. -/
theorem bad_mass_le {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK n C)
    {α : Type*} [MeasurableSpace α] (θ : Measure α) [IsFiniteMeasure θ]
    (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) (K : ℝ≥0)
    (hle : inc ≤ K • (θ.prod volume).restrict E₀) (hge : (θ.prod volume).restrict E₀ ≤ K • inc)
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin n)) (hΦ : Measurable Φ)
    (u : α × ℝ → EuclideanSpace ℝ (Fin n)) (hu1 : ∀ ω, ‖u ω‖ ≤ 1)
    {ιQ ιC : Type*} (𝒬 : Finset ιQ) (cells : ιQ → Finset ιC)
    (Ec : ιC → Set (EuclideanSpace ℝ (Fin n)))
    (hEm : ∀ c, MeasurableSet (Ec c)) (hdisj : ∀ Q ∈ 𝒬, (cells Q : Set ιC).PairwiseDisjoint Ec)
    (R : ℝ) (hER : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, Ec c ⊆ Metric.closedBall 0 R)
    (b : ℝ≥0) (hb0 : 0 < b)
    (hb : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, ∀ l, volume {t : ℝ | Φ (l, t) ∈ Ec c} ≤ b)
    (a e : ιQ → α → EuclideanSpace ℝ (Fin n)) (ha : ∀ Q, Measurable (a Q))
    (he : ∀ Q, Measurable (e Q)) (he1 : ∀ Q l, ‖e Q l‖ = 1) {B : ℝ} (hB : ∀ Q l, ‖a Q l‖ ≤ B)
    {r : ℝ} (hr : 0 < r)
    (htube : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, ∀ ω : α × ℝ, Φ ω ∈ Ec c → ∀ x ∈ Ec c,
      x ∈ tube r (a Q ω.1) (e Q ω.1))
    (δu : ℝ) (hdir : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, ∀ ω : α × ℝ, Φ ω ∈ Ec c → ‖u ω - e Q ω.1‖ ≤ δu)
    (S₀ : ℕ) (hS₀ : ∀ Q ∈ 𝒬, (cells Q).card ≤ S₀) (v₀ : ℝ) (hv₀ : 0 < v₀)
    (hvol : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, ENNReal.ofReal v₀ ≤ volume (Ec c))
    (β p₀ η : ℝ) (τ₀ : ℝ≥0) (hτ₀ : 0 < τ₀) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hp₀ : 2 * n * η ≤ p₀) (hK : 0 < K)
    (hβ' : 0 < β - n.factorial * n * δu)
    (hbad : ∀ Q ∈ 𝒬, ∀ c ∈ cells Q, ENNReal.ofReal p₀ * inc (Φ ⁻¹' Ec c) ^ n ≤
      Measure.pi (fun _ : Fin n => inc) {ω | (∀ i, Φ (ω i) ∈ Ec c) ∧
        β ≤ |Matrix.det (Matrix.of fun i k : Fin n => u (ω i) k)|})
    (hcontr : (S₀ : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
        (2 ^ n * C * r ^ n / v₀ * ((K * b : ℝ≥0) : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) /
          ((β - n.factorial * n * δu) * (p₀ - n * η)) ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
          ((K : ℝ) / τ₀) ^ ((n : ℝ) / ((n : ℝ) - 1))) ≤
        (1 / 2) ^ ((n : ℝ) / ((n : ℝ) - 1)))
    (mc : ℕ) (hmc : ∀ l, (𝒬.filter fun Q =>
      0 < duration (Φ ⁻¹' (⋃ c ∈ cells Q, Ec c) ∩ E₀) l).card ≤ mc) :
    ∑ Q ∈ 𝒬, ∑ c ∈ cells Q, (inc (Φ ⁻¹' Ec c)).toReal ≤
      3 / η * (K * τ₀ * (mc * (θ Set.univ).toReal)) := by
  classical
  have hcube : ∀ Q ∈ 𝒬, ∑ c ∈ cells Q, (inc (Φ ⁻¹' Ec c)).toReal ≤
      3 / η * (K * τ₀ * (θ {l | 0 < duration (Φ ⁻¹' (⋃ c ∈ cells Q, Ec c) ∩ E₀) l}).toReal) :=
    fun Q hQ => cube_bad_mass_le hn hC0 hC θ inc hE₀ K hle hge Φ hΦ u hu1 (cells Q) Ec hEm
      (hdisj Q hQ) R (hER Q hQ) b hb0 (hb Q hQ) (a Q) (e Q) (ha Q) (he Q) (he1 Q) (hB Q) hr
      (htube Q hQ) δu (hdir Q hQ) S₀ (hS₀ Q hQ) v₀ hv₀ (hvol Q hQ) β p₀ η τ₀ hτ₀ hη hη4 hp₀ hK
      hβ' (hbad Q hQ) hcontr
  set A : ιQ → Set α := fun Q => {l | 0 < duration (Φ ⁻¹' (⋃ c ∈ cells Q, Ec c) ∩ E₀) l}
    with hA
  have hAm : ∀ Q, MeasurableSet (A Q) := fun Q =>
    measurableSet_lt measurable_const (measurable_duration
      ((hΦ (Finset.measurableSet_biUnion _ (fun c _ => hEm c))).inter hE₀))
  have hsumA : ∑ Q ∈ 𝒬, θ (A Q) ≤ mc * θ Set.univ := by
    calc ∑ Q ∈ 𝒬, θ (A Q) = ∑ Q ∈ 𝒬, ∫⁻ l, (A Q).indicator (fun _ => (1 : ℝ≥0∞)) l ∂θ := by
          apply Finset.sum_congr rfl; intro Q _
          rw [lintegral_indicator_const (hAm Q), one_mul]
      _ = ∫⁻ l, ∑ Q ∈ 𝒬, (A Q).indicator (fun _ => (1 : ℝ≥0∞)) l ∂θ :=
          (lintegral_finsetSum _ fun Q _ => measurable_const.indicator (hAm Q)).symm
      _ ≤ ∫⁻ _l, (mc : ℝ≥0∞) ∂θ := by
          apply lintegral_mono
          intro l
          have h1 : ∑ Q ∈ 𝒬, (A Q).indicator (fun _ => (1 : ℝ≥0∞)) l =
              ((𝒬.filter fun Q => l ∈ A Q).card : ℝ≥0∞) := by
            simp only [Set.indicator_apply]
            rw [Finset.sum_boole]
          show ∑ Q ∈ 𝒬, (A Q).indicator (fun _ => (1 : ℝ≥0∞)) l ≤ (mc : ℝ≥0∞)
          rw [h1]
          exact_mod_cast hmc l
      _ = mc * θ Set.univ := by rw [lintegral_const]
  have hsumA_real : ∑ Q ∈ 𝒬, (θ (A Q)).toReal ≤ mc * (θ Set.univ).toReal := by
    have hfin : (mc : ℝ≥0∞) * θ Set.univ ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top mc) (measure_ne_top _ _)
    have := ENNReal.toReal_mono hfin hsumA
    rwa [ENNReal.toReal_sum (fun Q _ => measure_ne_top _ _), ENNReal.toReal_mul,
      ENNReal.toReal_natCast] at this
  calc ∑ Q ∈ 𝒬, ∑ c ∈ cells Q, (inc (Φ ⁻¹' Ec c)).toReal
      ≤ ∑ Q ∈ 𝒬, 3 / η * (K * τ₀ * (θ (A Q)).toReal) := Finset.sum_le_sum hcube
    _ = 3 / η * (K * τ₀ * ∑ Q ∈ 𝒬, (θ (A Q)).toReal) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 3 / η * (K * τ₀ * (mc * (θ Set.univ).toReal)) := by
        gcongr

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
