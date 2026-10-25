import Submission.Obl.k4_scalar_coefficient_clustering.Grid
import Submission.Obl.k4_scalar_coefficient_clustering.Measure

namespace Submission.Obl.k4_scalar_coefficient_clustering

open MeasureTheory Set

noncomputable section

theorem measurable_coefficientCode (p : ℝ) : Measurable (coefficientCode p) := by
  apply Measurable.of_eval
  intro j
  exact (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable).div_const p).floor

theorem coefficient_dist_of_code_eq {p : ℝ} (hp : 0 < p) {a b : Coeff}
    (h : coefficientCode p a = coefficientCode p b) : ‖a - b‖ ≤ 3 * p := by
  have hcoord : ∀ j, |a j - b j| ≤ p := by
    intro j
    have hh := (Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h j)).le
    rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp] at hh
    simpa using hh
  exact (coeff_norm_le_abs_add (a - b)).trans (by
    simp only [PiLp.sub_apply]
    linarith [hcoord 0, hcoord 1, hcoord 2])

theorem coefficient_codes_finite {α : Type*} (a : α → Coeff) (G : Set α)
    {p B : ℝ} (hp : 0 < p) (ha : ∀ l ∈ G, ‖a l‖ ≤ B) :
    ((coefficientCode p ∘ a) '' G).Finite := by
  classical
  let M : ℤ := ⌈|B| / p⌉ + 2
  apply (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-M) M)).finite_toSet.subset
  rintro q ⟨l, hl, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  have hc : |a l j| ≤ |B| := ((PiLp.norm_apply_le (a l) j).trans (ha l hl)).trans (le_abs_self B)
  have hc' : |a l j / p| ≤ |B| / p := by
    rw [abs_div, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hc hp.le
  have hM : |B| / p ≤ (⌈|B| / p⌉ : ℝ) := Int.le_ceil _
  have hlo := Int.sub_one_lt_floor (a l j / p)
  have hhi := Int.floor_le (a l j / p)
  have hh := abs_le.mp hc'
  have hmcast : (M : ℝ) = (⌈|B| / p⌉ : ℝ) + 2 := by simp [M]
  have hlo' : (-M : ℝ) ≤ (⌊a l j / p⌋ : ℝ) := by push_cast; linarith
  have hhi' : (⌊a l j / p⌋ : ℝ) ≤ (M : ℝ) := by linarith
  exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo', by exact_mod_cast hhi'⟩

theorem measure_sum_coefficient_bins {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {a : α → Coeff} (ha : Measurable a) {G : Set α}
    (hG : MeasurableSet G) (p : ℝ) (Q : Finset (Fin 3 → ℤ)) :
    (∑ q ∈ Q, ν {l | l ∈ G ∧ coefficientCode p (a l) = q}) =
      ν {l | l ∈ G ∧ coefficientCode p (a l) ∈ Q} := by
  classical
  have hm : ∀ q, MeasurableSet {l | l ∈ G ∧ coefficientCode p (a l) = q} := by
    intro q
    exact hG.inter (((measurable_coefficientCode p).comp ha) (measurableSet_singleton q))
  have hd : (↑Q : Set (Fin 3 → ℤ)).PairwiseDisjoint
      (fun q => {l | l ∈ G ∧ coefficientCode p (a l) = q}) := by
    intro q hq r hr hqr
    apply Set.disjoint_left.mpr
    intro l hl hl'
    exact hqr (hl.2.symm.trans hl'.2)
  rw [← measure_biUnion_finset hd (fun q _ => hm q)]
  congr 1
  ext l
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  aesop

/-- Discretize a finite prior without discarding its auxiliary trajectory labels. -/
theorem exists_binned_prior {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {a : α → Coeff} (ha : Measurable a) {G : Set α}
    (hG : MeasurableSet G) {p B : ℝ} (hp : 0 < p)
    (hB : ∀ l ∈ G, ‖a l‖ ≤ B) :
    ∃ (n : ℕ) (rep : Fin n → α) (ω : Fin n → ℝ),
      (∀ i, rep i ∈ G) ∧
      Function.Injective (fun i => coefficientCode p (a (rep i))) ∧
      (∀ i, 0 < ω i) ∧
      (∀ i, ω i = (ν {l | l ∈ G ∧ coefficientCode p (a l) =
        coefficientCode p (a (rep i))}).toReal) ∧
      (∑ i, ω i) = (ν G).toReal := by
  classical
  let m : (Fin 3 → ℤ) → ENNReal := fun q => ν {l | l ∈ G ∧ coefficientCode p (a l) = q}
  let Q₀ := (coefficient_codes_finite a G hp hB).toFinset
  let Q := Q₀.filter fun q => m q ≠ 0
  have hrep : ∀ q : Q, ∃ l, l ∈ G ∧ coefficientCode p (a l) = q := by
    intro q
    exact nonempty_of_measure_ne_zero (Finset.mem_filter.mp q.property).2
  choose r hr using hrep
  let e : Q ≃ Fin Q.card := (Finset.equivFin Q)
  let rep : Fin Q.card → α := fun i => r (e.symm i)
  let ω : Fin Q.card → ℝ := fun i => (m (e.symm i)).toReal
  refine ⟨Q.card, rep, ω, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hr (e.symm i)).1
  · intro i j hij
    have heq : (e.symm i).val = (e.symm j).val :=
      (hr (e.symm i)).2.symm.trans (hij.trans (hr (e.symm j)).2)
    exact e.symm.injective (Subtype.ext heq)
  · intro i
    apply ENNReal.toReal_pos
    · exact (Finset.mem_filter.mp (e.symm i).property).2
    · exact measure_ne_top _ _
  · intro i
    dsimp only [ω, rep, m]
    rw [(hr (e.symm i)).2]
  · have hmfinite : ∀ q ∈ Q, m q ≠ ⊤ := fun _ _ => measure_ne_top _ _
    have hfilter : (∑ q ∈ Q, m q) = ∑ q ∈ Q₀, m q := by
      change (∑ q ∈ Q₀.filter (fun q => m q ≠ 0), m q) = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs with h
      · rfl
      · simp_all
    have hfull : {l | l ∈ G ∧ coefficientCode p (a l) ∈ Q₀} = G := by
      ext l
      constructor
      · exact fun h => h.1
      · intro hl
        refine ⟨hl, ?_⟩
        simpa only [Q₀, Set.Finite.mem_toFinset] using
          (show coefficientCode p (a l) ∈ (coefficientCode p ∘ a) '' G from ⟨l, hl, rfl⟩)
    calc
      (∑ i, ω i) = ∑ q : Q, (m q).toReal := e.symm.sum_comp (fun q => (m q).toReal)
      _ = ∑ q ∈ Q, (m q).toReal := by
        change (∑ q ∈ Q.attach, (m q.val).toReal) = _
        exact Finset.sum_attach Q (fun q => (m q).toReal)
      _ = (∑ q ∈ Q, m q).toReal := (ENNReal.toReal_sum hmfinite).symm
      _ = (∑ q ∈ Q₀, m q).toReal := congrArg ENNReal.toReal hfilter
      _ = (ν G).toReal := by
        rw [measure_sum_coefficient_bins ν ha hG p Q₀, hfull]

theorem sum_binned_weights {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {a : α → Coeff} (ha : Measurable a) {G : Set α}
    (hG : MeasurableSet G) (p : ℝ) {n : ℕ} (rep : Fin n → α) (ω : Fin n → ℝ)
    (hinj : Function.Injective (fun i => coefficientCode p (a (rep i))))
    (hω : ∀ i, ω i = (ν {l | l ∈ G ∧ coefficientCode p (a l) =
      coefficientCode p (a (rep i))}).toReal) (S : Finset (Fin n)) :
    (∑ i ∈ S, ω i) =
      (ν {l | l ∈ G ∧ coefficientCode p (a l) ∈
        S.image (fun i => coefficientCode p (a (rep i)))}).toReal := by
  classical
  let m : (Fin 3 → ℤ) → ENNReal := fun q => ν {l | l ∈ G ∧ coefficientCode p (a l) = q}
  calc
    (∑ i ∈ S, ω i) = ∑ i ∈ S, (m (coefficientCode p (a (rep i)))).toReal := by
      exact Finset.sum_congr rfl (fun i _ => hω i)
    _ = ∑ q ∈ S.image (fun i => coefficientCode p (a (rep i))), (m q).toReal := by
      rw [Finset.sum_image hinj.injOn]
    _ = (∑ q ∈ S.image (fun i => coefficientCode p (a (rep i))), m q).toReal := by
      exact (ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)).symm
    _ = _ := by rw [measure_sum_coefficient_bins ν ha hG]

theorem binned_ball_cap {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] {a : α → Coeff} (ha : Measurable a) {G : Set α}
    (hG : MeasurableSet G) {p K d v : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hv : p ≤ 2 * v) {n : ℕ} (rep : Fin n → α) (ω : Fin n → ℝ)
    (hinj : Function.Injective (fun i => coefficientCode p (a (rep i))))
    (hω : ∀ i, ω i = (ν {l | l ∈ G ∧ coefficientCode p (a l) =
      coefficientCode p (a (rep i))}).toReal)
    (hcap : ∀ b r, p ≤ r → ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (K * r ^ d))
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, ∀ j ∈ S, ‖a (rep i) - a (rep j)‖ ≤ 24 * v) :
    (∑ i ∈ S, ω i) ≤ K * (32 * v) ^ d := by
  classical
  have hv0 : 0 < v := by linarith
  rw [sum_binned_weights ν ha hG p rep ω hinj hω S]
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp only [Finset.image_empty, Finset.notMem_empty, and_false, Set.setOf_false,
      measure_empty, ENNReal.toReal_zero]
    positivity
  have hsub : {l | l ∈ G ∧ coefficientCode p (a l) ∈
      S.image (fun i => coefficientCode p (a (rep i)))} ⊆
      {l | a l ∈ Metric.ball (a (rep i₀)) (32 * v)} := by
    rintro l ⟨hl, hq⟩
    rcases Finset.mem_image.mp hq with ⟨i, hi, heq⟩
    have hd := coefficient_dist_of_code_eq hp heq.symm
    have ht := dist_triangle (a l) (a (rep i)) (a (rep i₀))
    simp only [dist_eq_norm] at ht
    have hc := hS i hi i₀ hi₀
    change dist (a l) (a (rep i₀)) < 32 * v
    rw [dist_eq_norm]
    linarith
  have hh := (measure_mono hsub).trans (hcap (a (rep i₀)) (32 * v) (by linarith))
  have htt := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (by positivity)] at htt
  exact htt

end
end Submission.Obl.k4_scalar_coefficient_clustering
