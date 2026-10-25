import Submission.Obl.k4_dk4_smoothed_problem.Spread.BoxSlice

/-!
# The finite-scale spread estimate (box-density estimate)

For the smoothed prior of a finite line family (uniform boxes of radius `r` around each
line's intercept and slope), the `(prior ⊗ dt)`-mass of the incidences whose base point
`(t, y(t))` lies in a set `U ⊆ ℝ³` is bounded by a low-multiplicity term
`T (2r)⁻² vol U / n` plus the high-multiplicity time mass
`(1/n) Σ_i |{t ∈ [0,1] : mult_i(t) ≥ T}|`, where `mult_i(t)` counts the lines whose planar
position at time `t` is within `δ ≥ 4r` of that of line `i` in both coordinates.
All proofs here are original Mathlib proofs.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_dk4_smoothed_problem.Spread

open Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

/-- Lift of a base set `U ⊆ ℝ³` (time coordinate first) to `ℝ × ℝ²`. -/
def baseLift (U : Set (EuclideanSpace ℝ (Fin 3))) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | (WithLp.toLp 2 (Fin.cons p.1 p.2 : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3)) ∈ U}

theorem measurePreserving_baseMap :
    MeasurePreserving (fun p : ℝ × (Fin 2 → ℝ) =>
      (WithLp.toLp 2 (Fin.cons p.1 p.2 : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3)))
      volume volume := by
  have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0).symm
  have h2 := PiLp.volume_preserving_toLp (Fin 3)
  have h := h2.comp h1
  convert h using 1
  funext p
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply]
  congr 1
  ext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem measurable_baseMap :
    Measurable (fun p : ℝ × (Fin 2 → ℝ) =>
      (WithLp.toLp 2 (Fin.cons p.1 p.2 : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3))) :=
  measurePreserving_baseMap.measurable

theorem measurableSet_baseLift {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : MeasurableSet U) :
    MeasurableSet (baseLift U) :=
  hU.preimage measurable_baseMap

theorem volume_baseLift {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : MeasurableSet U) :
    volume (baseLift U) = volume U :=
  measurePreserving_baseMap.measure_preimage hU.nullMeasurableSet

/-- The time-`t` multiplicity of line `i` at radius `δ`: the number of lines whose planar
position at time `t` is within `δ` of that of line `i` in both planar coordinates. -/
noncomputable def mult {n : ℕ} (b s : Fin n → Fin 3 → ℝ) (δ : ℝ) (i : Fin n) (t : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun j =>
    |(b j 0 + t * s j 0) - (b i 0 + t * s i 0)| ≤ δ ∧
      |(b j 1 + t * s j 1) - (b i 1 + t * s i 1)| ≤ δ)).card

theorem measurable_mult {n : ℕ} (b s : Fin n → Fin 3 → ℝ) (δ : ℝ) (i : Fin n) :
    Measurable (fun t => (mult b s δ i t : ℝ)) := by
  classical
  have h : (fun t => (mult b s δ i t : ℝ)) = fun t => ∑ j : Fin n,
      (if |(b j 0 + t * s j 0) - (b i 0 + t * s i 0)| ≤ δ ∧
        |(b j 1 + t * s j 1) - (b i 1 + t * s i 1)| ≤ δ then (1 : ℝ) else 0) := by
    funext t
    simp only [mult, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
  rw [h]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (f := fun t => |(b j 0 + t * s j 0) - (b i 0 + t * s i 0)|)
      (by fun_prop) measurable_const
  · exact measurableSet_le (f := fun t => |(b j 1 + t * s j 1) - (b i 1 + t * s i 1)|)
      (by fun_prop) measurable_const

/-- The spread event of a base set `U`, on the pair coefficient space. -/
def pairSpread (U : Set (EuclideanSpace ℝ (Fin 3))) :
    Set (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ) :=
  {q | q.2 ∈ Icc (0 : ℝ) 1 ∧
    (WithLp.toLp 2 ![q.2, q.1.1 0 + q.2 * q.1.2 0, q.1.1 1 + q.2 * q.1.2 1] :
      EuclideanSpace ℝ (Fin 3)) ∈ U}

theorem pairSpread_eq (U : Set (EuclideanSpace ℝ (Fin 3))) :
    pairSpread U = {q | q.2 ∈ Icc (0 : ℝ) 1 ∧ (q.2, planarPos q.1.1 q.1.2 q.2) ∈ baseLift U} := by
  rfl

theorem pairSpread_mono {U U' : Set (EuclideanSpace ℝ (Fin 3))} (h : U ⊆ U') :
    pairSpread U ⊆ pairSpread U' :=
  fun _ hq => ⟨hq.1, h hq.2⟩

/-- The low-multiplicity incidence region of one line, in `(t, y)` space. -/
def lowRegion (c d : Fin 3 → ℝ) (r : ℝ) (G : Set ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.1 ∈ G ∧ p.2 ∈ coordBox (2 * r) (planarPos c d p.1)}

theorem measurableSet_lowRegion (c d : Fin 3 → ℝ) (r : ℝ) {G : Set ℝ}
    (hG : MeasurableSet G) : MeasurableSet (lowRegion c d r G) := by
  have hc : Continuous (fun p : ℝ × (Fin 2 → ℝ) => planarPos c d p.1) :=
    (continuous_planarPos_fixed c d).comp continuous_fst
  refine (measurableSet_Icc.preimage measurable_fst).inter
    ((hG.preimage measurable_fst).inter ?_)
  change MeasurableSet ({p : ℝ × (Fin 2 → ℝ) |
      (fun j => planarPos c d p.1 j - 2 * r) ≤ p.2} ∩
    {p : ℝ × (Fin 2 → ℝ) | p.2 ≤ fun j => planarPos c d p.1 j + 2 * r})
  have hc' : Continuous (fun p : ℝ × (Fin 2 → ℝ) => fun j => planarPos c d p.1 j - 2 * r) :=
    continuous_pi fun j => ((continuous_apply j).comp hc).sub continuous_const
  have hc'' : Continuous (fun p : ℝ × (Fin 2 → ℝ) => fun j => planarPos c d p.1 j + 2 * r) :=
    continuous_pi fun j => ((continuous_apply j).comp hc).add continuous_const
  exact (measurableSet_le hc'.measurable measurable_snd).inter
    (measurableSet_le measurable_snd hc''.measurable)

/-- One line: the incidences at good times `G` inside `V` have mass at most `(2r)⁻²` times
the volume of `V` within the low region of the line. -/
theorem line_lowSpread_le {r : ℝ} (hr : 0 < r) (c d : Fin 3 → ℝ)
    {V : Set (ℝ × (Fin 2 → ℝ))} (hV : MeasurableSet V) {G : Set ℝ} (hG : MeasurableSet G) :
    (((boxLaw r c).prod (boxLaw r d)).prod volume)
        {q | q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ G ∧ (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} ≤
      (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * volume (V ∩ lowRegion c d r G) := by
  have := boxLaw_isProbabilityMeasure hr c
  have := boxLaw_isProbabilityMeasure hr d
  have hm1 : MeasurableSet {q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ |
      q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ G ∧ (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} :=
    (measurableSet_Icc.preimage measurable_snd).inter ((hG.preimage measurable_snd).inter
      (hV.preimage (measurable_snd.prodMk continuous_planarPos.measurable)))
  have hm2 : MeasurableSet (V ∩ lowRegion c d r G) := hV.inter (measurableSet_lowRegion c d r hG)
  rw [Measure.prod_apply_symm hm1]
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume from rfl,
    Measure.prod_apply hm2, ← lintegral_const_mul _ (measurable_measure_prodMk_left hm2)]
  refine lintegral_mono fun t => ?_
  dsimp only
  by_cases ht : t ∈ Icc (0 : ℝ) 1 ∧ t ∈ G
  · have e1 : (fun x => (x, t)) ⁻¹' {q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ |
          q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ G ∧ (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} =
        {q : (Fin 3 → ℝ) × (Fin 3 → ℝ) | planarPos q.1 q.2 t ∈ Prod.mk t ⁻¹' V} := by
      ext q
      simp [ht.1.1, ht.1.2, ht.2]
    have e2 : Prod.mk t ⁻¹' (V ∩ lowRegion c d r G) =
        Prod.mk t ⁻¹' V ∩ coordBox (2 * r) (planarPos c d t) := by
      ext y
      simp [lowRegion, ht.1.1, ht.1.2, ht.2]
    rw [e1, e2]
    exact boxPair_planarPos_le hr c d ht.1 (measurable_prodMk_left hV)
  · have e1 : (fun x => (x, t)) ⁻¹' {q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ |
          q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ G ∧ (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} = ∅ := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      tauto
    rw [e1, measure_empty]
    exact bot_le


/-- The good (low-multiplicity) times of line `i`. -/
def lowTimes {n : ℕ} (b s : Fin n → Fin 3 → ℝ) (δ T : ℝ) (i : Fin n) : Set ℝ :=
  {t | ¬ T ≤ (mult b s δ i t : ℝ)}

theorem measurableSet_lowTimes {n : ℕ} (b s : Fin n → Fin 3 → ℝ) (δ T : ℝ) (i : Fin n) :
    MeasurableSet (lowTimes b s δ T i) :=
  (measurableSet_le measurable_const (measurable_mult b s δ i)).compl

open Classical in
/-- At any point of `(t, y)` space at most `T` low regions of lines overlap. -/
theorem card_low_le {n : ℕ} (b s : Fin n → Fin 3 → ℝ) {r δ T : ℝ} (h4r : 4 * r ≤ δ)
    (hT : 0 ≤ T) (p : ℝ × (Fin 2 → ℝ)) :
    (((Finset.univ : Finset (Fin n)).filter
      (fun i => p ∈ lowRegion (b i) (s i) r (lowTimes b s δ T i))).card : ℝ) ≤ T := by
  classical
  set A := (Finset.univ : Finset (Fin n)).filter
    (fun i => p ∈ lowRegion (b i) (s i) r (lowTimes b s δ T i)) with hAdef
  rcases A.eq_empty_or_nonempty with hA | ⟨i₀, hi₀⟩
  · rw [hA, Finset.card_empty, Nat.cast_zero]
    exact hT
  · have hi₀' := (Finset.mem_filter.mp hi₀).2
    have hclose : ∀ i ∈ A, ∀ j : Fin 2,
        |p.2 j - planarPos (b i) (s i) p.1 j| ≤ 2 * r := by
      intro i hi j
      exact mem_coordBox_iff.mp (Finset.mem_filter.mp hi).2.2.2 j
    have hsub : A ⊆ (Finset.univ : Finset (Fin n)).filter (fun j =>
        |(b j 0 + p.1 * s j 0) - (b i₀ 0 + p.1 * s i₀ 0)| ≤ δ ∧
          |(b j 1 + p.1 * s j 1) - (b i₀ 1 + p.1 * s i₀ 1)| ≤ δ) := by
      intro i hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h1 := hclose i hi 0
        have h2 := hclose i₀ hi₀ 0
        simp only [planarPos_zero] at h1 h2
        calc |(b i 0 + p.1 * s i 0) - (b i₀ 0 + p.1 * s i₀ 0)|
            = |(p.2 0 - (b i₀ 0 + p.1 * s i₀ 0)) - (p.2 0 - (b i 0 + p.1 * s i 0))| := by
              ring_nf
          _ ≤ |p.2 0 - (b i₀ 0 + p.1 * s i₀ 0)| + |p.2 0 - (b i 0 + p.1 * s i 0)| :=
              abs_sub _ _
          _ ≤ δ := by linarith
      · have h1 := hclose i hi 1
        have h2 := hclose i₀ hi₀ 1
        simp only [planarPos_one] at h1 h2
        calc |(b i 1 + p.1 * s i 1) - (b i₀ 1 + p.1 * s i₀ 1)|
            = |(p.2 1 - (b i₀ 1 + p.1 * s i₀ 1)) - (p.2 1 - (b i 1 + p.1 * s i 1))| := by
              ring_nf
          _ ≤ |p.2 1 - (b i₀ 1 + p.1 * s i₀ 1)| + |p.2 1 - (b i 1 + p.1 * s i 1)| :=
              abs_sub _ _
          _ ≤ δ := by linarith
    have hcard : (A.card : ℝ) ≤ (mult b s δ i₀ p.1 : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hlt : ¬ T ≤ (mult b s δ i₀ p.1 : ℝ) := hi₀'.2.1
    linarith [not_le.mp hlt]

/-- Summing the low regions of all lines over a measurable set `V` costs at most `T`. -/
theorem sum_low_le {n : ℕ} (b s : Fin n → Fin 3 → ℝ) {r δ T : ℝ} (h4r : 4 * r ≤ δ)
    (hT : 0 ≤ T) {V : Set (ℝ × (Fin 2 → ℝ))} (hV : MeasurableSet V) :
    ∑ i, volume (V ∩ lowRegion (b i) (s i) r (lowTimes b s δ T i)) ≤
      ENNReal.ofReal T * volume V := by
  classical
  set L := fun i => lowRegion (b i) (s i) r (lowTimes b s δ T i) with hLdef
  have hL : ∀ i, MeasurableSet (V ∩ L i) := fun i =>
    hV.inter (measurableSet_lowRegion _ _ r (measurableSet_lowTimes b s δ T i))
  calc ∑ i, volume (V ∩ L i) = ∑ i, ∫⁻ p, (V ∩ L i).indicator 1 p := by
        congr 1
        funext i
        rw [lintegral_indicator_one (hL i)]
    _ = ∫⁻ p, ∑ i, (V ∩ L i).indicator 1 p :=
        (lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hL i))).symm
    _ ≤ ∫⁻ p, V.indicator (fun _ => ENNReal.ofReal T) p := by
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ V
        · rw [indicator_of_mem hp]
          have hsum : ∑ i, (V ∩ L i).indicator (1 : ℝ × (Fin 2 → ℝ) → ℝ≥0∞) p =
              (((Finset.univ : Finset (Fin n)).filter (fun i => p ∈ L i)).card : ℝ≥0∞) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hpi : p ∈ L i
            · simp [indicator_of_mem (mem_inter hp hpi), hpi]
            · simp [hpi]
          rw [hsum, ← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (card_low_le b s h4r hT p)
        · have : ∀ i, p ∉ V ∩ L i := fun i h => hp h.1
          simp [indicator_of_notMem hp, indicator_of_notMem (this _)]
    _ = ENNReal.ofReal T * volume V := by
        rw [lintegral_indicator hV, setLIntegral_const]

/-- **Finite-scale spread estimate.** For the smoothed prior of `n` lines with boxes of
radius `r` and `4r ≤ δ`, the incidence mass over a base set `U` is at most
`(1/n) (Σ_i |{t ∈ [0,1] : T ≤ mult_i(t)}| + (2r)⁻² T vol U)`. -/
theorem smoothedPrior_spread_le {n : ℕ} (b s : Fin n → Fin 3 → ℝ) {r δ T : ℝ} (hr : 0 < r)
    (h4r : 4 * r ≤ δ) (hT : 0 ≤ T) (U : Set (EuclideanSpace ℝ (Fin 3))) :
    ((smoothedPrior r b s).prod volume) (pairSpread U) ≤
      (n : ℝ≥0∞)⁻¹ * (∑ i, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)} +
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * (ENNReal.ofReal T * volume U)) := by
  wlog hU : MeasurableSet U generalizing U
  · have h := this (toMeasurable volume U) (measurableSet_toMeasurable _ _)
    rw [measure_toMeasurable] at h
    exact (measure_mono (pairSpread_mono (subset_toMeasurable _ _))).trans h
  set V := baseLift U with hVdef
  have hV : MeasurableSet V := measurableSet_baseLift hU
  have hVU : volume V = volume U := volume_baseLift hU
  have hline : ∀ i, (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume) (pairSpread U) ≤
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)} +
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ *
          volume (V ∩ lowRegion (b i) (s i) r (lowTimes b s δ T i)) := by
    intro i
    have := boxLaw_isProbabilityMeasure hr (b i)
    have := boxLaw_isProbabilityMeasure hr (s i)
    have hsub : pairSpread U ⊆
        (univ ×ˢ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)}) ∪
          {q | q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ lowTimes b s δ T i ∧
            (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} := by
      intro q hq
      rw [pairSpread_eq] at hq
      by_cases hT' : T ≤ (mult b s δ i q.2 : ℝ)
      · exact Or.inl ⟨mem_univ _, hq.1, hT'⟩
      · exact Or.inr ⟨hq.1, hT', hq.2⟩
    calc (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume) (pairSpread U)
        ≤ (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume)
            ((univ ×ˢ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)}) ∪
              {q | q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ lowTimes b s δ T i ∧
                (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V}) := measure_mono hsub
      _ ≤ (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume)
            (univ ×ˢ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)}) +
          (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume)
            {q | q.2 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ lowTimes b s δ T i ∧
              (q.2, planarPos q.1.1 q.1.2 q.2) ∈ V} := measure_union_le _ _
      _ ≤ _ := by
        gcongr
        · rw [Measure.prod_prod, measure_univ, one_mul]
        · exact line_lowSpread_le hr (b i) (s i) hV (measurableSet_lowTimes b s δ T i)
  rw [smoothedPrior, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul,
    ← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_apply_of_countable, tsum_fintype]
  gcongr
  calc ∑ i, (((boxLaw r (b i)).prod (boxLaw r (s i))).prod volume) (pairSpread U)
      ≤ ∑ i, (volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)} +
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ *
          volume (V ∩ lowRegion (b i) (s i) r (lowTimes b s δ T i))) :=
        Finset.sum_le_sum fun i _ => hline i
    _ = ∑ i, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)} +
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ *
          ∑ i, volume (V ∩ lowRegion (b i) (s i) r (lowTimes b s δ T i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i, volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ T ≤ (mult b s δ i t : ℝ)} +
        (ENNReal.ofReal (2 * r) ^ 2)⁻¹ * (ENNReal.ofReal T * volume U) := by
        rw [← hVU]
        gcongr
        exact sum_low_le b s h4r hT hV

end Submission.Obl.k4_dk4_smoothed_problem.Spread
