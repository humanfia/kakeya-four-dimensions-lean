import Submission.Obl.k4_raw_localized_native_systems.C.NativeLaw

/-
Adapted from this LOT tree, o178, session x0596, `CLaw.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The law of a full-time chart

For a chart with assignment `A` of positive prior and a measurable good set
`G ⊆ A × [0,1]`, the law `ν(A)⁻¹ (ν ⊗ dt)|_G` is a `RegularScalarLaw` (dominated by
the conditional prior, supported in unit time), its budget `ν(A)` times it is
`(ν ⊗ dt)|_G`, and the weighted priors of disjoint assignments add up to at most one.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The law of a full-time chart with good set `G`. -/
def cLaw (ν : Measure Line) (A : Set Line) (G : Set Point) : Measure Point :=
  (ν A)⁻¹ • ((ν.prod volume).restrict G)

theorem cLaw_univ (ν : Measure Line) (A : Set Line) (G : Set Point) :
    cLaw ν A G Set.univ = (ν A)⁻¹ * (ν.prod volume) G := by
  simp [cLaw, Measure.restrict_apply MeasurableSet.univ]

theorem isProbability_cond (ν : Measure Line) [IsFiniteMeasure ν] {A : Set Line}
    (hpos : 0 < ν A) : IsProbabilityMeasure ((ν A)⁻¹ • ν.restrict A) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (measure_ne_top ν A)

theorem restrict_le_prod_restrict (ν : Measure Line) [SFinite ν] {A : Set Line} {G : Set Point}
    (hGA : G ⊆ A ×ˢ Set.univ) :
    (ν.prod volume).restrict G ≤ (ν.restrict A).prod volume := by
  have h1 : (ν.prod volume).restrict G ≤ (ν.prod volume).restrict (A ×ˢ Set.univ) :=
    Measure.restrict_mono hGA le_rfl
  refine h1.trans (le_of_eq ?_)
  rw [← Measure.prod_restrict, Measure.restrict_univ]

/-- **The law is a regular scalar law.** -/
theorem cLaw_regular {N χ d s m S U : ℝ} {ν : Measure Line} [IsProbabilityMeasure ν]
    {A : Set Line} {G : Set Point} (hG : MeasurableSet G)
    (hGA : G ⊆ A ×ˢ Set.Icc (0 : ℝ) 1) (hpos : 0 < ν A) (hNχ : 1 ≤ N ^ χ)
    {b : Line → Fin 5 → ℝ} (hb : Measurable b) (hbnd : ∀ l i, |b l i| ≤ N ^ χ) :
    RegularScalarLaw N χ d s m S U ((ν A)⁻¹ • ν.restrict A) (cLaw ν A G) b := by
  have hprob := isProbability_cond ν hpos
  refine ⟨hb, hprob, ?_, ?_, hbnd⟩
  · -- domination by the conditional prior
    have hGA' : G ⊆ A ×ˢ Set.univ := fun z hz => ⟨(hGA hz).1, Set.mem_univ _⟩
    have hdom := restrict_le_prod_restrict ν hGA'
    rw [Measure.prod_smul_left]
    intro t
    simp only [cLaw, Measure.smul_apply, smul_eq_mul]
    have h1 : (ν A)⁻¹ * (ν.prod volume).restrict G t ≤ (ν A)⁻¹ * ((ν.restrict A).prod volume) t := by
      gcongr
    refine h1.trans ?_
    have h2 : (1 : ENNReal) ≤ ENNReal.ofReal (N ^ χ) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hNχ
    calc (ν A)⁻¹ * ((ν.restrict A).prod volume) t
        = 1 * ((ν A)⁻¹ * ((ν.restrict A).prod volume) t) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (N ^ χ) * ((ν A)⁻¹ * ((ν.restrict A).prod volume) t) := by gcongr
  · -- unit-time support
    have hm : MeasurableSet ((Set.univ : Set Line) ×ˢ Set.Icc (0 : ℝ) 1)ᶜ :=
      (MeasurableSet.univ.prod measurableSet_Icc).compl
    simp only [cLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hm]
    have : ((Set.univ : Set Line) ×ˢ Set.Icc (0 : ℝ) 1)ᶜ ∩ G = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h hz
      exact h (hGA hz).2
    rw [this, measure_empty, mul_zero]

/-- The budget times the law is the restriction to the good set. -/
theorem budget_cLaw (ν : Measure Line) [IsFiniteMeasure ν] {A : Set Line} (hpos : 0 < ν A)
    (G : Set Point) : ν A • cLaw ν A G = (ν.prod volume).restrict G := by
  rw [cLaw, smul_smul, ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top ν A), one_smul]

/-- The weighted priors of assignments disjoint within each world add up to at most one. -/
theorem weighted_prior_sum_le {p : Data} {k : ℕ} (hp : Valid p) {C : ℕ}
    (γ : Fin C → Fin (p.W k)) (A : Fin C → Set Line) (hA : ∀ c, MeasurableSet (A c))
    (hdisj : ∀ c c', c ≠ c' → γ c = γ c' → Disjoint (A c) (A c')) :
    ∑ c, ENNReal.ofReal (p.ω k (γ c)) * p.ν k (γ c) (A c) ≤ 1 := by
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hω0 : ∀ w, 0 ≤ p.ω k w := (hfmt k).2.1
  have hω1 : ∑ w, p.ω k w = 1 := (hfmt k).2.2.1
  have hworld : ∀ w, ∑ c ∈ Finset.univ.filter (fun c => γ c = w), p.ν k w (A c) ≤ 1 := by
    intro w
    have : IsProbabilityMeasure (p.ν k w) := ((hfmt k).2.2.2.1 w).1
    have hdis : Set.PairwiseDisjoint (↑(Finset.univ.filter (fun c => γ c = w))) A := by
      intro c hc c' hc' hne
      exact hdisj c c' hne ((Finset.mem_filter.1 hc).2.trans (Finset.mem_filter.1 hc').2.symm)
    rw [← measure_biUnion_finset hdis (fun c _ => hA c)]
    exact prob_le_one
  calc ∑ c, ENNReal.ofReal (p.ω k (γ c)) * p.ν k (γ c) (A c)
      = ∑ w, ∑ c ∈ Finset.univ.filter (fun c => γ c = w),
          ENNReal.ofReal (p.ω k w) * p.ν k w (A c) := by
        rw [← Finset.sum_fiberwise Finset.univ γ]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun c hc => ?_
        rw [(Finset.mem_filter.1 hc).2]
    _ = ∑ w, ENNReal.ofReal (p.ω k w) *
          ∑ c ∈ Finset.univ.filter (fun c => γ c = w), p.ν k w (A c) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ w, ENNReal.ofReal (p.ω k w) * 1 := by
        gcongr with w; exact hworld w
    _ = 1 := by
        simp only [mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω0 w), hω1, ENNReal.ofReal_one]

end

end Submission.Obl.k4_raw_localized_native_systems.C
