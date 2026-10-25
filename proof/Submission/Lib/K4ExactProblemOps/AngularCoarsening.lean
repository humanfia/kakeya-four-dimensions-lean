import Submission.Lib.K4ExactProblemOps.FiberSum

/-!
# Angular caps under coarsening, one world at a time (paper Lemma 2.7)

Let a finite incidence measure `μ` have a fine pure observation `o` (hidden bins at
depth `L`), velocity bins `w`, a fine joint density `G`, a fine pure density `gL`
and a coarse pure density `gb` (hidden bins at depth `b`, obtained by the dyadic
coarsening `coarsenO m`).  Then the coarse joint density is the fiber sum of `G`,
and it exceeds `2 θ a₃` only where the fine angular cap `G ≤ a₁` fails, where the
fine pure lower bound `a₂ ≤ gL` fails, or where the coarse pure upper bound
`gb ≤ a₃` fails, with the omitted-mass loss factor two.  Here `a₁ ≤ θ a₂`.
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory

variable {I X Y : Type*} [MeasurableSpace I] [MeasurableSpace X] [MeasurableSpace Y]

/-- The joint observation of the coarsened problem is the coarsening of the fine one. -/
theorem map_coarsenJ_joint (μ : Measure I) (α : Measure X) (β : Measure Y) [SFinite β]
    {o : I → X × ℤ} {w : I → Y} (ho : Measurable o) (hw : Measurable w) (m : ℕ)
    {G : (X × ℤ) × Y → ENNReal} (hG : Measurable G)
    (hGd : Measure.map (fun p => (o p, w p)) μ =
      ((α.prod Measure.count).prod β).withDensity G) :
    Measure.map (fun p => coarsenJ m (o p, w p)) μ =
      ((α.prod Measure.count).prod β).withDensity (fiberSumJ m G) := by
  have h : (fun p => coarsenJ m (o p, w p)) = coarsenJ m ∘ (fun p => (o p, w p)) := rfl
  rw [h, ← Measure.map_map (measurable_coarsenJ m) (ho.prodMk hw), hGd,
    map_coarsenJ_withDensity m α β hG]

/-- The per-world mass estimate behind the angular cap of a coarsening. -/
theorem coarse_angular_mass (μ : Measure I) [IsFiniteMeasure μ]
    (α : Measure X) (β : Measure Y) [SFinite β]
    {o : I → X × ℤ} {w : I → Y} (ho : Measurable o) (hw : Measurable w) (m : ℕ)
    {G : (X × ℤ) × Y → ENNReal} {gL gb : X × ℤ → ENNReal}
    (hG : Measurable G) (hgL : Measurable gL) (hgb : Measurable gb)
    (hGd : Measure.map (fun p => (o p, w p)) μ =
      ((α.prod Measure.count).prod β).withDensity G)
    (hgLd : Measure.map o μ = (α.prod Measure.count).withDensity gL)
    (hgbd : Measure.map (fun p => coarsenO m (o p)) μ =
      (α.prod Measure.count).withDensity gb)
    {a₁ a₂ a₃ θ : ENNReal} (hθ : a₁ ≤ θ * a₂) :
    μ {p | 2 * θ * a₃ < fiberSumJ m G (coarsenJ m (o p, w p))} ≤
      2 * (μ {p | a₁ < G (o p, w p)} + μ {p | gL (o p) < a₂}) +
        μ {p | a₃ < gb (coarsenO m (o p))} := by
  classical
  set J : I → (X × ℤ) × Y := fun p => (o p, w p) with hJdef
  have hJ : Measurable J := ho.prodMk hw
  set refO : Measure (X × ℤ) := α.prod Measure.count with hrefO
  set refJ : Measure ((X × ℤ) × Y) := refO.prod β with hrefJ
  set Good : Set ((X × ℤ) × Y) := {z | G z ≤ a₁ ∧ a₂ ≤ gL z.1} with hGooddef
  have hGood : MeasurableSet Good :=
    (measurableSet_le hG measurable_const).inter
      (measurableSet_le measurable_const (hgL.comp measurable_fst))
  set Gg := Good.indicator G with hGgdef
  set Gb := Goodᶜ.indicator G with hGbdef
  have hGg : Measurable Gg := hG.indicator hGood
  have hGb : Measurable Gb := hG.indicator hGood.compl
  have hsplit : fiberSumJ m G = fiberSumJ m Gg + fiberSumJ m Gb := by
    rw [← fiberSumJ_add, hGgdef, hGbdef, Set.indicator_self_add_compl]
  -- Step 1: on good fine cells the joint density is at most `θ` times the pure one.
  have hptw : ∀ z, Gg z ≤ θ * gL z.1 := by
    intro z
    by_cases hz : z ∈ Good
    · rw [hGgdef, Set.indicator_of_mem hz]
      exact hz.1.trans (hθ.trans (by gcongr; exact hz.2))
    · rw [hGgdef, Set.indicator_of_notMem hz]
      exact zero_le
  have hfib : ∀ z, fiberSumJ m Gg z ≤ θ * fiberSumO m gL z.1 := by
    intro z
    unfold fiberSumJ fiberSumO
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hptw _
  -- Step 2: the fiber sum of the fine pure density is the coarse pure density.
  have hmapO : Measure.map (fun p => coarsenO m (o p)) μ =
      refO.withDensity (fiberSumO m gL) := by
    have h : (fun p => coarsenO m (o p)) = coarsenO m ∘ o := rfl
    rw [h, ← Measure.map_map (measurable_coarsenO m) ho, hgLd,
      map_coarsenO_withDensity m α hgL]
  have hfinite : ∫⁻ z, fiberSumO m gL z ∂refO ≠ ⊤ := by
    have h1 : ∫⁻ z, fiberSumO m gL z ∂refO =
        Measure.map (fun p => coarsenO m (o p)) μ Set.univ := by
      rw [hmapO, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1]
    exact measure_ne_top _ _
  have hae : fiberSumO m gL =ᵐ[refO] gb :=
    (withDensity_eq_iff (measurable_fiberSumO m hgL).aemeasurable hgb.aemeasurable
      hfinite).1 (hmapO.symm.trans hgbd)
  -- Step 3: the good coarse joint density is bounded by `θ gb` off a null set.
  set Z : Set ((X × ℤ) × Y) := {z | θ * gb z.1 < fiberSumJ m Gg z} with hZdef
  have hZ : MeasurableSet Z :=
    measurableSet_lt (measurable_const.mul (hgb.comp measurable_fst))
      (measurable_fiberSumJ m hGg)
  have hZnull : refJ Z = 0 := by
    set T : Set (X × ℤ) := {x | fiberSumO m gL x ≠ gb x} with hTdef
    have hT : refO T = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      exact hae
    have hsub : Z ⊆ T ×ˢ Set.univ := by
      intro z hz
      refine ⟨?_, Set.mem_univ _⟩
      intro heq
      have h1 := hfib z
      rw [heq] at h1
      exact absurd hz (not_lt.2 h1)
    refine measure_mono_null hsub ?_
    rw [hrefJ, Measure.prod_prod, hT, zero_mul]
  -- Step 4: the coarse joint law has density `fiberSumJ m G`.
  have hmapJ : Measure.map (fun p => coarsenJ m (o p, w p)) μ =
      refJ.withDensity (fiberSumJ m G) := map_coarsenJ_joint μ α β ho hw m hG hGd
  have hJb : Measurable fun p => coarsenJ m (o p, w p) := (measurable_coarsenJ m).comp hJ
  have hpre : ∀ S, MeasurableSet S →
      μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' S) = refJ.withDensity (fiberSumJ m G) S := by
    intro S hS
    rw [← hmapJ, Measure.map_apply hJb hS]
  have hZμ : μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' Z) = 0 := by
    rw [hpre Z hZ]
    exact withDensity_absolutelyContinuous _ _ hZnull
  -- Step 5: where the bad part dominates, the mass is at most twice the bad mass.
  set A₁ : Set ((X × ℤ) × Y) := {z | fiberSumJ m Gg z < fiberSumJ m Gb z} with hA₁def
  have hA₁ : MeasurableSet A₁ :=
    measurableSet_lt (measurable_fiberSumJ m hGg) (measurable_fiberSumJ m hGb)
  have hbadmass : refJ.withDensity (fiberSumJ m Gb) Set.univ = μ (J ⁻¹' Goodᶜ) := by
    rw [← map_coarsenJ_withDensity m α β hGb, Measure.map_apply (measurable_coarsenJ m)
      MeasurableSet.univ, Set.preimage_univ, hGbdef, withDensity_indicator hGood.compl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← withDensity_apply _ hGood.compl, ← hGd, Measure.map_apply hJ hGood.compl]
  have hA₁μ : μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' A₁) ≤ 2 * μ (J ⁻¹' Goodᶜ) := by
    rw [hpre A₁ hA₁, withDensity_apply _ hA₁, ← hbadmass,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ z in A₁, fiberSumJ m G z ∂refJ
        ≤ ∫⁻ z in A₁, 2 * fiberSumJ m Gb z ∂refJ := by
          refine setLIntegral_mono ((measurable_fiberSumJ m hGb).const_mul 2) ?_
          intro z hz
          rw [hsplit, Pi.add_apply, two_mul]
          exact add_le_add (show fiberSumJ m Gg z < fiberSumJ m Gb z from hz).le le_rfl
      _ = 2 * ∫⁻ z in A₁, fiberSumJ m Gb z ∂refJ :=
          lintegral_const_mul _ (measurable_fiberSumJ m hGb)
      _ ≤ 2 * ∫⁻ z, fiberSumJ m Gb z ∂refJ := by
          gcongr
          exact Measure.restrict_le_self
  -- Step 6: the bad fine set is covered by the two fine exceptional sets.
  have hbad : μ (J ⁻¹' Goodᶜ) ≤ μ {p | a₁ < G (o p, w p)} + μ {p | gL (o p) < a₂} := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro p hp
    simp only [Set.mem_preimage, Set.mem_compl_iff, hGooddef, Set.mem_ofPred_eq,
      not_and_or, not_le] at hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  -- Step 7: combine.
  have hcover : {p | 2 * θ * a₃ < fiberSumJ m G (coarsenJ m (o p, w p))} ⊆
      ((fun p => coarsenJ m (o p, w p)) ⁻¹' A₁ ∪ {p | a₃ < gb (coarsenO m (o p))}) ∪
        (fun p => coarsenJ m (o p, w p)) ⁻¹' Z := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, hA₁def, hZdef, Set.mem_ofPred_eq,
      not_or, not_lt] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hfst : (coarsenJ m (o p, w p)).1 = coarsenO m (o p) := rfl
    rw [hfst] at h3
    have : fiberSumJ m G (coarsenJ m (o p, w p)) ≤ 2 * θ * a₃ := by
      rw [hsplit, Pi.add_apply]
      calc fiberSumJ m Gg (coarsenJ m (o p, w p)) + fiberSumJ m Gb (coarsenJ m (o p, w p))
          ≤ fiberSumJ m Gg (coarsenJ m (o p, w p)) +
              fiberSumJ m Gg (coarsenJ m (o p, w p)) := add_le_add le_rfl h1
        _ = 2 * fiberSumJ m Gg (coarsenJ m (o p, w p)) := (two_mul _).symm
        _ ≤ 2 * (θ * gb (coarsenO m (o p))) := by gcongr
        _ ≤ 2 * (θ * a₃) := by gcongr
        _ = 2 * θ * a₃ := (mul_assoc _ _ _).symm
    exact absurd hp (not_lt.2 this)
  calc μ {p | 2 * θ * a₃ < fiberSumJ m G (coarsenJ m (o p, w p))}
      ≤ μ (((fun p => coarsenJ m (o p, w p)) ⁻¹' A₁ ∪ {p | a₃ < gb (coarsenO m (o p))}) ∪
          (fun p => coarsenJ m (o p, w p)) ⁻¹' Z) := measure_mono hcover
    _ ≤ μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' A₁ ∪ {p | a₃ < gb (coarsenO m (o p))}) +
          μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' Z) := measure_union_le _ _
    _ ≤ μ ((fun p => coarsenJ m (o p, w p)) ⁻¹' A₁) + μ {p | a₃ < gb (coarsenO m (o p))} := by
          rw [hZμ, add_zero]
          exact measure_union_le _ _
    _ ≤ 2 * (μ {p | a₁ < G (o p, w p)} + μ {p | gL (o p) < a₂}) +
          μ {p | a₃ < gb (coarsenO m (o p))} :=
          add_le_add (hA₁μ.trans (by gcongr)) le_rfl

end Submission.Lib.K4ExactProblemOps
