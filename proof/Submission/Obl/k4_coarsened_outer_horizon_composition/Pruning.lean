import Submission.Obl.k4_coarsened_outer_horizon_composition.Observations

/-!
# Pruning a chart system to short observation lists

Markov's inequality for crossing counts under an observation density cap, and the bounded
multiplicity of the selected incidences of a chart system (disjoint assignments within one
dyadic time interval).  These are the measure-theoretic steps of the list part of the
"Saturation and label knowledge" lemma of the paper.
-/

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- The crossing count of an observation. -/
noncomputable def crossCount {ι : Type*} (S : Finset ι) (Cr : ι → Set Obs) (o : Obs) : ℝ≥0∞ :=
  ∑ b ∈ S, (Cr b).indicator 1 o

theorem measurable_crossCount {ι : Type*} (S : Finset ι) (Cr : ι → Set Obs)
    (hCr : ∀ b, MeasurableSet (Cr b)) : Measurable (crossCount S Cr) :=
  Finset.measurable_sum _ fun b _ => measurable_one.indicator (hCr b)

theorem crossCount_eq_card {ι : Type*} (S : Finset ι) (Cr : ι → Set Obs) (o : Obs)
    [DecidablePred fun b => o ∈ Cr b] :
    crossCount S Cr o = ((S.filter fun b => o ∈ Cr b).card : ℝ≥0∞) := by
  classical
  unfold crossCount
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : o ∈ Cr b <;> simp [h]

/-- Markov's inequality for the crossing count, on the part of the law where the observation
density is at most `a`. -/
theorem markov_crossings (μ : Measure Inc) (ob : Inc → Obs) (hob : Measurable ob)
    (gd : Obs → ℝ≥0∞) (hgd : Measurable gd)
    (hlaw : μ.map ob = (volume.prod Measure.count).withDensity gd)
    {ι : Type*} (S : Finset ι) (Cr : ι → Set Obs) (hCr : ∀ b, MeasurableSet (Cr b))
    (a θ : ℝ≥0∞) :
    θ * μ {p | gd (ob p) ≤ a ∧ θ ≤ crossCount S Cr (ob p)} ≤
      a * ∑ b ∈ S, (volume.prod Measure.count) (Cr b) := by
  set cap : Set Obs := {o | gd o ≤ a} with hcap
  have hcapm : MeasurableSet cap := measurableSet_le hgd measurable_const
  let φ : Obs → ℝ≥0∞ := cap.indicator (crossCount S Cr)
  have hφ : Measurable φ := (measurable_crossCount S Cr hCr).indicator hcapm
  have hsub : {p | gd (ob p) ≤ a ∧ θ ≤ crossCount S Cr (ob p)} ⊆ {p | θ ≤ φ (ob p)} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    have : ob p ∈ cap := hp.1
    simp only [φ, indicator_of_mem this]
    exact hp.2
  calc θ * μ {p | gd (ob p) ≤ a ∧ θ ≤ crossCount S Cr (ob p)}
      ≤ θ * μ {p | θ ≤ φ (ob p)} := mul_le_mul_right (measure_mono hsub) θ
    _ ≤ ∫⁻ p, φ (ob p) ∂μ :=
        mul_meas_ge_le_lintegral₀ (hφ.comp hob).aemeasurable θ
    _ = ∫⁻ o, φ o ∂(μ.map ob) := (lintegral_map hφ hob).symm
    _ = ∫⁻ o, gd o * φ o ∂(volume.prod Measure.count) := by
        rw [hlaw, lintegral_withDensity_eq_lintegral_mul _ hgd hφ]
        rfl
    _ ≤ ∫⁻ o, a * crossCount S Cr o ∂(volume.prod Measure.count) := by
        apply lintegral_mono
        intro o
        by_cases ho : o ∈ cap
        · simp only [φ, indicator_of_mem ho]
          exact mul_le_mul_left ho _
        · simp [φ, indicator_of_notMem ho]
    _ = a * ∑ b ∈ S, (volume.prod Measure.count) (Cr b) := by
        rw [lintegral_const_mul _ (measurable_crossCount S Cr hCr)]
        congr 1
        unfold crossCount
        rw [lintegral_finsetSum _ fun b _ => measurable_one.indicator (hCr b)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [lintegral_indicator_one (hCr b)]

/-- The incidences with many crossings have small mass, apart from the large-density part. -/
theorem crossing_exceptional_le (μ : Measure Inc) (ob : Inc → Obs) (hob : Measurable ob)
    (gd : Obs → ℝ≥0∞) (hgd : Measurable gd)
    (hlaw : μ.map ob = (volume.prod Measure.count).withDensity gd)
    {ι : Type*} (S : Finset ι) (Cr : ι → Set Obs) (hCr : ∀ b, MeasurableSet (Cr b))
    (a θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ' : θ ≠ ∞) :
    μ {p | θ < crossCount S Cr (ob p)} ≤
      μ {p | a < gd (ob p)} + a * (∑ b ∈ S, (volume.prod Measure.count) (Cr b)) / θ := by
  have hsplit : {p | θ < crossCount S Cr (ob p)} ⊆
      {p | a < gd (ob p)} ∪ {p | gd (ob p) ≤ a ∧ θ ≤ crossCount S Cr (ob p)} := by
    intro p hp
    simp only [mem_ofPred_eq, mem_union] at hp ⊢
    by_cases h : a < gd (ob p)
    · exact Or.inl h
    · exact Or.inr ⟨not_lt.mp h, hp.le⟩
  refine (measure_mono hsplit).trans ((measure_union_le _ _).trans (add_le_add le_rfl ?_))
  have hm := markov_crossings μ ob hob gd hgd hlaw S Cr hCr a θ
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ) (Or.inl hθ'), mul_comm]
  exact hm

/-- Sets covering every point at most twice have at most twice the total mass. -/
theorem sum_measure_inter_le_two {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {ι : Type*} (S : Finset ι) (F : ι → Set X) (hF : ∀ b, MeasurableSet (F b))
    (hmult : ∀ p, (∑ b ∈ S, (F b).indicator (1 : X → ℝ≥0∞) p) ≤ 2)
    {Y : Set X} (hY : MeasurableSet Y) :
    ∑ b ∈ S, μ (F b ∩ Y) ≤ 2 * μ Y := by
  calc ∑ b ∈ S, μ (F b ∩ Y) = ∑ b ∈ S, ∫⁻ p, (F b ∩ Y).indicator 1 p ∂μ := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [lintegral_indicator_one ((hF b).inter hY)]
    _ = ∫⁻ p, ∑ b ∈ S, (F b ∩ Y).indicator 1 p ∂μ :=
        (lintegral_finsetSum _ fun b _ => measurable_one.indicator ((hF b).inter hY)).symm
    _ ≤ ∫⁻ p, Y.indicator (fun _ => (2 : ℝ≥0∞)) p ∂μ := by
        apply lintegral_mono
        intro p
        by_cases hp : p ∈ Y
        · rw [indicator_of_mem hp]
          refine le_trans (Finset.sum_le_sum fun b _ => ?_) (hmult p)
          by_cases hb : p ∈ F b
          · simp [indicator_of_mem hb, indicator_of_mem (mem_inter hb hp)]
          · have hb' : p ∉ F b ∩ Y := fun h => hb h.1
            simp [indicator_of_notMem hb, indicator_of_notMem hb']
        · rw [indicator_of_notMem hp]
          apply le_of_eq
          refine Finset.sum_eq_zero fun b _ => ?_
          exact indicator_of_notMem (fun h => hp h.2) _
    _ = 2 * μ Y := lintegral_indicator_const hY 2

/-- A time lies in at most two closed dyadic intervals of one generation. -/
theorem card_dyadic_intervals_le_two (T : ℕ) (t : ℝ) :
    (Finset.univ.filter fun j : Fin (2 ^ T) =>
      t ∈ Icc ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T)).card ≤ 2 := by
  classical
  set s := Finset.univ.filter fun j : Fin (2 ^ T) =>
      t ∈ Icc ((j : ℕ) / (2 : ℝ) ^ T) (((j : ℕ) + 1) / (2 : ℝ) ^ T) with hs
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have hclose : ∀ j ∈ s, ∀ j' ∈ s, (j : ℕ) ≤ (j' : ℕ) + 1 := by
    intro j hj j' hj'
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, mem_Icc] at hj hj'
    have h1 : ((j : ℕ) : ℝ) / 2 ^ T ≤ (((j' : ℕ) : ℝ) + 1) / 2 ^ T := hj.1.trans hj'.2
    rw [div_le_div_iff_of_pos_right hpos] at h1
    exact_mod_cast h1
  by_contra hcard
  push Not at hcard
  obtain ⟨j₁, hj₁, j₂, hj₂, j₃, hj₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hcard
  have a := hclose j₁ hj₁ j₂ hj₂
  have b := hclose j₂ hj₂ j₁ hj₁
  have c := hclose j₁ hj₁ j₃ hj₃
  have d := hclose j₃ hj₃ j₁ hj₁
  have e := hclose j₂ hj₂ j₃ hj₃
  have f := hclose j₃ hj₃ j₂ hj₂
  have n12 : (j₁ : ℕ) ≠ j₂ := fun h => h12 (Fin.ext h)
  have n13 : (j₁ : ℕ) ≠ j₃ := fun h => h13 (Fin.ext h)
  have n23 : (j₂ : ℕ) ≠ j₃ := fun h => h23 (Fin.ext h)
  omega

end Submission.Obl.k4_coarsened_outer_horizon_composition

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- The total pruning loss of a chart system at one sample: incidences whose observation is
crossed by more than `θ` charts of their world. -/
theorem pruning_loss_le {W' C' : ℕ} (ω' : Fin W' → ℝ) (hω0 : ∀ γ, 0 ≤ ω' γ)
    (hω1 : ∑ γ, ω' γ = 1)
    (ν' : Fin W' → Measure Line) (E' : Fin W' → Set Inc)
    (hμ1 : ∀ γ, ((ν' γ).prod volume).restrict (E' γ) univ ≤ 1)
    (ob : Fin W' → Inc → Obs) (hob : ∀ γ, Measurable (ob γ))
    (gd : Fin W' → Obs → ℝ≥0∞) (hgd : ∀ γ, Measurable (gd γ))
    (hlaw : ∀ γ, (((ν' γ).prod volume).restrict (E' γ)).map (ob γ) =
      (volume.prod Measure.count).withDensity (gd γ))
    (γ : Fin C' → Fin W') (F : Fin C' → Set Inc) (hF : ∀ b, MeasurableSet (F b))
    (hFE : ∀ b, F b ⊆ E' (γ b))
    (Cr : Fin C' → Set Obs) (hCr : ∀ b, MeasurableSet (Cr b))
    (hmult : ∀ γ₁ p, (∑ b ∈ Finset.univ.filter (fun b => γ b = γ₁),
      (F b).indicator (1 : Inc → ℝ≥0∞) p) ≤ 2)
    (a Kc θ X : ℝ≥0∞) (hθ : θ ≠ 0) (hθ' : θ ≠ ∞)
    (hvol : ∀ b, a * (volume.prod Measure.count) (Cr b) ≤ Kc * ((ν' (γ b)).prod volume) (F b))
    (htyp : ∑ γ₁, ENNReal.ofReal (ω' γ₁) *
      ((ν' γ₁).prod volume).restrict (E' γ₁) {p | a < gd γ₁ (ob γ₁ p)} ≤ X) :
    ∑ b, ENNReal.ofReal (ω' (γ b)) * ((ν' (γ b)).prod volume)
        (F b ∩ {p | θ < crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr
          (ob (γ b) p)}) ≤ 2 * X + 4 * Kc / θ := by
  classical
  set μ : Fin W' → Measure Inc := fun γ₁ => ((ν' γ₁).prod volume).restrict (E' γ₁) with hμ
  set S : Fin W' → Finset (Fin C') := fun γ₁ => Finset.univ.filter (fun b => γ b = γ₁) with hS
  set Xs : Fin W' → Set Inc := fun γ₁ => {p | θ < crossCount (S γ₁) Cr (ob γ₁ p)} with hXs
  have hXm : ∀ γ₁, MeasurableSet (Xs γ₁) := fun γ₁ =>
    measurableSet_lt measurable_const ((measurable_crossCount _ Cr hCr).comp (hob γ₁))
  -- restrict to the world measure
  have hrestr : ∀ b {Y : Set Inc}, ((ν' (γ b)).prod volume) (F b ∩ Y) = μ (γ b) (F b ∩ Y) := by
    intro b Y
    simp only [hμ]
    rw [Measure.restrict_eq_self _ (inter_subset_left.trans (hFE b))]
  -- fiberwise rewriting
  have hfib : ∑ b, ENNReal.ofReal (ω' (γ b)) * ((ν' (γ b)).prod volume) (F b ∩ Xs (γ b)) =
      ∑ γ₁, ENNReal.ofReal (ω' γ₁) * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ Xs γ₁) := by
    rw [← Finset.sum_fiberwise Finset.univ γ]
    refine Finset.sum_congr rfl fun γ₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hγ : γ b = γ₁ := (Finset.mem_filter.mp hb).2
    rw [hrestr b, hγ]
  have hfibm : ∑ b, ENNReal.ofReal (ω' (γ b)) * ((ν' (γ b)).prod volume) (F b) =
      ∑ γ₁, ENNReal.ofReal (ω' γ₁) * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ) := by
    rw [← Finset.sum_fiberwise Finset.univ γ]
    refine Finset.sum_congr rfl fun γ₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hγ : γ b = γ₁ := (Finset.mem_filter.mp hb).2
    subst hγ
    rw [← hrestr b, inter_univ]
  -- the total selected mass is at most two
  have htotal : ∑ b, ENNReal.ofReal (ω' (γ b)) * ((ν' (γ b)).prod volume) (F b) ≤ 2 := by
    rw [hfibm]
    calc ∑ γ₁, ENNReal.ofReal (ω' γ₁) * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ)
        ≤ ∑ γ₁, ENNReal.ofReal (ω' γ₁) * (2 * μ γ₁ univ) := by
          refine Finset.sum_le_sum fun γ₁ _ => mul_le_mul_right ?_ _
          exact sum_measure_inter_le_two (μ γ₁) (S γ₁) F hF (hmult γ₁) MeasurableSet.univ
      _ ≤ ∑ γ₁, ENNReal.ofReal (ω' γ₁) * 2 := by
          refine Finset.sum_le_sum fun γ₁ _ => mul_le_mul_right ?_ _
          calc 2 * μ γ₁ univ ≤ 2 * 1 := mul_le_mul_right (hμ1 γ₁) 2
            _ = 2 := mul_one 2
      _ = 2 := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun γ₁ _ => hω0 γ₁), hω1]
          simp
  -- one world
  have hworld : ∀ γ₁, ∑ b ∈ S γ₁, μ γ₁ (F b ∩ Xs γ₁) ≤
      2 * μ γ₁ {p | a < gd γ₁ (ob γ₁ p)} + 2 * (Kc * (∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ)) / θ) := by
    intro γ₁
    have h2 := sum_measure_inter_le_two (μ γ₁) (S γ₁) F hF (hmult γ₁) (hXm γ₁)
    have hex := crossing_exceptional_le (μ γ₁) (ob γ₁) (hob γ₁) (gd γ₁) (hgd γ₁) (hlaw γ₁)
      (S γ₁) Cr hCr a θ hθ hθ'
    have hcr : a * ∑ b ∈ S γ₁, (volume.prod Measure.count) (Cr b) ≤
        Kc * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      have hγ : γ b = γ₁ := (Finset.mem_filter.mp hb).2
      have := hvol b
      rw [← inter_univ (F b), hrestr b, hγ] at this
      exact this
    calc ∑ b ∈ S γ₁, μ γ₁ (F b ∩ Xs γ₁) ≤ 2 * μ γ₁ (Xs γ₁) := h2
      _ ≤ 2 * (μ γ₁ {p | a < gd γ₁ (ob γ₁ p)} +
            a * (∑ b ∈ S γ₁, (volume.prod Measure.count) (Cr b)) / θ) := mul_le_mul_right hex 2
      _ ≤ 2 * (μ γ₁ {p | a < gd γ₁ (ob γ₁ p)} +
            Kc * (∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ)) / θ) := by
          gcongr
      _ = _ := mul_add _ _ _
  calc ∑ b, ENNReal.ofReal (ω' (γ b)) * ((ν' (γ b)).prod volume)
        (F b ∩ {p | θ < crossCount (Finset.univ.filter (fun b' => γ b' = γ b)) Cr (ob (γ b) p)})
      = ∑ γ₁, ENNReal.ofReal (ω' γ₁) * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ Xs γ₁) := hfib
    _ ≤ ∑ γ₁, ENNReal.ofReal (ω' γ₁) * (2 * μ γ₁ {p | a < gd γ₁ (ob γ₁ p)} +
          2 * (Kc * (∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ)) / θ)) :=
        Finset.sum_le_sum fun γ₁ _ => mul_le_mul_right (hworld γ₁) _
    _ = 2 * ∑ γ₁, ENNReal.ofReal (ω' γ₁) * μ γ₁ {p | a < gd γ₁ (ob γ₁ p)} +
          2 * (Kc / θ) * ∑ γ₁, ENNReal.ofReal (ω' γ₁) * ∑ b ∈ S γ₁, μ γ₁ (F b ∩ univ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun γ₁ _ => ?_
        simp only [ENNReal.div_eq_inv_mul]
        ring
    _ ≤ 2 * X + 2 * (Kc / θ) * 2 := by
        refine add_le_add (mul_le_mul_right htyp 2) (mul_le_mul_right ?_ _)
        rw [← hfibm]; exact htotal
    _ = 2 * X + 4 * Kc / θ := by
        simp only [ENNReal.div_eq_inv_mul]
        ring

end Submission.Obl.k4_coarsened_outer_horizon_composition
