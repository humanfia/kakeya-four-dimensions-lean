import Submission.Lib.K4ChartLifting.NormAngular

/-!
# Weighted masses of normalized problems

`ChartSystem.normalized_chart_apply`: the selected law of a normalized world on any measurable
set, `(ν(A_c) q)⁻¹ (ν ⊗ vol)(F_c ∩ normInc⁻¹ X)`. `ChartSystem.normalized_weighted_apply`: with
the normalized world weights, `Σ_c ω'_c μ'_c(X_c) = Z⁻¹ Σ_c ω_{γ_c} (ν ⊗ vol)(F_c ∩ normInc_c⁻¹ X_c)`.
`ChartSystem.sum_world_event_le`: the selected sets of the charts of one world overlap at most
twice (`card_blocks_le`). **`ChartSystem.normalized_exceptional_le`**: if the normalized
exceptional sets pull back (almost everywhere) into exceptional sets `Y_γ` of the worlds, the
weighted normalized
exceptional mass is at most `2 Z⁻¹ Σ_γ ω_γ μ_γ(Y_γ)`; `ChartSystem.normZ_inv_le`: `Z⁻¹ ≤ κ`
when the charts' weighted selected mass is at least `κ⁻¹`. These transfer the typical density
bounds (pure and angular) of a problem to its normalization.
-/
namespace Submission.Lib.K4ChartLifting
open MeasureTheory

namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

/-- The normalized selected law of chart `c`, evaluated on any measurable set, in terms of
the chart's original selected law. -/
theorem normalized_chart_apply (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (c : Fin s.count) (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c))
    (hF : MeasurableSet (s.event c))
    (hsub : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    (X : Set Incidence) (hX : MeasurableSet X) :
    (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) X =
      (ν (s.world c) (s.assignment c) * ENNReal.ofReal (s.frameOf c).q)⁻¹ *
        ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X) := by
  have hq := s.frameOf_q_pos c
  have hsub' : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧
      p.2 ∈ Set.Icc (s.frameOf c).t₀ ((s.frameOf c).t₀ + (s.frameOf c).q) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsub p hp
    exact ⟨h1, (s.timeBlock_frameOf c) ▸ h2⟩
  have hlaw := (s.frameOf c).normalized_selected_law hq hD (ν (s.world c)) hA hF hsub'
  unfold normPrior normEventOf
  rw [hlaw, Measure.smul_apply, smul_eq_mul, Measure.map_apply (s.frameOf c).measurable_normInc hX,
    Measure.restrict_apply ((s.frameOf c).measurable_normInc hX), Set.inter_comm]

/-- **Weighted mass transfer**: the weighted mass of normalized worlds equals `Z⁻¹` times the
weighted original mass of the corresponding incidences of the charts. -/
theorem normalized_weighted_apply (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν)
    (hD : ∀ c, IsUnit (s.frame c).det) (hA : ∀ c, MeasurableSet (s.assignment c))
    (hF : ∀ c, MeasurableSet (s.event c))
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    (X : Fin s.count → Set Incidence) (hX : ∀ c, MeasurableSet (X c)) :
    ∑ c, ENNReal.ofReal (s.normWeight ω ν c) *
        (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) (X c) =
      ENNReal.ofReal (s.normZ ω ν)⁻¹ * ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X c) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [s.normalized_chart_apply ν c (hD c) (hA c) (hF c) (hsub c) (X c) (hX c)]
  have hq := s.frameOf_q_pos c
  set νA := ν (s.world c) (s.assignment c)
  set m := ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X c)
  have hq' : (s.frameOf c).q = 1 / (2 : ℝ) ^ T₀ := rfl
  by_cases h0 : νA = 0
  · have hm : m = 0 := by
      refine measure_mono_null (fun p hp => ?_) (show ((ν (s.world c)).prod volume)
        ({p : Incidence | p.1 ∈ s.assignment c}) = 0 from ?_)
      · exact (hsub c p hp.1).1
      · have : {p : Incidence | p.1 ∈ s.assignment c} = s.assignment c ×ˢ Set.univ := by
          ext p; simp
        rw [this, Measure.prod_prod]; exact mul_eq_zero_of_left h0 _
    rw [hm]; simp
  · have hνA : ENNReal.ofReal νA.toReal = νA := ENNReal.ofReal_toReal (measure_ne_top _ _)
    have hZi : 0 ≤ (s.normZ ω ν)⁻¹ := inv_nonneg.mpr hZ.le
    have hw : s.normWeight ω ν c =
        ω (s.world c) * (s.frameOf c).q * (s.normZ ω ν)⁻¹ * νA.toReal := by
      unfold normWeight; rw [hq']; field_simp; rfl
    have e1 : ENNReal.ofReal (s.normWeight ω ν c) = ENNReal.ofReal (ω (s.world c)) *
        ENNReal.ofReal (s.frameOf c).q * ENNReal.ofReal (s.normZ ω ν)⁻¹ * νA := by
      rw [hw, ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hω _) hq.le) hZi),
        ENNReal.ofReal_mul (mul_nonneg (hω _) hq.le), ENNReal.ofReal_mul (hω _), hνA]
    have hq0 : ENNReal.ofReal (s.frameOf c).q ≠ 0 := by simpa using hq
    have e2 : (νA * ENNReal.ofReal (s.frameOf c).q) * (νA * ENNReal.ofReal (s.frameOf c).q)⁻¹
        = 1 := ENNReal.mul_inv_cancel (mul_ne_zero h0 hq0)
          (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
    rw [e1]
    calc ENNReal.ofReal (ω (s.world c)) * ENNReal.ofReal (s.frameOf c).q *
          ENNReal.ofReal (s.normZ ω ν)⁻¹ * νA * ((νA * ENNReal.ofReal (s.frameOf c).q)⁻¹ * m)
        = ENNReal.ofReal (s.normZ ω ν)⁻¹ * (ENNReal.ofReal (ω (s.world c)) * m) *
            ((νA * ENNReal.ofReal (s.frameOf c).q) *
              (νA * ENNReal.ofReal (s.frameOf c).q)⁻¹) := by ring
      _ = _ := by rw [e2, mul_one]

/-- A time lies in at most two closed dyadic blocks. -/
theorem card_blocks_le (T : ℕ) (t : ℝ) [DecidablePred fun j : Fin (2 ^ T) => t ∈ timeBlock T j] :
    (Finset.univ.filter (fun j : Fin (2 ^ T) => t ∈ timeBlock T j)).card ≤ 2 := by
  set n := ⌊t * (2 : ℝ) ^ T⌋
  have hsub : Finset.univ.filter (fun j : Fin (2 ^ T) => t ∈ timeBlock T j) ⊆
      Finset.univ.filter (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ) = n ∨ ((j : ℕ) : ℤ) = n - 1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨h1, h2⟩ := hj
    have hp : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    rw [div_le_iff₀ hp] at h1
    rw [le_div_iff₀ hp] at h2
    have a1 : ((j : ℕ) : ℤ) ≤ n := Int.le_floor.mpr (by push_cast; linarith)
    have a2 : n ≤ ((j : ℕ) : ℤ) + 1 := by
      have := Int.floor_le (t * (2 : ℝ) ^ T)
      have : ((n : ℤ) : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by linarith
      exact_mod_cast this
    omega
  refine (Finset.card_le_card hsub).trans ?_
  calc (Finset.univ.filter (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ) = n ∨
        ((j : ℕ) : ℤ) = n - 1)).card
      ≤ (Finset.univ.filter (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ) = n)).card +
        (Finset.univ.filter (fun j : Fin (2 ^ T) => ((j : ℕ) : ℤ) = n - 1)).card := by
        rw [Finset.filter_or]; exact Finset.card_union_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · refine Finset.card_le_one.mpr fun a ha b hb => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)
        · refine Finset.card_le_one.mpr fun a ha b hb => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact Fin.ext (by omega)

/-- **Overlap of the charts of one world**: an incidence lies in the selected sets of at most
two charts of each world (same block ⇒ disjoint assignments; at most two closed blocks). -/
theorem sum_world_event_le (μ : Measure Incidence) (E : Fin W → Set Incidence) (γ : Fin W)
    (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    (Y : Set Incidence) (hY : MeasurableSet Y) (hEY : MeasurableSet (E γ ∩ Y)) :
    ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ), μ (s.event c ∩ Y) ≤ 2 * μ (E γ ∩ Y) := by
  classical
  set S := Finset.univ.filter (fun c => s.world c = γ)
  have hpt : ∀ p, ∑ c ∈ S, (s.event c ∩ Y).indicator (1 : Incidence → ENNReal) p ≤
      2 * (E γ ∩ Y).indicator 1 p := by
    intro p
    have hsum : ∑ c ∈ S, (s.event c ∩ Y).indicator (1 : Incidence → ENNReal) p =
        ((S.filter (fun c => p ∈ s.event c ∩ Y)).card : ENNReal) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : p ∈ s.event c ∩ Y <;> simp [h]
    rw [hsum]
    by_cases hp : p ∈ E γ ∩ Y
    · rw [Set.indicator_of_mem hp, Pi.one_apply, mul_one]
      have hcard : (S.filter (fun c => p ∈ s.event c ∩ Y)).card ≤
          (Finset.univ.filter (fun j : Fin (2 ^ T₀) => p.2 ∈ timeBlock T₀ j)).card := by
        refine Finset.card_le_card_of_injOn (fun c => s.block c) ?_ ?_
        · intro c hc
          simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hc ⊢
          exact (hsub c p hc.2.1).2.2
        · intro c hc c' hc' hbl
          simp only [S, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hc hc'
          by_contra hne
          have hd := hdisj c c' hne (hc.1.trans hc'.1.symm) hbl
          exact Set.disjoint_left.mp hd (hsub c p hc.2.1).2.1 (hsub c' p hc'.2.1).2.1
      have h2 := card_blocks_le T₀ p.2
      have : ((S.filter (fun c => p ∈ s.event c ∩ Y)).card : ENNReal) ≤ (2 : ℕ) := by
        exact_mod_cast hcard.trans h2
      simpa using this
    · rw [Set.indicator_of_notMem hp, mul_zero]
      have : S.filter (fun c => p ∈ s.event c ∩ Y) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun c hc hpc => hp ⟨?_, hpc.2⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [← hc]; exact (hsub c p hpc.1).1
      rw [this]; simp
  calc ∑ c ∈ S, μ (s.event c ∩ Y)
      = ∑ c ∈ S, ∫⁻ p, (s.event c ∩ Y).indicator 1 p ∂μ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [lintegral_indicator_one ((hF c).inter hY)]
    _ = ∫⁻ p, ∑ c ∈ S, (s.event c ∩ Y).indicator 1 p ∂μ := by
        rw [lintegral_finsetSum]
        intro c _
        exact measurable_one.indicator ((hF c).inter hY)
    _ ≤ ∫⁻ p, 2 * (E γ ∩ Y).indicator 1 p ∂μ := lintegral_mono hpt
    _ = 2 * μ (E γ ∩ Y) := by
        rw [lintegral_const_mul _ (measurable_one.indicator hEY), lintegral_indicator_one hEY]

/-- **Exceptional mass transfer**: if the normalized exceptional set of each chart pulls back
into an exceptional set `Y` of its world, the weighted normalized exceptional mass is at most
`2 Z⁻¹` times the weighted original exceptional mass. -/
theorem normalized_exceptional_le (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν)
    (E : Fin W → Set Incidence) (hE : ∀ γ, MeasurableSet (E γ))
    (hD : ∀ c, IsUnit (s.frame c).det) (hA : ∀ c, MeasurableSet (s.assignment c))
    (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    (X : Fin s.count → Set Incidence) (hX : ∀ c, MeasurableSet (X c))
    (Y : Fin W → Set Incidence) (hY : ∀ γ, MeasurableSet (Y γ))
    (hXY : ∀ c, ∀ᵐ p ∂((ν (s.world c)).prod volume), p ∈ s.event c →
      (s.frameOf c).normInc p ∈ X c → p ∈ Y (s.world c)) :
    ∑ c, ENNReal.ofReal (s.normWeight ω ν c) *
        (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) (X c) ≤
      ENNReal.ofReal (s.normZ ω ν)⁻¹ * (2 * ∑ γ, ENNReal.ofReal (ω γ) *
        (((ν γ).prod volume).restrict (E γ)) (Y γ)) := by
  classical
  rw [s.normalized_weighted_apply ω ν hω hZ hD hA hF (fun c p hp => (hsub c p hp).2) X hX]
  refine mul_le_mul_right ?_ _
  calc ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X c)
      ≤ ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c)) := by
        refine Finset.sum_le_sum fun c _ => mul_le_mul_right (measure_mono_ae ?_) _
        filter_upwards [hXY c] with p hp hpX
        exact ⟨hpX.1, hp hpX.1 hpX.2⟩
    _ = ∑ γ, ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ), ENNReal.ofReal (ω γ) *
        ((ν γ).prod volume) (s.event c ∩ Y γ) := by
        rw [← Finset.sum_fiberwise Finset.univ s.world]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun c hc => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [hc]
    _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * (2 * ((ν γ).prod volume) (E γ ∩ Y γ)) := by
        gcongr with γ
        rw [← Finset.mul_sum]
        gcongr
        exact s.sum_world_event_le _ E γ hF hdisj hsub (Y γ) (hY γ) ((hE γ).inter (hY γ))
    _ = 2 * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) (Y γ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [Measure.restrict_apply (hY γ), Set.inter_comm]
        ring

/-- The selected mass of the charts bounds the normalizing constant from below. -/
theorem mass_le_normZ (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ)
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c)) :
    ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c) ≤
      ENNReal.ofReal (s.normZ ω ν) := by
  unfold normZ
  rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hω _) (by positivity))]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [ENNReal.ofReal_mul (hω _)]
  refine mul_le_mul_right ?_ _
  have hsubset : s.event c ⊆ s.assignment c ×ˢ timeBlock T₀ (s.block c) :=
    fun p hp => hsub c p hp
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  calc ((ν (s.world c)).prod volume) (s.event c)
      ≤ ((ν (s.world c)).prod volume) (s.assignment c ×ˢ timeBlock T₀ (s.block c)) :=
        measure_mono hsubset
    _ = ν (s.world c) (s.assignment c) * ENNReal.ofReal (1 / (2 : ℝ) ^ T₀) := by
        rw [Measure.prod_prod, timeBlock, Real.volume_Icc]
        congr 2
        field_simp
        ring
    _ = ENNReal.ofReal ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) := by
        rw [show (ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀ =
          (ν (s.world c) (s.assignment c)).toReal * (1 / (2 : ℝ) ^ T₀) by ring,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The inverse normalizing constant is at most the slack of the atlas mass condition. -/
theorem normZ_inv_le (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ)
    (hsub : ∀ c, ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    {κ : ℝ} (hκ : 0 < κ)
    (htotal : ENNReal.ofReal κ⁻¹ ≤
      ∑ c, ENNReal.ofReal (ω (s.world c)) * ((ν (s.world c)).prod volume) (s.event c)) :
    0 < s.normZ ω ν ∧ (s.normZ ω ν)⁻¹ ≤ κ := by
  have h := htotal.trans (s.mass_le_normZ ω ν hω hsub)
  have hZ : κ⁻¹ ≤ s.normZ ω ν := by
    rw [ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · exact h
    · exact absurd h (not_le.mpr (inv_pos.mpr hκ))
  have hZpos : 0 < s.normZ ω ν := lt_of_lt_of_le (inv_pos.mpr hκ) hZ
  exact ⟨hZpos, by rw [inv_le_comm₀ hZpos hκ]; exact hZ⟩

end ChartSystem
end Submission.Lib.K4ChartLifting
