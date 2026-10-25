import Submission.Lib.K4ChartLifting.NormCompare

/-!
# The terminal lower comparison of normalized densities

`exists_density_of_le`: a finite law below a density law has a density.
`ChartSystem.weighted_event_le`: the weighted selected mass of the charts inside sets `Y_γ` of
their worlds is at most twice the weighted mass of the `Y_γ`.
`ChartSystem.normalized_density_ge`: almost surely the normalized density of a chart at the
normalized sample is at least `J_c/ν_c` times the chart's own original density at the composed
depth (the exact transform (2.15), read from below).
**`ChartSystem.normalized_terminal_lower`** (paper Lemma 2.13 with Lemma 2.3, terminal half):
if each chart is listed at the terminal observation of each of its incidences, by measurable
lists of at most `κ` charts, the weighted normalized mass where `g'_c < (J_c/ν_c) ε V` at a
depth `r'` with `alignedDepth N r r' ≤ L` is at most
`Z⁻¹ (2 Σ_γ ω_γ μ_γ{g_L < V} + ε κ Σ_γ ω_γ μ_γ(univ))`.
-/
namespace Submission.Lib.K4ChartLifting
open MeasureTheory

/-- A finite law below a density law has a density. -/
theorem exists_density_of_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) [SigmaFinite ρ]
    (l : Measure Y) [IsFiniteMeasure l] (g : Y → ENNReal) (hle : l ≤ ρ.withDensity g) :
    ∃ h : Y → ENNReal, Measurable h ∧ l = ρ.withDensity h :=
  ⟨l.rnDeriv ρ, Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq _ _ ((Measure.absolutelyContinuous_of_le hle).trans
      (withDensity_absolutelyContinuous _ _))).symm⟩

namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

theorem event_measure_ne_top (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (c : Fin s.count)
    (hsub : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c)) :
    ((ν (s.world c)).prod volume) (s.event c) ≠ ⊤ := by
  have hsubset : s.event c ⊆ s.assignment c ×ˢ timeBlock T₀ (s.block c) :=
    fun p hp => hsub p hp
  refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
  rw [Measure.prod_prod, timeBlock, Real.volume_Icc]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

/-- The weighted selected mass of the charts inside worlds' sets is at most twice the weighted
mass of the worlds' sets. -/
theorem weighted_event_le (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (hE : ∀ γ, MeasurableSet (E γ))
    (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    (Y : Fin W → Set Incidence) (hY : ∀ γ, MeasurableSet (Y γ)) :
    ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c)) ≤
      2 * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) (Y γ) := by
  classical
  calc ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c))
      = ∑ γ, ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ), ENNReal.ofReal (ω γ) *
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

/-- A normalized chart's density is at least `J_c/ν_c` times its own original density at the
composed depth, almost surely at the normalized sample. -/
theorem normalized_density_ge (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (B : Fin W → ℝ) (c : Fin s.count)
    (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c))
    (hF : MeasurableSet (s.event c))
    (hsub : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ timeBlock T₀ (s.block c))
    {N r r' : ℝ} (hN : 1 < N)
    (H : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hH : Measurable H)
    (hlawH : Measure.map (obs (B (s.world c)) (dyWidth N (alignedDepth N r r')))
      (((ν (s.world c)).prod volume).restrict (s.event c)) =
        (volume.prod Measure.count).withDensity H)
    (g' : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal)
    (hlaw' : Measure.map (obs (s.normScale B (dyWidth N r) c) (dyWidth N r'))
      (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) =
        (volume.prod Measure.count).withDensity g') :
    ∀ᵐ p ∂(((ν (s.world c)).prod volume).restrict (s.event c)),
      s.normFactor ν c * H (obs (B (s.world c)) (dyWidth N (alignedDepth N r r')) p) ≤
        g' (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') ((s.frameOf c).normInc p)) := by
  set F := s.frameOf c
  have hq := s.frameOf_q_pos c
  have hδ : dyWidth N r ≠ 0 := by unfold dyWidth; positivity
  have hmul : dyWidth N r * dyWidth N r' = dyWidth N (alignedDepth N r r') := dyWidth_mul N r r' hN
  set ρ := alignedDepth N r r'
  set ref := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)
  set e := F.obsEquiv hq.ne' hD
  have hsub' : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hsub p hp
    exact ⟨h1, (s.timeBlock_frameOf c) ▸ h2⟩
  have hlawH' : Measure.map (obs (B (s.world c)) (dyWidth N r * dyWidth N r'))
      (((ν (s.world c)).prod volume).restrict (s.event c)) = ref.withDensity H := by
    rw [hmul]; exact hlawH
  have hdens := F.normalized_obs_density hq hD (ν (s.world c)) hA hF hsub' (B (s.world c))
    (dyWidth N r) (dyWidth N r') hδ H hH hlawH'
  have heq : ref.withDensity (fun z => s.normFactor ν c * H (e.symm z)) = ref.withDensity g' := by
    rw [← hlaw']
    unfold normScale normPrior normEventOf
    rw [hdens]
    congr 1
    funext z
    unfold normFactor
    ring
  have hae1 : ∀ᵐ z ∂ref, s.normFactor ν c * H (e.symm z) ≤ g' z :=
    density_le_of_le ref (measurable_const.mul (hH.comp e.symm.measurable)) heq.le
  have hae2 : ∀ᵐ z ∂ref, s.normFactor ν c * H z ≤ g' (e z) := by
    have hpre : ref (e ⁻¹' {z | ¬ s.normFactor ν c * H (e.symm z) ≤ g' z}) = 0 := by
      have := e.map_apply (μ := ref) {z | ¬ s.normFactor ν c * H (e.symm z) ≤ g' z}
      rw [F.map_obsEquiv hq.ne' hD, Measure.smul_apply, ae_iff.mp hae1, smul_zero] at this
      exact this.symm
    refine ae_iff.mpr (measure_mono_null (fun z hz => ?_) hpre)
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, MeasurableEquiv.symm_apply_apply] at hz ⊢
    exact hz
  have hac : Measure.map (obs (B (s.world c)) (dyWidth N ρ))
      (((ν (s.world c)).prod volume).restrict (s.event c)) ≪ ref := by
    rw [hlawH]; exact withDensity_absolutelyContinuous _ _
  have hae3 := ae_of_ae_map (measurable_obs (B (s.world c)) (dyWidth N ρ)).aemeasurable (hac hae2)
  filter_upwards [hae3] with p hp
  have hobs : obs (s.normScale B (dyWidth N r) c) (dyWidth N r') (F.normInc p) =
      e (obs (B (s.world c)) (dyWidth N ρ) p) := by
    unfold normScale
    rw [F.obs_normInc hq.ne' (B (s.world c)) (dyWidth N r) (dyWidth N r') hδ p, hmul]
    rfl
  rw [hobs]
  exact hp

/-- **Terminal lower comparison** (paper Lemma 2.13 with (2.15) and Lemma 2.3, lower half):
if each chart is listed at the terminal observation of its incidences, by lists of at most `κ`
charts, then the weighted normalized mass where a chart's density at depth `r'` (with composed
depth `alignedDepth N r r' ≤ L`) falls below `(J_c/ν_c) ε V` is at most `Z⁻¹` times twice the
weighted original mass where the terminal density falls below `V`, plus `ε κ` times the total
weighted mass. -/
theorem normalized_terminal_lower (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν)
    (E : Fin W → Set Incidence) (hE : ∀ γ, MeasurableSet (E γ)) (B : Fin W → ℝ)
    (hD : ∀ c, IsUnit (s.frame c).det) (hA : ∀ c, MeasurableSet (s.assignment c))
    (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    {N r r' L : ℝ} (hN : 1 < N) (hL : alignedDepth N r r' ≤ L)
    (g G : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg : ∀ γ, Measurable (g γ))
    (hlawL : ∀ γ, Measure.map (obs (B γ) (dyWidth N L)) (((ν γ).prod volume).restrict (E γ)) =
      (volume.prod Measure.count).withDensity (g γ))
    (hlawρ : ∀ γ, Measure.map (obs (B γ) (dyWidth N (alignedDepth N r r')))
      (((ν γ).prod volume).restrict (E γ)) = (volume.prod Measure.count).withDensity (G γ))
    (g' : Fin s.count → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal)
    (hlaw' : ∀ c, Measure.map (obs (s.normScale B (dyWidth N r) c) (dyWidth N r'))
      (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) =
        (volume.prod Measure.count).withDensity (g' c))
    (hg' : ∀ c, Measurable (g' c))
    (lst : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → Finset (Fin s.count)) (κ : ℕ)
    (hlst : ∀ γ y, (lst γ y).card ≤ κ)
    (hlstm : ∀ c, MeasurableSet {y | c ∈ lst (s.world c) y})
    (hmem : ∀ c, ∀ p ∈ s.event c, c ∈ lst (s.world c) (obs (B (s.world c)) (dyWidth N L) p))
    (ε V : ENNReal) :
    ∑ c, ENNReal.ofReal (s.normWeight ω ν c) *
        (((s.normPrior ν c).prod volume).restrict (s.normEventOf c))
          {z | g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') z) <
            s.normFactor ν c * (ε * V)} ≤
      ENNReal.ofReal (s.normZ ω ν)⁻¹ * (2 * ∑ γ, ENNReal.ofReal (ω γ) *
        (((ν γ).prod volume).restrict (E γ)) {p | g γ (obs (B γ) (dyWidth N L) p) < V} +
        ε * κ * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) Set.univ) := by
  classical
  set ref := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)
  set ρ := alignedDepth N r r'
  have hfin : ∀ c, IsFiniteMeasure (((ν (s.world c)).prod volume).restrict (s.event c)) :=
    fun c => isFiniteMeasure_restrict.mpr
      (s.event_measure_ne_top ν c (fun p hp => (hsub c p hp).2))
  have hle : ∀ c (a : ℝ) (k : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal),
      Measure.map (obs (B (s.world c)) a) (((ν (s.world c)).prod volume).restrict (E (s.world c)))
        = ref.withDensity (k (s.world c)) →
      Measure.map (obs (B (s.world c)) a) (((ν (s.world c)).prod volume).restrict (s.event c)) ≤
        ref.withDensity (k (s.world c)) := by
    intro c a k hk
    rw [← hk]
    exact Measure.map_mono (Measure.restrict_mono (fun p hp => (hsub c p hp).1) le_rfl)
      (measurable_obs _ _)
  have hex : ∀ c (a : ℝ) (k : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal),
      Measure.map (obs (B (s.world c)) a) (((ν (s.world c)).prod volume).restrict (E (s.world c)))
        = ref.withDensity (k (s.world c)) →
      ∃ h : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal, Measurable h ∧
        Measure.map (obs (B (s.world c)) a) (((ν (s.world c)).prod volume).restrict (s.event c))
          = ref.withDensity h := by
    intro c a k hk
    have := hfin c
    exact exists_density_of_le ref _ (k (s.world c)) (hle c a k hk)
  choose h hh hlawh using fun c => hex c (dyWidth N L) g (hlawL _)
  choose H hH hlawH using fun c => hex c (dyWidth N ρ) G (hlawρ _)
  -- the a.e. lower bound at the normalized sample
  have hlow : ∀ c, ∀ᵐ p ∂(((ν (s.world c)).prod volume).restrict (s.event c)),
      s.normFactor ν c * h c (obs (B (s.world c)) (dyWidth N L) p) ≤
        g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') ((s.frameOf c).normInc p)) := by
    intro c
    have h1 := s.normalized_density_ge ν B c (hD c) (hA c) (hF c)
      (fun p hp => (hsub c p hp).2) hN (H c) (hH c) (hlawH c) (g' c) (hlaw' c)
    have h2 := density_depth_le (((ν (s.world c)).prod volume).restrict (s.event c))
      (B (s.world c)) hN.le hL (H c) (h c) (hH c) (hh c) (hlawH c) (hlawh c)
    filter_upwards [h1, h2] with p hp1 hp2
    exact (mul_le_mul_right hp2 _).trans hp1
  -- the low-density sets of the charts
  set Λ : Fin s.count → Set Incidence := fun c =>
    obs (B (s.world c)) (dyWidth N L) ⁻¹' {y | h c y < ε * g (s.world c) y}
  set Y : Fin W → Set Incidence := fun γ => {p | g γ (obs (B γ) (dyWidth N L) p) < V}
  have hΛ : ∀ c, MeasurableSet (Λ c) := fun c =>
    measurable_obs _ _ (measurableSet_lt (hh c) (measurable_const.mul (hg _)))
  have hY : ∀ γ, MeasurableSet (Y γ) := fun γ =>
    measurableSet_lt ((hg γ).comp (measurable_obs _ _)) measurable_const
  set X : Fin s.count → Set Incidence := fun c =>
    {z | g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') z) <
      s.normFactor ν c * (ε * V)}
  have hX : ∀ c, MeasurableSet (X c) := fun c =>
    measurableSet_lt ((hg' c).comp (measurable_obs _ _)) measurable_const
  have hchart : ∀ c, ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X c)
      ≤ ((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c)) +
        ((ν (s.world c)).prod volume) (s.event c ∩ Λ c) := by
    intro c
    have e1 : ∀ S, MeasurableSet S → ((ν (s.world c)).prod volume) (s.event c ∩ S) =
        (((ν (s.world c)).prod volume).restrict (s.event c)) S := fun S hS => by
      rw [Measure.restrict_apply hS, Set.inter_comm]
    rw [e1 _ ((s.frameOf c).measurable_normInc (hX c)), e1 _ (hY _), e1 _ (hΛ c)]
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hlow c] with p hp hpX
    have hpX' : g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') ((s.frameOf c).normInc p))
        < s.normFactor ν c * (ε * V) := hpX
    have hlt := lt_of_le_of_lt hp hpX'
    have hlt2 : h c (obs (B (s.world c)) (dyWidth N L) p) < ε * V := by
      by_contra hcon
      exact absurd (mul_le_mul_right (not_lt.mp hcon) (s.normFactor ν c)) (not_le.mpr hlt)
    by_cases hgV : g (s.world c) (obs (B (s.world c)) (dyWidth N L) p) < V
    · exact Or.inl hgV
    · right
      show h c (obs (B (s.world c)) (dyWidth N L) p) < ε * g (s.world c) (obs (B (s.world c)) (dyWidth N L) p)
      exact lt_of_lt_of_le hlt2 (mul_le_mul_right (not_lt.mp hgV) ε)
  -- the list refinement in each world
  have hΛint : ∀ c, ((ν (s.world c)).prod volume) (s.event c ∩ Λ c) =
      ∫⁻ y in {y | h c y < ε * g (s.world c) y}, h c y ∂ref := by
    intro c
    have hS : MeasurableSet {y | h c y < ε * g (s.world c) y} :=
      measurableSet_lt (hh c) (measurable_const.mul (hg _))
    rw [← withDensity_apply _ hS, ← hlawh c, Measure.map_apply (measurable_obs _ _) hS,
      Measure.restrict_apply (measurable_obs _ _ hS), Set.inter_comm]
  have hworld : ∀ γ, ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ),
      ∫⁻ y in {y | h c y < ε * g γ y}, h c y ∂ref ≤ ε * κ * ∫⁻ y, g γ y ∂ref := by
    intro γ
    set h' : Fin s.count → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal :=
      fun c => if s.world c = γ then h c else 0
    have hh' : ∀ c, Measurable (h' c) := by
      intro c; by_cases hc : s.world c = γ
      · simp only [h', hc, ite_true]; exact hh c
      · simp only [h', hc, ite_false]; exact measurable_const
    have hsupp : ∀ c, ∀ᵐ y ∂ref, c ∉ lst γ y → h' c y = 0 := by
      intro c
      by_cases hc : s.world c = γ
      · have hv := density_vanishes_off_lists ref ((ν (s.world c)).prod volume)
          (measurable_obs (B (s.world c)) (dyWidth N L)) (s.event c) c (lst (s.world c))
          (hlstm c) (hmem c) (hh c) (hlawh c)
        rw [hc] at hv
        filter_upwards [hv] with y hy hcy
        simp only [h', hc, ite_true]
        exact hy hcy
      · exact Filter.Eventually.of_forall fun y _ => by simp [h', hc]
    have href := refinement_lists ref (g γ) h' hh' (hg γ) (lst γ) κ (hlst γ) hsupp ε
    calc ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ),
          ∫⁻ y in {y | h c y < ε * g γ y}, h c y ∂ref
        = ∑ c, ∫⁻ y in {y | h' c y < ε * g γ y}, h' c y ∂ref := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases hc : s.world c = γ
          · simp only [h', hc, ite_true]
          · simp [h', hc]
      _ ≤ _ := href
  have hlist : ∑ c, ENNReal.ofReal (ω (s.world c)) *
      ((ν (s.world c)).prod volume) (s.event c ∩ Λ c) ≤
        ε * κ * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) Set.univ := by
    calc ∑ c, ENNReal.ofReal (ω (s.world c)) *
          ((ν (s.world c)).prod volume) (s.event c ∩ Λ c)
        = ∑ γ, ∑ c ∈ Finset.univ.filter (fun c => s.world c = γ), ENNReal.ofReal (ω γ) *
          ∫⁻ y in {y | h c y < ε * g γ y}, h c y ∂ref := by
          rw [← Finset.sum_fiberwise Finset.univ s.world]
          refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun c hc => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          rw [hΛint c, hc]
      _ ≤ ∑ γ, ENNReal.ofReal (ω γ) * (ε * κ * ∫⁻ y, g γ y ∂ref) := by
          gcongr with γ
          rw [← Finset.mul_sum]
          exact mul_le_mul_right (hworld γ) _
      _ = ε * κ * ∑ γ, ENNReal.ofReal (ω γ) * (((ν γ).prod volume).restrict (E γ)) Set.univ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          have : ∫⁻ y, g γ y ∂ref = (((ν γ).prod volume).restrict (E γ)) Set.univ := by
            rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hlawL γ,
              Measure.map_apply (measurable_obs _ _) MeasurableSet.univ, Set.preimage_univ]
          rw [this]; ring
  rw [s.normalized_weighted_apply ω ν hω hZ hD hA hF (fun c p hp => (hsub c p hp).2) X hX]
  refine mul_le_mul_right ?_ _
  calc ∑ c, ENNReal.ofReal (ω (s.world c)) *
        ((ν (s.world c)).prod volume) (s.event c ∩ (s.frameOf c).normInc ⁻¹' X c)
      ≤ ∑ c, ENNReal.ofReal (ω (s.world c)) *
        (((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c)) +
          ((ν (s.world c)).prod volume) (s.event c ∩ Λ c)) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_right (hchart c) _
    _ = ∑ c, ENNReal.ofReal (ω (s.world c)) *
          ((ν (s.world c)).prod volume) (s.event c ∩ Y (s.world c)) +
        ∑ c, ENNReal.ofReal (ω (s.world c)) *
          ((ν (s.world c)).prod volume) (s.event c ∩ Λ c) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ ≤ _ := add_le_add (s.weighted_event_le ω ν E hE hF hdisj hsub Y hY) hlist

end ChartSystem
end Submission.Lib.K4ChartLifting
