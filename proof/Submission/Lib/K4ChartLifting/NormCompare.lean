import Submission.Lib.K4ChartLifting.NormMass

/-!
# Depth monotonicity and the upper comparison of normalized densities

`density_fine_le_coarse`: when a fine observation and its coarsening `(y, n) ↦ (y, n / m)` both
have densities, almost surely the fine density at the sample is at most the coarse density at
the sample. For the frozen observations (`obs_coarsen`, bins of depth `s ≤ ρ` nest with ratio
`binRatio N s ρ`): `density_depth_le` and `mass_density_gt_le_of_le` (upper typical bounds pass
to finer depths, lower ones to coarser depths; this sandwiches the composed depths
`alignedDepth N r r'` between fixed ones).

`ChartSystem.normFactor` is `J_c / ν_c = (ν(A_c) q)⁻¹ |det obsMatrix|⁻¹`.
`ChartSystem.normalized_density_le`: almost surely the normalized density of a chart at the
normalized sample is at most `J_c/ν_c` times the world's density at the composed depth.
**`ChartSystem.normalized_upper_comparison`** (the intermediate upper comparison of paper
Lemma 2.13): the weighted normalized mass where `g'_c > (J_c/ν_c) U` at depth `r'` is at most
`2 Z⁻¹` times the weighted original mass where `g > U` at any fixed depth
`σ ≤ alignedDepth N r r'`.
-/
open MeasureTheory

namespace Submission.Lib.K4ChartLifting

theorem withDensity_prod_singleton {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    (f : X × ℤ → ENNReal) (hf : Measurable f) (T : Set X) (hT : MeasurableSet T) (j : ℤ) :
    ((ν.prod Measure.count).withDensity f) (T ×ˢ {j}) = ∫⁻ y in T, f (y, j) ∂ν := by
  rw [withDensity_apply _ (hT.prod (measurableSet_singleton j)),
    setLIntegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [lintegral_singleton, Measure.count_singleton, mul_one]

/-- **Fine densities are below coarse ones at the sample**: if a fine observation `φ` and its
coarsening `(y, n) ↦ (y, n / m)` both have densities, then almost surely the fine density at
the sampled fine observation is at most the coarse density at the sampled coarse one. -/
theorem density_fine_le_coarse {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [SigmaFinite ν] (μ : Measure Ω) (φ : Ω → X × ℤ) (hφ : Measurable φ)
    (m : ℕ) (g g' : X × ℤ → ENNReal) (hg : Measurable g) (hg' : Measurable g')
    (hfine : Measure.map φ μ = (ν.prod Measure.count).withDensity g)
    (hcoarse : Measure.map (fun p => ((φ p).1, (φ p).2 / (m : ℤ))) μ =
      (ν.prod Measure.count).withDensity g') :
    ∀ᵐ p ∂μ, g (φ p) ≤ g' ((φ p).1, (φ p).2 / (m : ℤ)) := by
  have hc : Measurable fun z : X × ℤ => (z.1, z.2 / (m : ℤ)) :=
    measurable_fst.prodMk ((measurable_of_countable (fun j : ℤ => j / (m : ℤ))).comp measurable_snd)
  have hφc : Measurable fun p => ((φ p).1, (φ p).2 / (m : ℤ)) := hc.comp hφ
  have key : ∀ j : ℤ, ∀ᵐ y ∂ν, g (y, j) ≤ g' (y, j / (m : ℤ)) := by
    intro j
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (hg.comp (measurable_id.prodMk measurable_const)) fun T hT _ => ?_
    rw [← withDensity_prod_singleton ν g hg T hT j,
      ← withDensity_prod_singleton ν g' hg' T hT (j / (m : ℤ)), ← hfine, ← hcoarse,
      Measure.map_apply hφ (hT.prod (measurableSet_singleton _)),
      Measure.map_apply hφc (hT.prod (measurableSet_singleton _))]
    refine measure_mono fun p hp => ?_
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff] at hp ⊢
    exact ⟨hp.1, by rw [hp.2]⟩
  have hnull : (ν.prod Measure.count) {z : X × ℤ | ¬ g z ≤ g' (z.1, z.2 / (m : ℤ))} = 0 := by
    have hsub : {z : X × ℤ | ¬ g z ≤ g' (z.1, z.2 / (m : ℤ))} ⊆
        ⋃ j : ℤ, {y | ¬ g (y, j) ≤ g' (y, j / (m : ℤ))} ×ˢ {j} := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨z.2, ⟨hz, rfl⟩⟩
    refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
    rw [Measure.prod_prod, Measure.count_singleton, mul_one]
    exact ae_iff.mp (key j)
  have hac : Measure.map φ μ ≪ ν.prod Measure.count := by
    rw [hfine]; exact withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂(Measure.map φ μ), g z ≤ g' (z.1, z.2 / (m : ℤ)) :=
    hac (ae_iff.mp (ae_iff.mpr hnull))
  exact ae_of_ae_map hφ.aemeasurable hae

/-- The number of fine dyadic bins in a coarse one, from depth `s` to depth `ρ`. -/
noncomputable def binRatio (N s ρ : ℝ) : ℕ :=
  2 ^ (⌊ρ * Real.log N / Real.log 2⌋ - ⌊s * Real.log N / Real.log 2⌋).toNat

theorem dyWidth_eq_mul_binRatio {N s ρ : ℝ} (hN : 1 ≤ N) (hsρ : s ≤ ρ) :
    dyWidth N s = dyWidth N ρ * (binRatio N s ρ : ℝ) := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : ⌊s * Real.log N / Real.log 2⌋ ≤ ⌊ρ * Real.log N / Real.log 2⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsρ hlog) hlog2.le)
  unfold dyWidth binRatio
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hmono),
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- Coarse observations are a function of fine ones: bins divide by the bin ratio. -/
theorem obs_coarsen (B : ℝ) {N s ρ : ℝ} (hN : 1 ≤ N) (hsρ : s ≤ ρ) (p : Incidence) :
    obs B (dyWidth N s) p = ((obs B (dyWidth N ρ) p).1,
      (obs B (dyWidth N ρ) p).2 / ((binRatio N s ρ : ℕ) : ℤ)) := by
  unfold obs
  rw [dyWidth_eq_mul_binRatio hN hsρ, ← div_div, Int.floor_div_natCast]

/-- **Depth monotonicity of densities at the sample**: for `s ≤ ρ`, almost surely the density
at depth `ρ` at the sampled observation is at most the density at depth `s`. -/
theorem density_depth_le (μ : Measure Incidence) (B : ℝ) {N s ρ : ℝ} (hN : 1 ≤ N)
    (hsρ : s ≤ ρ) (gs gρ : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hgs : Measurable gs)
    (hgρ : Measurable gρ)
    (hs : Measure.map (obs B (dyWidth N s)) μ = (volume.prod Measure.count).withDensity gs)
    (hρ : Measure.map (obs B (dyWidth N ρ)) μ = (volume.prod Measure.count).withDensity gρ) :
    ∀ᵐ p ∂μ, gρ (obs B (dyWidth N ρ) p) ≤ gs (obs B (dyWidth N s) p) := by
  have hfun : obs B (dyWidth N s) = fun p => ((obs B (dyWidth N ρ) p).1,
      (obs B (dyWidth N ρ) p).2 / ((binRatio N s ρ : ℕ) : ℤ)) :=
    funext fun p => obs_coarsen B hN hsρ p
  rw [hfun] at hs ⊢
  exact density_fine_le_coarse volume μ _ (measurable_obs B _) (binRatio N s ρ) gρ gs hgρ hgs
    hρ hs

/-- Upper typical bounds pass to finer depths, lower ones to coarser depths. -/
theorem mass_density_gt_le_of_le (μ : Measure Incidence) (B : ℝ) {N s ρ : ℝ} (hN : 1 ≤ N)
    (hsρ : s ≤ ρ) (gs gρ : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hgs : Measurable gs)
    (hgρ : Measurable gρ)
    (hs : Measure.map (obs B (dyWidth N s)) μ = (volume.prod Measure.count).withDensity gs)
    (hρ : Measure.map (obs B (dyWidth N ρ)) μ = (volume.prod Measure.count).withDensity gρ)
    (U V : ENNReal) :
    μ {p | U < gρ (obs B (dyWidth N ρ) p)} ≤ μ {p | U < gs (obs B (dyWidth N s) p)} ∧
      μ {p | gs (obs B (dyWidth N s) p) < V} ≤ μ {p | gρ (obs B (dyWidth N ρ) p) < V} := by
  have h := density_depth_le μ B hN hsρ gs gρ hgs hgρ hs hρ
  constructor
  · exact measure_mono_ae (h.mono fun p hp hU => lt_of_lt_of_le hU hp)
  · exact measure_mono_ae (h.mono fun p hp hV => lt_of_le_of_lt hp hV)

namespace ChartSystem
variable {W T₀ : ℕ} (s : ChartSystem W T₀)

/-- The density factor `J_c / ν_c` of normalized chart `c`:
`(ν(A_c) q)⁻¹ |det obsMatrix|⁻¹`, with `|det obsMatrix|⁻¹ = q |det D_c|`. -/
noncomputable def normFactor (ν : Fin W → Measure Trajectory) (c : Fin s.count) : ENNReal :=
  (ν (s.world c) (s.assignment c) * ENNReal.ofReal (s.frameOf c).q)⁻¹ *
    ENNReal.ofReal |(s.frameOf c).obsMatrix.det|⁻¹

/-- **Upper comparison of a normalized chart's density**: almost every original incidence of
the world satisfies `g'_c(obs'(normInc p)) ≤ (J_c/ν_c) G(obs_ρ p)`, where `G` is the world's
density at the composed depth `ρ = alignedDepth N r r'`. -/
theorem normalized_density_le (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) (c : Fin s.count)
    (hD : IsUnit (s.frame c).det) (hA : MeasurableSet (s.assignment c))
    (hF : MeasurableSet (s.event c))
    (hsub : ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    {N r r' : ℝ} (hN : 1 < N)
    (G : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hG : Measurable G)
    (hlawρ : Measure.map (obs (B (s.world c)) (dyWidth N (alignedDepth N r r')))
      (((ν (s.world c)).prod volume).restrict (E (s.world c))) =
        (volume.prod Measure.count).withDensity G)
    (g' : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg' : Measurable g')
    (hlaw' : Measure.map (obs (s.normScale B (dyWidth N r) c) (dyWidth N r'))
      (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) =
        (volume.prod Measure.count).withDensity g') :
    ∀ᵐ p ∂(((ν (s.world c)).prod volume).restrict (E (s.world c))),
      g' (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') ((s.frameOf c).normInc p)) ≤
        s.normFactor ν c * G (obs (B (s.world c)) (dyWidth N (alignedDepth N r r')) p) := by
  set F := s.frameOf c
  have hq := s.frameOf_q_pos c
  have hδ : dyWidth N r ≠ 0 := by unfold dyWidth; positivity
  have hmul : dyWidth N r * dyWidth N r' = dyWidth N (alignedDepth N r r') := dyWidth_mul N r r' hN
  set ρ := alignedDepth N r r'
  set μγ := ((ν (s.world c)).prod volume).restrict (E (s.world c))
  set ref := (volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)
  set e := F.obsEquiv hq.ne' hD
  set C := ENNReal.ofReal |F.obsMatrix.det|⁻¹
  set a := (ν (s.world c) (s.assignment c) * ENNReal.ofReal F.q)⁻¹
  have hsub' : ∀ p ∈ s.event c, p.1 ∈ s.assignment c ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q) := by
    intro p hp
    obtain ⟨_, h1, h2⟩ := hsub p hp
    exact ⟨h1, (s.timeBlock_frameOf c) ▸ h2⟩
  -- the normalized law in terms of the chart's original law at the composed width
  have hlaw := F.normalized_obs_law hq hD (ν (s.world c)) hA hF hsub' (B (s.world c))
    (dyWidth N r) (dyWidth N r') hδ
  rw [hmul] at hlaw
  have hle : Measure.map (obs (B (s.world c)) (dyWidth N ρ))
      (((ν (s.world c)).prod volume).restrict (s.event c)) ≤ ref.withDensity G := by
    rw [← hlawρ]
    exact Measure.map_mono (Measure.restrict_mono (fun p hp => (hsub p hp).1) le_rfl)
      (measurable_obs _ _)
  have hcmp : ref.withDensity g' ≤ ref.withDensity (fun z => a * (C * G (e.symm z))) := by
    rw [← hlaw']
    unfold normScale normPrior normEventOf
    rw [hlaw]
    have hmap := map_withDensity_of_map_eq_smul ref e C (F.map_obsEquiv hq.ne' hD) G hG
    have hcoe : (e : (EuclideanSpace ℝ (Fin 3) × ℤ) → (EuclideanSpace ℝ (Fin 3) × ℤ)) =
        Prod.map F.obsBase id := rfl
    rw [hcoe] at hmap
    calc a • Measure.map (Prod.map F.obsBase id) (Measure.map (obs (B (s.world c))
          (dyWidth N ρ)) (((ν (s.world c)).prod volume).restrict (s.event c)))
        ≤ a • Measure.map (Prod.map F.obsBase id) (ref.withDensity G) := by
          have h := Measure.map_mono hle (F.measurable_obsBase.prodMap measurable_id)
          refine Measure.le_iff.mpr fun S hS => ?_
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
          exact mul_le_mul_right (Measure.le_iff.mp h S hS) a
      _ = a • ref.withDensity (fun z => C * G (e.symm z)) := by rw [hmap]
      _ = _ := by
          have hf : Measurable (fun z => C * G (e.symm z)) :=
            measurable_const.mul (hG.comp e.symm.measurable)
          rw [← withDensity_smul a hf]
          rfl
  have hae1 : ∀ᵐ z ∂ref, g' z ≤ a * (C * G (e.symm z)) :=
    density_le_of_le ref hg' hcmp
  -- pull back along `e`, which rescales the reference measure
  have hae2 : ∀ᵐ z ∂ref, g' (e z) ≤ a * (C * G z) := by
    have hm : MeasurableSet {z | ¬ g' z ≤ a * (C * G (e.symm z))} :=
      (measurableSet_le hg' (measurable_const.mul (measurable_const.mul
        (hG.comp e.symm.measurable)))).compl
    have h0 : ref {z | ¬ g' z ≤ a * (C * G (e.symm z))} = 0 := ae_iff.mp hae1
    have hpre : ref (e ⁻¹' {z | ¬ g' z ≤ a * (C * G (e.symm z))}) = 0 := by
      have := e.map_apply (μ := ref) {z | ¬ g' z ≤ a * (C * G (e.symm z))}
      rw [F.map_obsEquiv hq.ne' hD, Measure.smul_apply, h0, smul_zero] at this
      exact this.symm
    refine ae_iff.mpr (measure_mono_null (fun z hz => ?_) hpre)
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, MeasurableEquiv.symm_apply_apply] at hz ⊢
    exact hz
  -- transfer to incidences of the world
  have hac : Measure.map (obs (B (s.world c)) (dyWidth N ρ)) μγ ≪ ref := by
    rw [hlawρ]; exact withDensity_absolutelyContinuous _ _
  have hae3 : ∀ᵐ p ∂μγ, g' (e (obs (B (s.world c)) (dyWidth N ρ) p)) ≤
      a * (C * G (obs (B (s.world c)) (dyWidth N ρ) p)) :=
    ae_of_ae_map (measurable_obs _ _).aemeasurable (hac hae2)
  filter_upwards [hae3] with p hp
  have hobs : obs (s.normScale B (dyWidth N r) c) (dyWidth N r') (F.normInc p) =
      e (obs (B (s.world c)) (dyWidth N ρ) p) := by
    unfold normScale
    rw [F.obs_normInc hq.ne' (B (s.world c)) (dyWidth N r) (dyWidth N r') hδ p, hmul]
    rfl
  rw [hobs]
  calc g' (e (obs (B (s.world c)) (dyWidth N ρ) p)) ≤ a * (C * G (obs (B (s.world c))
        (dyWidth N ρ) p)) := hp
    _ = s.normFactor ν c * G (obs (B (s.world c)) (dyWidth N ρ) p) := by
        unfold normFactor; ring

/-- **Intermediate upper comparison** (paper Lemma 2.13 with (2.15), upper half): the weighted
mass of the normalized problem where a chart's density at depth `r'` exceeds `(J_c/ν_c) U` is at
most `2 Z⁻¹` times the weighted original mass where the density at any fixed depth
`σ ≤ alignedDepth N r r'` exceeds `U`. -/
theorem normalized_upper_comparison (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν)
    (E : Fin W → Set Incidence) (hE : ∀ γ, MeasurableSet (E γ)) (B : Fin W → ℝ)
    (hD : ∀ c, IsUnit (s.frame c).det) (hA : ∀ c, MeasurableSet (s.assignment c))
    (hF : ∀ c, MeasurableSet (s.event c))
    (hdisj : ∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
      Disjoint (s.assignment b) (s.assignment b'))
    (hsub : ∀ c, ∀ p ∈ s.event c, p ∈ E (s.world c) ∧ p.1 ∈ s.assignment c ∧
      p.2 ∈ timeBlock T₀ (s.block c))
    {N r r' σ : ℝ} (hN : 1 < N) (hσ : σ ≤ alignedDepth N r r')
    (g G : Fin W → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg : ∀ γ, Measurable (g γ))
    (hG : ∀ γ, Measurable (G γ))
    (hlawσ : ∀ γ, Measure.map (obs (B γ) (dyWidth N σ)) (((ν γ).prod volume).restrict (E γ)) =
      (volume.prod Measure.count).withDensity (g γ))
    (hlawρ : ∀ γ, Measure.map (obs (B γ) (dyWidth N (alignedDepth N r r')))
      (((ν γ).prod volume).restrict (E γ)) = (volume.prod Measure.count).withDensity (G γ))
    (g' : Fin s.count → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hg' : ∀ c, Measurable (g' c))
    (hlaw' : ∀ c, Measure.map (obs (s.normScale B (dyWidth N r) c) (dyWidth N r'))
      (((s.normPrior ν c).prod volume).restrict (s.normEventOf c)) =
        (volume.prod Measure.count).withDensity (g' c))
    (U : ENNReal) :
    ∑ c, ENNReal.ofReal (s.normWeight ω ν c) *
        (((s.normPrior ν c).prod volume).restrict (s.normEventOf c))
          {z | s.normFactor ν c * U < g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') z)} ≤
      ENNReal.ofReal (s.normZ ω ν)⁻¹ * (2 * ∑ γ, ENNReal.ofReal (ω γ) *
        (((ν γ).prod volume).restrict (E γ)) {p | U < g γ (obs (B γ) (dyWidth N σ) p)}) := by
  refine s.normalized_exceptional_le ω ν hω hZ E hE hD hA hF hdisj hsub _
    (fun c => measurableSet_lt measurable_const ((hg' c).comp (measurable_obs _ _))) _
    (fun γ => measurableSet_lt measurable_const ((hg γ).comp (measurable_obs _ _))) fun c => ?_
  have h1 := s.normalized_density_le ν E B c (hD c) (hA c) (hF c) (hsub c) hN (G (s.world c))
    (hG _) (hlawρ _) (g' c) (hg' c) (hlaw' c)
  have h2 := density_depth_le (((ν (s.world c)).prod volume).restrict (E (s.world c)))
    (B (s.world c)) hN.le hσ (g (s.world c)) (G (s.world c)) (hg _) (hG _) (hlawσ _) (hlawρ _)
  have h3 : ∀ᵐ p ∂(((ν (s.world c)).prod volume).restrict (E (s.world c))),
      g' c (obs (s.normScale B (dyWidth N r) c) (dyWidth N r') ((s.frameOf c).normInc p)) ≤
        s.normFactor ν c * g (s.world c) (obs (B (s.world c)) (dyWidth N σ) p) := by
    filter_upwards [h1, h2] with p hp1 hp2
    exact hp1.trans (mul_le_mul_right hp2 _)
  rw [ae_restrict_iff' (hE _)] at h3
  filter_upwards [h3] with p hp hpF hpX
  have hlt := lt_of_lt_of_le hpX (hp (hsub c p hpF).1)
  show U < g (s.world c) (obs (B (s.world c)) (dyWidth N σ) p)
  by_contra hcon
  exact absurd (mul_le_mul_right (not_lt.mp hcon) (s.normFactor ν c)) (not_le.mpr hlt)

end ChartSystem

end Submission.Lib.K4ChartLifting
