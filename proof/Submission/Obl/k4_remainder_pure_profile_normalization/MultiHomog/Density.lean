import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Decode

/-!
# Densities of the encoded world

For arbitrary measurable versions `g γ` of the world observation densities at depth `s`,
`encDensity g` is a version of the density of the encoded joint observation at depth
`depthSum N s₀ s` and unit velocity width. On the incidences of a retained world it equals
`Λ` times the world density, since the planar regions of the worlds are disjoint. Hence
exceptional masses of the worlds and of the encoded world agree.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

/-- The encoded observation of an incidence of a world at depth `s`. -/
noncomputable abbrev jointObs (N r u : ℝ) : Incidence → JointObservation :=
  Submission.Obl.k4_joint_homogenization.Observation N r u

/-- The reference measure of joint observations. -/
noncomputable abbrev jointRef : Measure JointObservation :=
  Submission.Obl.k4_joint_homogenization.Reference

namespace Sample

variable {S : Sample}

/-- Observations whose first planar coordinate is at most `K`. -/
def goodObs (S : Sample) : Set Observation := {q | |q.1 1| ≤ S.K}

theorem measurableSet_goodObs (S : Sample) : MeasurableSet S.goodObs := by
  unfold goodObs
  have : Continuous (fun q : Observation => |q.1 1|) := by fun_prop
  exact measurableSet_le this.measurable measurable_const

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) := by
  have hx : Continuous (fun p : Incidence => x p.1 p.2) := by
    unfold x
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  unfold obs
  refine Measurable.prodMk ?_ ?_
  · have : Continuous (fun p : Incidence =>
        (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2] : EuclideanSpace ℝ (Fin 3))) := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      fin_cases i
      · simp; fun_prop
      · simp; exact (continuous_apply 1).comp hx
      · simp; exact (continuous_apply 2).comp hx
    exact this.measurable
  · refine Int.measurable_floor.comp ?_
    exact ((measurable_const.mul ((continuous_apply 3).comp hx).measurable).div_const _)

/-- The encoded density built from per-world densities. -/
noncomputable def encDensity (S : Sample) (g : Fin S.W → Observation → ℝ≥0∞)
    (z : JointObservation) : ℝ≥0∞ :=
  ∑ γ, ENNReal.ofReal (S.ω γ) * (ENNReal.ofReal |S.a * S.b γ|⁻¹ *
    S.goodObs.indicator (g γ) (baseInv S.a (S.b γ) (S.o γ) z.1.1, z.1.2) *
    (({0} : Set (Fin 2 → ℤ)).indicator (fun _ => (1 : ℝ≥0∞)) z.2))

theorem measurable_encDensity (S : Sample) {g : Fin S.W → Observation → ℝ≥0∞}
    (hg : ∀ γ, Measurable (g γ)) : Measurable (S.encDensity g) := by
  have hA : ∀ γ : Fin S.W, Measurable (fun z : JointObservation =>
      S.goodObs.indicator (g γ) (baseInv S.a (S.b γ) (S.o γ) z.1.1, z.1.2)) := by
    intro γ
    refine ((hg γ).indicator S.measurableSet_goodObs).comp ?_
    exact ((continuous_baseInv _ _ _).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)
  have hB : Measurable (fun z : JointObservation =>
      (({0} : Set (Fin 2 → ℤ)).indicator (fun _ => (1 : ℝ≥0∞)) z.2)) :=
    (measurable_const.indicator (measurableSet_singleton _)).comp measurable_snd
  have : S.encDensity g = fun z => ∑ γ, ENNReal.ofReal (S.ω γ) * (ENNReal.ofReal |S.a * S.b γ|⁻¹ *
      S.goodObs.indicator (g γ) (baseInv S.a (S.b γ) (S.o γ) z.1.1, z.1.2) *
      (({0} : Set (Fin 2 → ℤ)).indicator (fun _ => (1 : ℝ≥0∞)) z.2)) := rfl
  rw [this]
  exact Finset.measurable_sum _ fun γ _ => (((hA γ).const_mul _).mul hB).const_mul _

namespace Hyp

variable (h : S.Hyp)
include h

/-- Almost every selected incidence of a world is a good line at a time in `[0,1]`. -/
theorem ae_decLaw_good {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') (hsub : E'' ⊆ S.event) (γ : Fin S.W) :
    ∀ᵐ p ∂S.decLaw E'' γ, S.GoodLine p.1 ∧ p.2 ∈ Icc (0 : ℝ) 1 := by
  have h0 := ae_goodLine hT γ
  have hq : Measure.QuasiMeasurePreserving (Prod.fst : Incidence → Trajectory)
      ((S.ν γ).prod (volume : Measure ℝ)) (S.ν γ) := Measure.quasiMeasurePreserving_fst
  have h1 : ∀ᵐ p ∂((S.ν γ).prod (volume : Measure ℝ)), S.GoodLine p.1 := hq.ae h0
  have h2 : ∀ᵐ p ∂S.decLaw E'' γ, p ∈ S.decEvent E'' γ :=
    ae_restrict_mem (hE''.preimage (measurable_encInc γ))
  filter_upwards [ae_restrict_of_ae h1, h2] with p hp1 hp2
  exact ⟨hp1, (hT.event_time γ (h.decEvent_subset hsub γ hp2)).2⟩

omit h in
/-- The observation of a good incidence is a good observation. -/
theorem obs_mem_goodObs {p : Incidence} (hp : S.GoodLine p.1)
    (ht : p.2 ∈ Icc (0 : ℝ) 1) (B a : ℝ) : obs B a p ∈ S.goodObs := by
  have hy := hp.y_le ht
  have := PiLp.norm_apply_le (y p.1 p.2) 0
  have e : (obs B a p).1 1 = (y p.1 p.2) 0 := by simp [obs, y]
  show |(obs B a p).1 1| ≤ S.K
  rw [e, ← Real.norm_eq_abs]
  exact this.trans hy

/-- The encoded joint observation of a good incidence is the encoded world observation. -/
theorem jointObs_encInc (γ : Fin S.W) (s : ℝ) {p : Incidence} (hp : S.GoodLine p.1) :
    jointObs S.N (depthSum S.N S.s0 s) 0 (S.encInc γ p) =
      encObs S.a (S.b γ) (S.o γ) (obs (S.B γ) (δ S.N s) p) := by
  obtain ⟨hv1, hv2⟩ := h.enc_velocity_small γ hp
  have hn : 1 < S.N := by linarith [h.N_ge]
  exact observation_encLine γ hn S.s0 s rfl p hv1 hv2

/-- World densities vanish almost everywhere off good observations. -/
theorem density_eq_indicator {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') (hsub : E'' ⊆ S.event) (γ : Fin S.W)
    (s : ℝ) {g : Observation → ℝ≥0∞} (hg : Measurable g)
    (hmap : (S.decLaw E'' γ).map (obs (S.B γ) (δ S.N s)) =
      (volume.prod Measure.count).withDensity g) :
    g =ᵐ[volume.prod Measure.count] S.goodObs.indicator g := by
  have hT' : MeasurableSet S.goodObsᶜ := S.measurableSet_goodObs.compl
  have hobs : Measurable (obs (S.B γ) (δ S.N s)) := measurable_obs _ _
  have hzero : ((volume.prod Measure.count).withDensity g) S.goodObsᶜ = 0 := by
    rw [← hmap, Measure.map_apply hobs hT']
    refine measure_mono_null ?_ (ae_iff.mp (h.ae_decLaw_good hT hE'' hsub γ))
    intro p hp hgood
    exact hp (obs_mem_goodObs hgood.1 hgood.2 _ _)
  rw [withDensity_apply _ hT', lintegral_eq_zero_iff hg] at hzero
  have := (ae_restrict_iff' hT').mp hzero
  filter_upwards [this] with q hq
  by_cases hqg : q ∈ S.goodObs
  · rw [indicator_of_mem hqg]
  · rw [indicator_of_notMem hqg]
    exact hq hqg

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
