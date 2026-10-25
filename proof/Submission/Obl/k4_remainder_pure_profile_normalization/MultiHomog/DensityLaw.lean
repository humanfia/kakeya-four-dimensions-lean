import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.Density
import Submission.Obl.k4_native_grid_profile_extension.ProfileBridge

/-!
# The encoded density law and exceptional masses

`encDensity g` is a version of the density of the encoded joint observation; on the
incidences of a retained world it equals `Λ` times the world density, so the exceptional
masses of the worlds and of the encoded world coincide.
-/

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog

open MeasureTheory Set Filter
open scoped ENNReal

theorem measurable_jointObs (N r u : ℝ) : Measurable (jointObs N r u) := by
  have := Submission.Obl.k4_native_grid_profile_extension.measurable_nativeObservation N r u
  rw [Submission.Obl.k4_native_grid_profile_extension.nativeObservation_eq_Observation] at this
  exact this

/-- A finite weighted sum of densities. -/
theorem sum_smul_withDensity {α ι : Type*} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (w : ι → ℝ≥0∞) (F : ι → α → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    ∑ i, w i • μ.withDensity (F i) = μ.withDensity (fun z => ∑ i, w i * F i z) := by
  ext X hX
  rw [Measure.coe_finsetSum, Finset.sum_apply, withDensity_apply _ hX,
    lintegral_finset_sum _ (fun i _ => (hF i).const_mul (w i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, withDensity_apply _ hX, smul_eq_mul, lintegral_const_mul _ (hF i)]

namespace Sample

variable {S : Sample}

/-- The base change of a world observation as a measurable equivalence. -/
noncomputable def baseChange (h : S.Hyp) (γ : Fin S.W) : Observation ≃ᵐ Observation :=
  (baseEquiv h.a_ne (h.b_ne γ) (S.o γ)).prodCongr (MeasurableEquiv.refl ℤ)

namespace Hyp

variable (h : S.Hyp)
include h

theorem map_baseChange (γ : Fin S.W) :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)).map
        (baseChange h γ) =
      ENNReal.ofReal |S.a * S.b γ|⁻¹ •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (Measure.count : Measure ℤ)) := by
  have hcoe : (baseChange h γ : Observation → Observation) =
      Prod.map (baseMap S.a (S.b γ) (S.o γ)) id := rfl
  rw [hcoe, ← Measure.map_prod_map _ _ (continuous_baseMap _ _ _).measurable measurable_id,
    map_baseMap_volume h.a_ne (h.b_ne γ), Measure.map_id, Measure.prod_smul_left]

/-- Transport of a world density to the encoded joint observation. -/
theorem map_encObs_withDensity (γ : Fin S.W) {f : Observation → ℝ≥0∞} (hf : Measurable f) :
    ((volume.prod Measure.count).withDensity f).map (encObs S.a (S.b γ) (S.o γ)) =
      jointRef.withDensity (fun z => ENNReal.ofReal |S.a * S.b γ|⁻¹ *
        f (baseInv S.a (S.b γ) (S.o γ) z.1.1, z.1.2) *
        (({0} : Set (Fin 2 → ℤ)).indicator (fun _ => (1 : ℝ≥0∞)) z.2)) := by
  have hcomp : encObs S.a (S.b γ) (S.o γ) =
      (fun q : Observation => (q, (0 : Fin 2 → ℤ))) ∘ (baseChange h γ) := by
    funext q; rfl
  have hpair : Measurable (fun q : Observation => (q, (0 : Fin 2 → ℤ))) :=
    measurable_id.prodMk measurable_const
  rw [hcomp, ← Measure.map_map hpair (baseChange h γ).measurable,
    map_withDensity_equiv_smul _ _ (baseChange h γ) _ (h.map_baseChange γ) f hf]
  exact map_pair_withDensity (volume.prod Measure.count)
    (fun q : Observation => ENNReal.ofReal |S.a * S.b γ|⁻¹ * f ((baseChange h γ).symm q))
    (measurable_const.mul (hf.comp (baseChange h γ).symm.measurable)) (0 : Fin 2 → ℤ)

/-- `encDensity g` is a version of the density of the encoded joint observation. -/
theorem encoded_density_law {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') (hsub : E'' ⊆ S.event) (s : ℝ)
    {g : Fin S.W → Observation → ℝ≥0∞} (hg : ∀ γ, Measurable (g γ))
    (hmap : ∀ γ, (S.decLaw E'' γ).map (obs (S.B γ) (δ S.N s)) =
      (volume.prod Measure.count).withDensity (g γ)) :
    ((S.prior.prod volume).restrict E'').map (jointObs S.N (depthSum S.N S.s0 s) 0) =
      jointRef.withDensity (S.encDensity g) := by
  have hJ := measurable_jointObs S.N (depthSum S.N S.s0 s) 0
  have hworld : ∀ γ, (S.decLaw E'' γ).map (jointObs S.N (depthSum S.N S.s0 s) 0 ∘ S.encInc γ) =
      jointRef.withDensity (fun z => ENNReal.ofReal |S.a * S.b γ|⁻¹ *
        S.goodObs.indicator (g γ) (baseInv S.a (S.b γ) (S.o γ) z.1.1, z.1.2) *
        (({0} : Set (Fin 2 → ℤ)).indicator (fun _ => (1 : ℝ≥0∞)) z.2)) := by
    intro γ
    have hae : jointObs S.N (depthSum S.N S.s0 s) 0 ∘ S.encInc γ =ᵐ[S.decLaw E'' γ]
        encObs S.a (S.b γ) (S.o γ) ∘ obs (S.B γ) (δ S.N s) := by
      filter_upwards [h.ae_decLaw_good hT hE'' hsub γ] with p hp
      exact h.jointObs_encInc γ s hp.1
    rw [Measure.map_congr hae, ← Measure.map_map (measurable_encObs _ _ _) (measurable_obs _ _),
      hmap γ, withDensity_congr_ae (h.density_eq_indicator hT hE'' hsub γ s (hg γ) (hmap γ)),
      h.map_encObs_withDensity γ ((hg γ).indicator S.measurableSet_goodObs)]
  rw [h.law_decomposition hT hE'', map_finset_sum' _ hJ]
  have hterm : ∀ γ, ((ENNReal.ofReal (S.ω γ)) • (S.decLaw E'' γ).map (S.encInc γ)).map
      (jointObs S.N (depthSum S.N S.s0 s) 0) =
      ENNReal.ofReal (S.ω γ) • (S.decLaw E'' γ).map
        (jointObs S.N (depthSum S.N S.s0 s) 0 ∘ S.encInc γ) := by
    intro γ
    rw [Measure.map_smul, Measure.map_map hJ (measurable_encInc γ)]
    exact hJ.aemeasurable
  simp_rw [hterm, hworld]
  rw [sum_smul_withDensity]
  · rfl
  · intro γ
    refine ((Measurable.const_mul ?_ _).mul ?_)
    · refine ((hg γ).indicator S.measurableSet_goodObs).comp ?_
      exact ((continuous_baseInv _ _ _).measurable.comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)
    · exact (measurable_const.indicator (measurableSet_singleton _)).comp measurable_snd

/-- On the incidences of a retained world, the encoded density is `Λ` times the world density. -/
theorem encDensity_encInc {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') (hsub : E'' ⊆ S.event) (s : ℝ)
    (g : Fin S.W → Observation → ℝ≥0∞) (γ : Fin S.W) (hγ : S.Retained γ) :
    ∀ᵐ p ∂S.decLaw E'' γ, S.encDensity g (jointObs S.N (depthSum S.N S.s0 s) 0 (S.encInc γ p)) =
      ENNReal.ofReal S.Lam * g γ (obs (S.B γ) (δ S.N s) p) := by
  filter_upwards [h.ae_decLaw_good hT hE'' hsub γ] with p hp
  rw [h.jointObs_encInc γ s hp.1]
  set q := obs (S.B γ) (δ S.N s) p with hq
  have hqg : q ∈ S.goodObs := obs_mem_goodObs hp.1 hp.2 _ _
  unfold encDensity encObs
  rw [Finset.sum_eq_single γ]
  · simp only [indicator_of_mem (mem_singleton (0 : Fin 2 → ℤ)), mul_one]
    have hbi : (baseInv S.a (S.b γ) (S.o γ) (baseMap S.a (S.b γ) (S.o γ) q.1), q.2) = q := by
      rw [baseInv_baseMap h.a_ne (h.b_ne γ)]
    rw [hbi, indicator_of_mem hqg, ← mul_assoc, ← ENNReal.ofReal_mul (h.ω_nonneg γ)]
    congr 2
    rw [abs_of_pos (mul_pos h.a_pos (h.b_pos γ)), ← div_eq_mul_inv]
    exact h.weight_div γ hγ
  · intro γ' _ hne
    have hnot : (baseInv S.a (S.b γ') (S.o γ') (baseMap S.a (S.b γ) (S.o γ) q.1), q.2) ∉
        S.goodObs := by
      intro hmem
      have hsep := h.o_sep hne.symm
      have hq1 : |q.1 1| ≤ S.K := hqg
      have hmem' : |(baseInv S.a (S.b γ') (S.o γ') (baseMap S.a (S.b γ) (S.o γ) q.1)) 1| ≤ S.K :=
        hmem
      have hval : (baseInv S.a (S.b γ') (S.o γ') (baseMap S.a (S.b γ) (S.o γ) q.1)) 1 =
          q.1 1 + (S.o γ - S.o γ') / S.a := by
        simp [baseInv, baseMap]
        field_simp [h.a_ne]
        ring
      rw [hval] at hmem'
      have ha := h.a_pos
      have hK := h.K_pos
      have h2 : 2 * S.K < |(S.o γ - S.o γ') / S.a| := by
        rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha]
        linarith
      have h3 : |(S.o γ - S.o γ') / S.a| ≤ |q.1 1 + (S.o γ - S.o γ') / S.a| + |q.1 1| := by
        have := abs_sub_abs_le_abs_sub ((S.o γ - S.o γ') / S.a) (-(q.1 1))
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        linarith
      linarith
    rw [indicator_of_notMem hnot, mul_zero, zero_mul, mul_zero]
  · intro hγ'; exact absurd (Finset.mem_univ γ) hγ'

/-- The exceptional masses of the worlds and of the encoded world coincide. -/
theorem bad_mass {D : ℕ} (hT : Tempered S.N S.K S.M D S.W S.ω S.ν S.E S.B)
    {E'' : Set Incidence} (hE'' : MeasurableSet E'') (hsub : E'' ⊆ S.event) (s : ℝ)
    {g : Fin S.W → Observation → ℝ≥0∞} (hg : ∀ γ, Measurable (g γ)) (lo hi : ℝ≥0∞) :
    ∑ γ, ENNReal.ofReal (S.ω γ) * (S.decLaw E'' γ)
        {p | g γ (obs (S.B γ) (δ S.N s) p) < lo ∨ hi < g γ (obs (S.B γ) (δ S.N s) p)} =
      ((S.prior.prod volume).restrict E'')
        {P | S.encDensity g (jointObs S.N (depthSum S.N S.s0 s) 0 P) <
            ENNReal.ofReal S.Lam * lo ∨
          ENNReal.ofReal S.Lam * hi <
            S.encDensity g (jointObs S.N (depthSum S.N S.s0 s) 0 P)} := by
  have hJ := measurable_jointObs S.N (depthSum S.N S.s0 s) 0
  have hGm := (S.measurable_encDensity hg).comp hJ
  have hX : MeasurableSet {P : Incidence |
      S.encDensity g (jointObs S.N (depthSum S.N S.s0 s) 0 P) < ENNReal.ofReal S.Lam * lo ∨
        ENNReal.ofReal S.Lam * hi < S.encDensity g (jointObs S.N (depthSum S.N S.s0 s) 0 P)} :=
    (measurableSet_lt hGm measurable_const).union (measurableSet_lt measurable_const hGm)
  rw [h.law_decomposition hT hE'', Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_encInc γ) hX]
  congr 1
  by_cases hγ : S.Retained γ
  · have hL0 : ENNReal.ofReal S.Lam ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h.Lam_pos
    have hLt : ENNReal.ofReal S.Lam ≠ ⊤ := ENNReal.ofReal_ne_top
    refine measure_congr ?_
    filter_upwards [h.encDensity_encInc hT hE'' hsub s g γ hγ] with p hp
    simp only [mem_preimage, mem_ofPred_eq, eq_iff_iff]
    rw [hp, ENNReal.mul_lt_mul_iff_right hL0 hLt, ENNReal.mul_lt_mul_iff_right hL0 hLt]
  · have : S.decLaw E'' γ = 0 := by
      rw [Sample.decLaw, h.decEvent_empty hsub γ hγ, Measure.restrict_empty]
    rw [this]
    rfl

end Hyp

end Sample

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
