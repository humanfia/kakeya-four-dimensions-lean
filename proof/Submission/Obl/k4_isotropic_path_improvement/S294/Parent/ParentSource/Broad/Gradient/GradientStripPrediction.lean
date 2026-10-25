-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.GradientStripPrediction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/GradientStripPrediction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit af69463910936c02b3e287e9153c4781be3e7639,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/GradientStripPrediction.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.GradientFreeze
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalGradientRenewal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-- Large frozen gradients yield an actual strip containing EVERY tested
velocity. This is pointwise and requires no breadth premise or normalized
source law; the offset is bounded by an actual source velocity. -/
theorem frozen_derivative_strip_prediction {Ω : Type*}
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (S : Set Ω) (hS : S.Nonempty)
    (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {δ R B : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |F (spacetimeDirection (V ω))| ≤ R)
    (hlarge : R+(B+2)*(R/δ) < ‖F‖) :
    ∃ (normal : EuclideanSpace ℝ (Fin 2)) (center : ℝ),
      ‖normal‖=1 ∧ |center| ≤ B+δ ∧
      S⊆V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip normal center δ := by
  let a := derivativeCoordinate F 0
  let b := derivativeSpatialRow F
  have htest' (ω) (hω : ω∈S) : |a+inner ℝ (V ω) b| ≤ R := by
    simpa only [a,b,derivative_spacetime_direction] using htest ω hω
  obtain ⟨ω₀,hω₀⟩ := hS
  have ha : |a| ≤ R+B*‖b‖ := by
    calc
      _ = |(a+inner ℝ (V ω₀) b)-inner ℝ (V ω₀) b| := by ring_nf
      _ ≤ |a+inner ℝ (V ω₀) b|+|inner ℝ (V ω₀) b| := abs_sub _ _
      _ ≤ R+‖V ω₀‖*‖b‖ := add_le_add (htest' ω₀ hω₀) (abs_real_inner_le_norm _ _)
      _ ≤ _ := by gcongr; exact hspeed ω₀ hω₀
  have hb : R/δ < ‖b‖ := by
    by_contra h
    have hb' : ‖b‖ ≤ R/δ := le_of_not_gt h
    have hF : ‖F‖ ≤ |a|+2*‖b‖ := derivative_norm_le_row F
    have hmul := mul_le_mul_of_nonneg_left hb' (by linarith : 0 ≤ B+2)
    nlinarith
  have hbp : 0 < ‖b‖ := (div_nonneg hR hδ.le).trans_lt hb
  let normal := ‖b‖⁻¹ • b
  let center := -a/‖b‖
  have hunit : ‖normal‖=1 := by
    rw [show normal=‖b‖⁻¹ • b from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hbp),inv_mul_cancel₀ hbp.ne']
  have hstrip (ω) (hω : ω∈S) : V ω∈Submission.Lib.K4VelocityStrips.affineStrip normal center δ := by
    change |inner ℝ (V ω) normal-center| ≤ δ
    have heq : inner ℝ (V ω) normal-center=(a+inner ℝ (V ω) b)/‖b‖ := by
      simp only [normal,center,inner_smul_right,div_eq_mul_inv]
      ring
    rw [heq,abs_div,abs_of_pos hbp]
    apply (div_le_iff₀ hbp).mpr
    exact (htest' ω hω).trans (by nlinarith [(div_lt_iff₀ hδ).mp hb])
  have hcenter : |center| ≤ B+δ := by
    have hh := hstrip ω₀ hω₀
    change |inner ℝ (V ω₀) normal-center| ≤ δ at hh
    have hn := abs_real_inner_le_norm (V ω₀) normal
    rw [hunit,mul_one] at hn
    have htri := abs_sub (inner ℝ (V ω₀) normal) (inner ℝ (V ω₀) normal-center)
    rw [sub_sub_cancel] at htri
    linarith [hspeed ω₀ hω₀]
  exact ⟨normal,center,hunit,hcenter,hstrip⟩

/-- Varying derivative tests freeze to one explicit strip certificate on
an original source cell. This exposes the alternative used by narrow
capture, before any breadth renewal is available at that scale. -/
theorem derivative_freeze_strip_prediction {Ω : Type*}
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (S : Set Ω) (hS : S.Nonempty)
    (F : Ω → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (F₀ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {δ E e B : ℝ} (hδ : 0 < δ) (hE : 0 ≤ E) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |F ω (spacetimeDirection (V ω))| ≤ E)
    (hfreeze : ∀ ω∈S, ‖F ω-F₀‖ ≤ e)
    (hlarge : (E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ) < ‖F₀‖) :
    ∃ (normal : EuclideanSpace ℝ (Fin 2)) (center : ℝ),
      ‖normal‖=1 ∧ |center| ≤ B+δ ∧
      S⊆V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip normal center δ := by
  apply frozen_derivative_strip_prediction V S hS F₀ hδ (by positivity) hB hspeed _ hlarge
  intro ω hω
  have htime : |derivativeCoordinate F₀ 0-derivativeCoordinate (F ω) 0| ≤ e := by
    have hh := derivative_coordinate_distance (F ω) F₀ 0
    simpa only [abs_sub_comm] using hh.trans (hfreeze ω hω)
  have hspace : ‖derivativeSpatialRow F₀-derivativeSpatialRow (F ω)‖ ≤ 2*e := by
    have hh := derivative_spatial_distance (F ω) F₀
    simpa only [norm_sub_rev] using hh.trans (mul_le_mul_of_nonneg_left (hfreeze ω hω) (by norm_num))
  have herror : |inner ℝ (V ω) (derivativeSpatialRow F₀-derivativeSpatialRow (F ω))| ≤ B*(2*e) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hspeed ω hω) hspace (norm_nonneg _) hB)
  have heq : F₀ (spacetimeDirection (V ω))=
      F ω (spacetimeDirection (V ω))+
        (derivativeCoordinate F₀ 0-derivativeCoordinate (F ω) 0)+
        inner ℝ (V ω) (derivativeSpatialRow F₀-derivativeSpatialRow (F ω)) := by
    rw [derivative_spacetime_direction,derivative_spacetime_direction,inner_sub_right]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (htest ω hω) htime)) herror)

/-- One total table of actual strip predictions covers every large-gradient
source cell. Empty or small-gradient cells receive harmless unit defaults. -/
theorem exists_derivative_strip_prediction_table {Ω I : Type*}
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (S : Set Ω) (state : Ω → I)
    (F : Ω → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (frozen : I → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {δ E e B : ℝ} (hδ : 0 < δ) (hE : 0 ≤ E) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |F ω (spacetimeDirection (V ω))| ≤ E)
    (hfreeze : ∀ ω∈S, ‖F ω-frozen (state ω)‖ ≤ e) :
    ∃ (normal : I → EuclideanSpace ℝ (Fin 2)) (center : I → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ B+δ) ∧
      ∀ ω∈S, (E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ) < ‖frozen (state ω)‖ →
        V ω∈Submission.Lib.K4VelocityStrips.affineStrip (normal (state ω)) (center (state ω)) δ := by
  classical
  let threshold := (E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ)
  have hlocal (i : I) : ∃ (n : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
      ‖n‖=1 ∧ |c| ≤ B+δ ∧ ∀ ω∈S, state ω=i → threshold < ‖frozen i‖ →
        V ω∈Submission.Lib.K4VelocityStrips.affineStrip n c δ := by
    by_cases hi : threshold < ‖frozen i‖ ∧ (S∩state ⁻¹' {i}).Nonempty
    · obtain ⟨n,c,hn,hc,hsub⟩ := derivative_freeze_strip_prediction V (S∩state ⁻¹' {i})
        hi.2 F (frozen i) hδ hE he hB (fun ω hω => hspeed ω hω.1)
        (fun ω hω => htest ω hω.1)
        (fun ω hω => by simpa only [mem_preimage,mem_singleton_iff.mp hω.2] using hfreeze ω hω.1) hi.1
      exact ⟨n,c,hn,hc,fun ω hω hstate _ => hsub ⟨hω,hstate⟩⟩
    · have hunit : ‖(WithLp.toLp 2 ![1,0] : EuclideanSpace ℝ (Fin 2))‖=1 := by
        simp [EuclideanSpace.norm_eq,Fin.sum_univ_two]
      have hzero : |(0:ℝ)| ≤ B+δ := by simpa only [abs_zero] using add_nonneg hB hδ.le
      refine ⟨WithLp.toLp 2 ![1,0],0,hunit,hzero,?_⟩
      intro ω hω hstate hlarge
      exact (hi ⟨hlarge,⟨ω,hω,hstate⟩⟩).elim
  choose normal center hnormal hcenter hfit using hlocal
  exact ⟨normal,center,(fun i => ⟨hnormal i,hcenter i⟩),
    fun ω hω hlarge => hfit (state ω) ω hω rfl hlarge⟩

/-- If a derivative is large somewhere on the core, the low-gradient cells
have LESS than one original entry floor. Value-jet norming is applied to
their genuine measurable base region; no breadth is assumed. -/
theorem low_gradient_cells_mass_lt_original_floor
    {D J : ℕ} (hjets : ValueJetBound D J)
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (S : Set Ω) (hS : MeasurableSet S) (state : Ω → I)
    (hstate : ∀ i, MeasurableSet (state ⁻¹' {i}))
    (region : I → Set (EuclideanSpace ℝ (Fin 3)))
    (hregion : ∀ i, MeasurableSet (region i))
    (hball : ∀ i, region i⊆Metric.closedBall 0 1)
    (hZ : ∀ ω∈S, Z ω∈region (state ω))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hgext : ∀ j : Fin 3, exf D (gradientComponent g j))
    (frozen : I → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {A β threshold e : ℝ} (hA : 2 ≤ A) (hβ : 0 < β)
    (hthreshold : 0 ≤ threshold) (he : 0 ≤ e)
    (hcap : ∀ U, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β*volume U)
    (hfreeze : ∀ i x, x∈region i → ‖fderiv ℝ g x-frozen i‖ ≤ e)
    (hlarge : ∃ x∈Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      3*A^J*(threshold+e) < ‖fderiv ℝ g x‖) :
    μ {ω | ω∈S ∧ ‖frozen (state ω)‖ ≤ threshold} < ENNReal.ofReal (β/A) := by
  classical
  let low := {ω | ω∈S ∧ ‖frozen (state ω)‖ ≤ threshold}
  have hlow : MeasurableSet low := by
    have heq : low=⋃ i, if ‖frozen i‖ ≤ threshold then S∩state ⁻¹' {i} else ∅ := by
      ext ω
      constructor
      · rintro ⟨hω,hsmall⟩
        exact mem_iUnion.mpr ⟨state ω,by rw [ite_eq_left hsmall]; exact ⟨hω,rfl⟩⟩
      · intro hω
        obtain ⟨i,hi⟩ := mem_iUnion.mp hω
        split_ifs at hi with hsmall
        · have hsi : state ω=i := hi.2
          exact ⟨hi.1,by rw [hsi]; exact hsmall⟩
        · exact hi.elim
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    split_ifs
    · exact hS.inter (hstate i)
    · exact MeasurableSet.empty
  let base := ⋃ i, if ‖frozen i‖ ≤ threshold then region i else ∅
  have hbase : MeasurableSet base := by
    apply MeasurableSet.iUnion
    intro i
    split_ifs
    · exact hregion i
    · exact MeasurableSet.empty
  have hbaseBall : base⊆Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    split_ifs at hi with hsmall
    · exact hball i hi
    · exact hi.elim
  have hsmall : ∀ x∈base, ‖fderiv ℝ g x‖ ≤ threshold+e := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    split_ifs at hi with hiSmall
    · calc
        _ = ‖(fderiv ℝ g x-frozen i)+frozen i‖ := by rw [sub_add_cancel]
        _ ≤ ‖fderiv ℝ g x-frozen i‖+‖frozen i‖ := norm_add_le _ _
        _ ≤ e+threshold := add_le_add (hfreeze i x hi) hiSmall
        _ = _ := add_comm _ _
    · exact hi.elim
  by_contra h
  have hfloor : ENNReal.ofReal (β/A) ≤ (μ.restrict low) univ := by
    simpa only [Measure.restrict_apply_univ] using le_of_not_gt h
  have hsupp : ∀ᵐ ω ∂μ.restrict low, Z ω∈base := by
    filter_upwards [ae_restrict_mem hlow] with ω hω
    exact mem_iUnion.mpr ⟨state ω,by rw [ite_eq_left hω.2]; exact hZ ω hω.1⟩
  have hvolume := original_entry_base_volume_lower (μ.restrict low) Z base hbase
    (by linarith : 0 < A) hβ hfloor
    (fun U hU => (Measure.restrict_le_self _).trans (hcap U hU)) hsupp
  have hnorm := gradient_norm_from_value_jets_on_set hjets g hgext base hbase hbaseBall
    hA hvolume (by positivity : 0 ≤ threshold+e) hsmall
  obtain ⟨x,hx,hlarge⟩ := hlarge
  exact (not_lt_of_ge (hnorm x hx)) hlarge

/-- A large original core gradient produces a table of actual thin
strip predictions covering all but one original entry floor. This is a
narrow-capture alternative, with no input velocity breadth. -/
theorem original_entry_large_gradient_strip_capture
    {D J : ℕ} (hjets : ValueJetBound D J)
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) (hS : MeasurableSet S) (state : Ω → I)
    (hstate : ∀ i, MeasurableSet (state ⁻¹' {i}))
    (region : I → Set (EuclideanSpace ℝ (Fin 3)))
    (hregion : ∀ i, MeasurableSet (region i))
    (hball : ∀ i, region i⊆Metric.closedBall 0 1)
    (hZ : ∀ ω∈S, Z ω∈region (state ω))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hgext : ∀ j : Fin 3, exf D (gradientComponent g j))
    (frozen : I → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    {A β δ E e B : ℝ} (hA : 2 ≤ A) (hβ : 0 < β)
    (hδ : 0 < δ) (hE : 0 ≤ E) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hcap : ∀ U, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β*volume U)
    (hfreeze : ∀ i x, x∈region i → ‖fderiv ℝ g x-frozen i‖ ≤ e)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤ E)
    (hlarge : ∃ x∈Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      3*A^J*((E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ)+e) < ‖fderiv ℝ g x‖) :
    ∃ (normal : I → EuclideanSpace ℝ (Fin 2)) (center : I → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ B+δ) ∧
      MeasurableSet (⋃ i, state ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) ∧
      μ (S\⋃ i, state ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) <
          ENNReal.ofReal (β/A) := by
  classical
  obtain ⟨normal,center,hbounds,hfit⟩ := exists_derivative_strip_prediction_table V S state
    (fun ω => fderiv ℝ g (Z ω)) frozen hδ hE he hB hspeed htest
    (fun ω hω => hfreeze (state ω) (Z ω) (hZ ω hω))
  let capture := ⋃ i, state ⁻¹' {i}∩
    V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ
  have hcapture : MeasurableSet capture := MeasurableSet.iUnion (fun i => (hstate i).inter
    ((Submission.Lib.K4VelocityStrips.measurableSet_affineStrip _ _ _).preimage hV))
  have hlow := low_gradient_cells_mass_lt_original_floor hjets μ Z S hS state hstate
    region hregion hball hZ g hgext frozen hA hβ (by positivity) he hcap hfreeze hlarge
  have hsub : S\capture⊆{ω | ω∈S ∧ ‖frozen (state ω)‖ ≤
      (E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ)} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    by_contra hlargeCell
    have hh := hfit ω hω.1 (lt_of_not_ge hlargeCell)
    exact hω.2 (mem_iUnion.mpr ⟨state ω,⟨rfl,hh⟩⟩)
  exact ⟨normal,center,hbounds,hcapture,(measure_mono hsub).trans_lt hlow⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
