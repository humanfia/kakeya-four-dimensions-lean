-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceParameterPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/IncidenceParameterPalettes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterEntryPruning
import Submission.Lib.K4OriginalReferenceCapacity.SoundBounds

/-! # Parameter palettes from current incidence caps

Full original parameter-bin floors are first localized by genuine current
entry floors. The common profile amplitude then cancels against the current
incidence ceiling. No ceiling on unlabelled fixed-time original priors is used.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Count actual fine parameters in every canonical cell using original
bin floors and the localized original incidence entries. -/
theorem parameter_cell_palettes_from_original_entries {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E R : Set (Λ × ℝ)) (hsub : R ⊆ E)
    {ρ s amplitude K C cut : ℝ} (hρ : 0 < ρ) (hs : 0 < s)
    (hamp : 0 < amplitude) (hK : 0 < K) (hC : 0 ≤ C) (hcut : 0 < cut)
    (n : ℕ) (hsdyadic : s = dyadicParameterWidth n)
    (hfinite : ((fun z : Λ × ℝ => parameterCode (ρ*s) (c z.1)) '' R).Finite)
    (π : (Fin 2 → ℤ) → ENNReal) (hπtop : ∀ v, π v ≠ ∞)
    (hfloor : ∀ z∈R,
      ENNReal.ofReal ((ρ*s)^2*amplitude/K)*π (parameterCode (ρ*s) (zv (c z.1))) ≤
        ν {l | parameterCode (ρ*s) (c l)=parameterCode (ρ*s) (c z.1)})
    (hentry : ∀ z∈R,
      ENNReal.ofReal (cut*s)*ν {l | originalZoomBlock c ρ s l=originalZoomBlock c ρ s z.1} <
        μ (R ∩ {y | originalZoomBlock c ρ s y.1=originalZoomBlock c ρ s z.1 ∧
          canonicalZoomCell c ρ s y=canonicalZoomCell c ρ s z}))
    (hcap : ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ s z=cell ∧ parameterCode (ρ*s) (zv (c z.1))=v} ≤
        ENNReal.ofReal (C*s*(ρ*s)^2*amplitude)*π v) :
    ∃ palettes : (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ),
      (∀ key, ((palettes key).card : ℝ) ≤ C*K/cut) ∧
      ∀ z∈R, parameterCode (ρ*s) (c z.1) ∈
        palettes ((parameterCode ρ (c z.1),canonicalZoomCell c ρ s z),
          parameterCode (ρ*s) (zv (c z.1))) := by
  classical
  let p := ρ*s
  let code := fun l => parameterCode p (c l)
  let velocity := fun l => parameterCode p (zv (c l))
  let carrier := hfinite.toFinset
  let palettes := fun key : ((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ) =>
    carrier.filter (fun q => ∃ z∈R, code z.1=q ∧ parameterCode ρ (c z.1)=key.1.1 ∧
      canonicalZoomCell c ρ s z=key.1.2 ∧ velocity z.1=key.2)
  have hwitness key q (hq : q∈palettes key) :
      ∃ z∈R, code z.1=q ∧ parameterCode ρ (c z.1)=key.1.1 ∧
        canonicalZoomCell c ρ s z=key.1.2 ∧ velocity z.1=key.2 :=
    (Finset.mem_filter.mp hq).2
  have hm : Measurable code := (measurable_parameterCode p).comp hc
  have hvel (l l' : Λ) (heq : code l=code l') : velocity l=velocity l' := by
    funext i
    fin_cases i
    · exact congrFun heq 4
    · exact congrFun heq 6
  refine ⟨palettes,?_,?_⟩
  · intro key
    let Q := palettes key
    let entry := fun q : Fin 7 → ℤ =>
      {y : Λ × ℝ | originalZoomBlock c ρ s y.1=(key.1.1,q) ∧
        canonicalZoomCell c ρ s y=key.1.2}
    let Box := {z : Λ × ℝ | parameterCode ρ (c z.1)=key.1.1 ∧
      canonicalZoomCell c ρ s z=key.1.2 ∧ velocity z.1=key.2}
    have he (q) : MeasurableSet (entry q) :=
      (((((measurable_parameterCode ρ).comp hc).prodMk hm).comp measurable_fst)
        (measurableSet_singleton (key.1.1,q))).inter
          ((measurable_canonicalZoomCell hc ρ s) (measurableSet_singleton key.1.2))
    have hBox : MeasurableSet Box :=
      (((measurable_parameterCode ρ).comp (hc.comp measurable_fst))
        (measurableSet_singleton key.1.1)).inter
        (((measurable_canonicalZoomCell hc ρ s) (measurableSet_singleton key.1.2)).inter
          (by
            have hv : Measurable velocity := by
              apply (measurable_parameterCode p).comp
              unfold zv
              fun_prop
            exact (hv.comp measurable_fst) (measurableSet_singleton key.2)))
    have hsumcap : (μ.restrict R) Box ≤ ENNReal.ofReal (C*s*p^2*amplitude)*π key.2 := by
      calc
        _ = μ (Box ∩ R) := Measure.restrict_apply hBox
        _ ≤ μ (Box ∩ E) := measure_mono (inter_subset_inter_right _ hsub)
        _ = (μ.restrict E) Box := (Measure.restrict_apply hBox).symm
        _ ≤ _ := hcap key.1.1 key.1.2 key.2
    have hsound (q) (hq : q∈Q) : entry q ⊆ Box := by
      obtain ⟨z,hz,hzq,hworld,hcell,hv⟩ := hwitness key q hq
      intro y hy
      have hyworld : parameterCode ρ (c y.1)=key.1.1 := congrArg Prod.fst hy.1
      have hycode : code y.1=q := congrArg Prod.snd hy.1
      exact ⟨hyworld,hy.2,(hvel y.1 z.1 (hycode.trans hzq.symm)).trans hv⟩
    have hpositive (q) (hq : q∈Q) : (μ.restrict R) (entry q) ≠ 0 := by
      obtain ⟨z,hz,hzq,hworld,hcell,hv⟩ := hwitness key q hq
      have htag : originalZoomBlock c ρ s z.1=(key.1.1,q) := Prod.ext hworld hzq
      have hh := hentry z hz
      rw [htag,hcell] at hh
      rw [Measure.restrict_apply (he q),inter_comm]
      exact ne_of_gt (lt_of_le_of_lt bot_le hh)
    by_cases hnonempty : Q.Nonempty
    · obtain ⟨q,hq⟩ := hnonempty
      have hπ0 : π key.2 ≠ 0 := by
        intro hzero
        apply hpositive q hq
        have hz : (μ.restrict R) Box=0 := le_antisymm
          (by simpa only [hzero,mul_zero] using hsumcap) zero_le
        exact measure_mono_null (hsound q hq) hz
      have hfl (q) (hq : q∈Q) :
          ENNReal.ofReal (cut*s*(p^2*amplitude/K))*π key.2 ≤ (μ.restrict R) (entry q) := by
        obtain ⟨z,hz,hzq,hworld,hcell,hv⟩ := hwitness key q hq
        have htag : originalZoomBlock c ρ s z.1=(key.1.1,q) := Prod.ext hworld hzq
        have hh := (hentry z hz).le
        rw [original_zoom_block_fiber_eq_fine c ρ s hρ n hsdyadic z.1] at hh
        have hprior := mul_le_mul' (le_refl (ENNReal.ofReal (cut*s))) (hfloor z hz)
        rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ cut*s)] at hprior
        have hbound := hprior.trans hh
        change parameterCode (ρ*s) (zv (c z.1))=key.2 at hv
        rw [hv] at hbound
        rw [htag,hcell] at hbound
        rw [Measure.restrict_apply (he q),inter_comm]
        exact hbound
      have hcapacity := Submission.Lib.K4OriginalReferenceCapacity.sound_finite_reference_capacity
        (μ.restrict R) entry Q (fun _ => π key.2)
        (ENNReal.ofReal (cut*s*(p^2*amplitude/K))) (fun q _ => he q)
        (by
          intro q _ q' _ hne
          exact disjoint_left.mpr fun y hy hy' =>
            hne (congrArg Prod.snd (hy.1.symm.trans hy'.1)))
        hfl Box hsound
      simp only [Finset.sum_const,nsmul_eq_mul] at hcapacity
      have htotal : (Q.card : ENNReal)*ENNReal.ofReal (cut*s*(p^2*amplitude/K))*π key.2 ≤
          ENNReal.ofReal (C*s*p^2*amplitude)*π key.2 := by
        calc
          _ = ENNReal.ofReal (cut*s*(p^2*amplitude/K))*((Q.card : ENNReal)*π key.2) := by ac_rfl
          _ ≤ (μ.restrict R) Box := hcapacity
          _ ≤ _ := hsumcap
      have hcancel := (ENNReal.mul_le_mul_iff_left hπ0 (hπtop key.2)).mp htotal
      have hp : 0 < p := mul_pos hρ hs
      have hreal : (Q.card : ℝ)*(cut*s*(p^2*amplitude/K)) ≤ C*s*p^2*amplitude := by
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcancel
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel
      have hmul := mul_le_mul_of_nonneg_right hreal hK.le
      have heq : (Q.card : ℝ)*(cut*s*(p^2*amplitude/K))*K =
          ((Q.card : ℝ)*cut)*(s*p^2*amplitude) := by field_simp
      rw [heq] at hmul
      have hnum : (Q.card : ℝ)*cut ≤ C*K := by
        apply (mul_le_mul_iff_left₀ (by positivity : 0 < s*p^2*amplitude)).mp
        nlinarith only [hmul]
      exact (le_div_iff₀ hcut).mpr hnum
    · have heq : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
      change (Q.card : ℝ) ≤ C*K/cut
      rw [heq,Finset.card_empty,Nat.cast_zero]
      positivity
  · intro z hz
    exact Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr ⟨z,hz,rfl⟩,z,hz,rfl,rfl,rfl,rfl⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
