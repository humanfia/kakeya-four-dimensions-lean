-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetCoefficientMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetCoefficientMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetWorldCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalMenuFractions

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory

noncomputable section

/-- One actual fine physical state bounds the coefficient diameter once
four derivative coefficients are bounded. All three intercepts cancel. -/
theorem coefficient_diameter_of_jets_and_state (c c' : Fin 7 → ℝ)
    {b H t u : ℝ} (hb : 0 < b) (hH : 0 ≤ H)
    (ht : t∈Icc (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1)
    (hc : |c 1| ≤ H ∧ |c 2| ≤ H ∧ |c 4| ≤ H ∧ |c 6| ≤ H)
    (hc' : |c' 1| ≤ H ∧ |c' 2| ≤ H ∧ |c' 4| ≤ H ∧ |c' 6| ≤ H)
    (hstate : Submission.Lib.K4CommonLocalChoice.cell b (zpos c t)=
      Submission.Lib.K4CommonLocalChoice.cell b (zpos c' u)) :
    ∀ i, |c i-c' i| ≤ b+6*H := by
  have hgap (i : Fin 4) : |zpos c t i-zpos c' u i| ≤ b :=
    (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hb (congrFun hstate i)).le
  have htc := tangentCoefficients_bound hH hc
  have htc' := tangentCoefficients_bound hH hc'
  have hX : |c 0-c' 0| ≤ b+6*H := by
    have heq : c 0-c' 0=(zx c t-zx c' u)-
        (zx (tangentCoefficients c) t-zx (tangentCoefficients c') u) := by
      simp [zx,tangentCoefficients]
      ring
    rw [heq]
    apply (abs_sub _ _).trans
    apply add_le_add (hgap 1)
    exact (abs_sub _ _).trans ((add_le_add (abs_zx_le htc ht)
      (abs_zx_le htc' hu)).trans_eq (by ring))
  have hY (i : Fin 2) :
      |(if i=0 then c 3 else c 5)-(if i=0 then c' 3 else c' 5)| ≤ b+4*H := by
    have heq : (if i=0 then c 3 else c 5)-(if i=0 then c' 3 else c' 5)=
        (zy c t i-zy c' u i)-(zy (tangentCoefficients c) t i-zy (tangentCoefficients c') u i) := by
      fin_cases i <;> simp [zy,tangentCoefficients] <;> ring
    rw [heq]
    apply (abs_sub _ _).trans
    apply add_le_add (hgap i.succ.succ)
    exact (abs_sub _ _).trans ((add_le_add (abs_zy_le htc ht i)
      (abs_zy_le htc' hu i)).trans_eq (by ring))
  have hdiff (i : Fin 7) (hi : |c i| ≤ H) (hi' : |c' i| ≤ H) :
      |c i-c' i| ≤ b+6*H := by
    have hh := (abs_sub (c i) (c' i)).trans (add_le_add hi hi')
    linarith
  intro i
  fin_cases i
  · exact hX
  · exact hdiff 1 hc.1 hc'.1
  · exact hdiff 2 hc.2.1 hc'.2.1
  · have hh := hY 0
    simp only [ite_true] at hh
    change |c 3-c' 3| ≤ b+6*H
    linarith
  · exact hdiff 4 hc.2.2.1 hc'.2.2.1
  · have hh := hY 1
    norm_num only [Fin.isValue,one_ne_zero,ite_false] at hh
    change |c 5-c' 5| ≤ b+6*H
    linarith
  · exact hdiff 6 hc.2.2.2 hc'.2.2.2

/-- A fine physical state meets a bounded local menu of unit coefficient
worlds, irrespective of any global coefficient range or number of states. -/
theorem exists_unit_coefficient_world_menus {Λ : Type*}
    (E : Set (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) {b H : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hH : 0 ≤ H)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hc : ∀ z∈E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧
      |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H) :
    ∃ menu : (Fin 4 → ℤ) → Finset (Fin 7 → ℤ),
      (∀ q, ((menu q).card : ℝ) ≤ (12*H+4)^7) ∧
      ∀ z∈E, parameterCode 1 (c z.1)∈menu (originalFineState c b z) := by
  classical
  let S := fun q : Fin 4 → ℤ => {z∈E | originalFineState c b z=q}
  have hf (q : Fin 4 → ℤ) :=
    Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PointStateCounts.records_finite_card_of_relative_diameter
      (S q) (fun z : Λ×ℝ => c z.1) (fun _ => 1) (1+6*H)
      (by intro i; norm_num) (by positivity) (by
        intro i z hz z' hz'
        have hh := coefficient_diameter_of_jets_and_state (c z.1) (c z'.1)
          hb hH (ht z hz.1) (ht z' hz'.1) (hc z hz.1) (hc z' hz'.1)
          (hz.2.trans hz'.2.symm) i
        simpa only [mul_one] using hh.trans (by linarith))
  let menu := fun q => (hf q).1.toFinset
  refine ⟨menu,?_,?_⟩
  · intro q
    have hh := (hf q).2
    rw [Set.ncard_eq_toFinset_card _ (hf q).1] at hh
    simpa only [Fintype.card_fin,show 2*(1+6*H)+2=12*H+4 by ring] using hh
  · intro z hz
    apply (hf _).1.mem_toFinset.mpr
    refine ⟨z,⟨hz,rfl⟩,?_⟩
    rfl

/-- Simultaneously prune all unit coefficient worlds using the original
state masses. Every old per-state ratio survives with only the reciprocal
retained-fraction cost; no prior is conditioned on the selected event. -/
theorem original_unit_world_pruning_of_jets {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ×ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (hfull : ∀ᵐ z ∂μ, z∈E) {b H : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hH : 0 ≤ H)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧
      |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H) (f : ENNReal) :
    let state := originalFineState c b
    let world := fun z : Λ×ℝ => parameterCode 1 (c z.1)
    let keep := ParentSource.Broad.Source.LocalMenuFractions.keep μ state world f
    MeasurableSet keep ∧ μ keepᶜ ≤ (f*ENNReal.ofReal ((12*H+4)^7))*μ univ ∧
      ∀ (q : Fin 7 → ℤ) (A : Set (Λ×ℝ)) (ratio : ENNReal), f≠0 → f≠⊤ →
        (∀ w, μ (state ⁻¹' {w}∩A) ≤ ratio*μ (state ⁻¹' {w})) →
        ∀ w, μ (keep∩world ⁻¹' {q}∩state ⁻¹' {w}∩A) ≤
          (ratio/f)*μ (keep∩world ⁻¹' {q}∩state ⁻¹' {w}) := by
  dsimp only
  let state := originalFineState c b
  let world := fun z : Λ×ℝ => parameterCode 1 (c z.1)
  have hs : Measurable state := measurable_originalFineState hc b
  have hw : Measurable world := ((measurable_parameterCode 1).comp hc).comp measurable_fst
  obtain ⟨menu,hmenu,hknown⟩ := exists_unit_coefficient_world_menus E c hb hb1 hH ht hjets
  have hsupport : ∀ᵐ z ∂μ, world z∈menu (state z) := hfull.mono (fun z hz => hknown z hz)
  have hcard (w : Fin 4 → ℤ) : ((menu w).card : ENNReal) ≤ ENNReal.ofReal ((12*H+4)^7) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hmenu w)
  refine ⟨ParentSource.Broad.Source.LocalMenuFractions.measurableSet_keep μ hs hw f,
    ParentSource.Broad.Source.LocalMenuFractions.deletion_le μ hs hw menu hsupport _ f hcard,?_⟩
  intro q A ratio hf0 hftop hratio w
  exact ParentSource.Broad.Source.LocalMenuFractions.state_ratio μ state world
    hf0 hftop q A ratio hratio w

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
