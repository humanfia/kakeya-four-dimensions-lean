-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.QualificationClock

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set Polynomial

noncomputable section

namespace AncestorQualification

/-- Read an original incidence in the unit clock of one earlier ancestor.
The original trajectory index is retained. -/
def fromAncestor {Λ : Type*} (tA hA : ℝ) (z : Λ × ℝ) : Λ × ℝ :=
  (z.1, tA + hA * z.2)

def event {Λ : Type*} (tA hA : ℝ) (E : Set (Λ × ℝ)) : Set (Λ × ℝ) :=
  fromAncestor tA hA ⁻¹' E

theorem measurable_fromAncestor {Λ : Type*} [MeasurableSpace Λ] (tA hA : ℝ) :
    Measurable (fromAncestor (Λ := Λ) tA hA) := by
  exact measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

/-- A true old label confines all witnesses to that old block, even when
the preceding reference contains many different old packets. -/
theorem qualWitness_of_native_label {Λ σ ι : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hE : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st)) (lab : Λ × ℝ → ι)
    {M T : ℕ} {K err dur t0 h : ℝ} (hK : 0 ≤ K)
    (ht0 : 0 ≤ t0) (ht01 : t0 ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    {w : Λ × ℝ}
    (hlabel : ∀ t, (w.1,t)∈Eref → lab (w.1,t)=lab w → t∈Icc t0 (t0+h))
    (hq : Qualification.Jets2.NativeQualified Eref lab (Gs ∘ st) M T K err dur w) :
    Cartesian.QualWitness Eref st Gs t0 h M (QualificationClock.coefficientCost M*K)
      err (dur/h) w := by
  rcases hq with ⟨Q,hdeg,hcoeff,hpoint,hmass⟩
  let R : Set ℝ := {t | t∈Icc t0 (t0+h) ∧ (w.1,t)∈Eref ∧
    ∀ j, |Gs (st (w.1,t)) j-(Q j).eval t|≤err}
  have hRm : MeasurableSet R := by
    apply measurableSet_Icc.inter
    apply (hE.preimage (measurable_const.prodMk measurable_id)).inter
    have hm : Measurable (fun t : ℝ => (w.1,t)) := measurable_const.prodMk measurable_id
    have hf j : MeasurableSet {t : ℝ | |Gs (st (w.1,t)) j-(Q j).eval t|≤err} :=
      measurableSet_le (((measurable_pi_apply j).comp (hG.comp hm)).sub
        (Q j).continuous.measurable).abs measurable_const
    exact (MeasurableSet.iInter hf).congr (by
      ext t
      simp only [mem_iInter,mem_setOf_eq]
      rfl)
  have hRmass : ENNReal.ofReal dur≤volume R := hmass.trans (measure_mono (by
    intro t ht
    exact ⟨hlabel t ht.2.1 ht.2.2.1,ht.2.1,ht.2.2.2⟩))
  let B := (fun s : ℝ => t0+h*s) ⁻¹' R
  refine ⟨fun j => QualificationClock.retime t0 h (Q j),
    fun j => QualificationClock.degree_retime t0 hh.ne' (hdeg j),
    fun j n => QualificationClock.coeff_retime (hdeg j) hK (hcoeff j) ht0 ht01 hh hh1 n,
    ?_,B,hRm.preimage (by fun_prop),?_,?_,?_⟩
  · intro j
    simpa only [Function.comp_apply,QualificationClock.eval_retime,
      show t0+h*((w.2-t0)/h)=w.2 by field_simp; ring] using hpoint j
  · intro s hs
    have hb := hs.1
    change t0≤t0+h*s ∧ t0+h*s≤t0+h at hb
    constructor <;> nlinarith
  · rw [show volume B=ENNReal.ofReal h⁻¹*volume R from QualificationClock.volume_retime t0 hh R,
      ENNReal.ofReal_div_of_pos hh,div_eq_mul_inv,
      ←ENNReal.ofReal_inv_of_pos hh,mul_comm]
    exact mul_le_mul' le_rfl hRmass
  · intro s hs
    exact ⟨hs.2.1,fun j => by simpa only [QualificationClock.eval_retime] using hs.2.2 j⟩

/-- A witness in the shallow ancestor clock is the same witness in the
original old packet. Its normalized times and polynomial stay unchanged. -/
theorem pullback_qualWitness {Λ σ : Type*}
    (Eref : Set (Λ × ℝ)) (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    {tA hA t0 h K err dur : ℝ} (hhA : hA≠0) (hh : h≠0)
    {M : ℕ} {w : Λ × ℝ}
    (hq : Cartesian.QualWitness (event tA hA Eref) (st ∘ fromAncestor tA hA) Gs
      ((t0-tA)/hA) (h/hA) M K err dur (w.1,(w.2-tA)/hA)) :
    Cartesian.QualWitness Eref st Gs t0 h M K err dur w := by
  rcases hq with ⟨Q,hdeg,hcoeff,hpoint,R,hRm,hR,hvol,hfit⟩
  have hreconstruct : tA+hA*((w.2-tA)/hA)=w.2 := by field_simp; ring
  have hnormalized : (((w.2-tA)/hA)-(t0-tA)/hA)/(h/hA)=(w.2-t0)/h := by
    field_simp
    ring
  have htime (s : ℝ) : tA+hA*((t0-tA)/hA+(h/hA)*s)=t0+h*s := by
    field_simp
    ring
  refine ⟨Q,hdeg,hcoeff,?_,R,hRm,hR,hvol,?_⟩
  · intro j
    simpa only [Function.comp_apply,fromAncestor,hreconstruct,hnormalized] using hpoint j
  · intro s hs
    have hp := hfit s hs
    simpa only [event,mem_preimage,Function.comp_apply,fromAncestor,htime] using hp

/-- Qualify in the shallow ancestor, then use the polynomial on its
actual original old block. The duration is normalized only by that block. -/
theorem qualWitness_of_native_in_ancestor {Λ σ ι : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hE : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st)) (lab : Λ × ℝ → ι)
    {M T : ℕ} {tA hA t0 h K err dur : ℝ}
    (hhA : 0 < hA) (hh : 0 < h) (hhAold : h ≤ hA)
    (ht0 : tA ≤ t0) (ht01 : t0 ≤ tA+hA) (hK : 0 ≤ K)
    {w : Λ × ℝ}
    (hlabel : ∀ t, (w.1,t)∈Eref →
      lab (w.1,(t-tA)/hA)=lab (w.1,(w.2-tA)/hA) → t∈Icc t0 (t0+h))
    (hq : Qualification.Jets2.NativeQualified (event tA hA Eref) lab
      (Gs ∘ (st ∘ fromAncestor tA hA)) M T K err dur (w.1,(w.2-tA)/hA)) :
    Cartesian.QualWitness Eref st Gs t0 h M (QualificationClock.coefficientCost M*K)
      err (dur/(h/hA)) w := by
  apply pullback_qualWitness Eref st Gs hhA.ne' hh.ne'
  apply qualWitness_of_native_label (event tA hA Eref)
    (hE.preimage (measurable_fromAncestor tA hA)) (st ∘ fromAncestor tA hA) Gs
    (hG.comp (measurable_fromAncestor tA hA)) lab hK
    (div_nonneg (sub_nonneg.mpr ht0) hhA.le)
    ((div_le_one hhA).mpr (by linarith)) (div_pos hh hhA)
    ((div_le_one hhA).mpr hhAold) _ hq
  intro u hu hlab
  have htime : (tA+hA*u-tA)/hA=u := by field_simp; ring
  have hb := hlabel (tA+hA*u) hu (by simpa only [htime] using hlab)
  constructor
  · exact (div_le_iff₀ hhA).mpr (by nlinarith [hb.1])
  · have heq : (t0-tA)/hA+h/hA=(t0+h-tA)/hA := by ring
    rw [heq]
    exact (le_div_iff₀ hhA).mpr (by nlinarith [hb.2])

end AncestorQualification

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
