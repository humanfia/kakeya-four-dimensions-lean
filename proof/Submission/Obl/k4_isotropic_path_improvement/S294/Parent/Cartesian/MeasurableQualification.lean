-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Cartesian.MeasurableQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Cartesian/MeasurableQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian.QualWitness
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeQualification

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian

open Set MeasureTheory
open scoped ENNReal

noncomputable section

open Qualification.Jets2

/-- Qualification with polynomials on a fixed coefficient grid, in the
normalized time of one original block. The witness times remain in Eref. -/
def GridQualWitness {Λ σ : Type*} (Eref : Set (Λ × ℝ))
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ) (t0 h : ℝ) (M : ℕ)
    (mesh : ℝ) (limit : ℤ) (err dur : ℝ) (w : Λ × ℝ) : Prop :=
  ∃ a : Fin 3 → Fin (M+1) → ℤ, (∀ i k, |a i k| ≤ limit) ∧
    (∀ i, |Gs (st w) i-(gridPoly mesh (a i)).eval ((w.2-t0)/h)| ≤ err) ∧
    ENNReal.ofReal dur ≤ volume {s : ℝ | s∈Icc (0:ℝ) 1 ∧
      (w.1,t0+h*s)∈Eref ∧
      ∀ i, |Gs (st (w.1,t0+h*s)) i-(gridPoly mesh (a i)).eval s| ≤ err}

/-- The normalized-block grid test is measurable, without requiring that
the unrestricted existential polynomial test be measurable. -/
theorem measurableSet_gridQualWitness {Λ σ : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hEref : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st)) (t0 h : ℝ) (M : ℕ)
    (mesh : ℝ) (limit : ℤ) (err dur : ℝ) :
    MeasurableSet {w | GridQualWitness Eref st Gs t0 h M mesh limit err dur w} := by
  have heq : {w | GridQualWitness Eref st Gs t0 h M mesh limit err dur w} =
      ⋃ a : Fin 3 → Fin (M+1) → ℤ,
        {w : Λ × ℝ | ∀ i k, |a i k| ≤ limit} ∩
        ({w | ∀ i, |Gs (st w) i-(gridPoly mesh (a i)).eval ((w.2-t0)/h)| ≤ err} ∩
        {w | ENNReal.ofReal dur ≤ volume {s : ℝ | s∈Icc (0:ℝ) 1 ∧
          (w.1,t0+h*s)∈Eref ∧
          ∀ i, |Gs (st (w.1,t0+h*s)) i-(gridPoly mesh (a i)).eval s| ≤ err}}) := by
    ext w
    simp only [mem_ofPred_eq, GridQualWitness, mem_iUnion, mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro a
  refine (MeasurableSet.const _).inter ((measurableSet_gridFit hG M mesh err a
    measurable_id ((measurable_snd.sub_const t0).div_const h)).inter ?_)
  let S : Set ((Λ × ℝ) × ℝ) := {q | q.2∈Icc (0:ℝ) 1 ∧
    (q.1.1,t0+h*q.2)∈Eref ∧
    ∀ i, |Gs (st (q.1.1,t0+h*q.2)) i-(gridPoly mesh (a i)).eval q.2| ≤ err}
  have hmap : Measurable (fun q : (Λ × ℝ) × ℝ => (q.1.1,t0+h*q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_const.add
      (measurable_const.mul measurable_snd))
  have hS : MeasurableSet S :=
    ((measurableSet_Icc.preimage measurable_snd).inter
      ((hEref.preimage hmap).inter
        (measurableSet_gridFit hG M mesh err a hmap measurable_snd)))
  exact measurableSet_le measurable_const (measurable_measure_prodMk_left hS)

/-- Rounding a genuine normalized-block fit preserves every witness time.
No measurable choice of its polynomial is required. -/
theorem gridQualWitness_of_qualWitness {Λ σ : Type*}
    {Eref : Set (Λ × ℝ)} {st : Λ × ℝ → σ} {Gs : σ → Fin 3 → ℝ}
    {t0 h K err dur mesh : ℝ} {M : ℕ} {w : Λ × ℝ}
    (hmesh : 0 < mesh) (htime : (w.2-t0)/h∈Icc (0:ℝ) 1)
    (hq : QualWitness Eref st Gs t0 h M K err dur w) :
    GridQualWitness Eref st Gs t0 h M mesh (⌈K/mesh⌉+1)
      (err+(M+1)*mesh) dur w := by
  obtain ⟨P,hdeg,hcoeff,hfit,E,hEm,hE,hvol,hwit⟩ := hq
  refine ⟨fun i => meshCoords mesh M (P i),fun i k =>
    abs_meshCoords_le hmesh (hcoeff i) k,?_,hvol.trans (measure_mono ?_)⟩
  · intro i
    exact (abs_sub_le _ ((P i).eval ((w.2-t0)/h)) _).trans
      (add_le_add (hfit i) (abs_eval_sub_gridPoly_le hmesh (hdeg i)
        (abs_le.mpr ⟨by linarith [htime.1],htime.2⟩)))
  · intro s hs
    obtain ⟨hsE,hsfit⟩ := hwit s hs
    refine ⟨hE hs,hsE,fun i => ?_⟩
    exact (abs_sub_le _ ((P i).eval s) _).trans
      (add_le_add (hsfit i) (abs_eval_sub_gridPoly_le hmesh (hdeg i)
        (abs_le.mpr ⟨by linarith [(hE hs).1],(hE hs).2⟩)))

/-- A grid-qualified occurrence supplies a genuine measurable set of
ordinary normalized witness times on its original indexed line. -/
theorem qualWitness_of_gridQualWitness {Λ σ : Type*} [MeasurableSpace Λ]
    {Eref : Set (Λ × ℝ)} (hEref : MeasurableSet Eref)
    {st : Λ × ℝ → σ} {Gs : σ → Fin 3 → ℝ}
    (hG : Measurable (Gs ∘ st)) {t0 h mesh err dur : ℝ}
    {M : ℕ} {limit : ℤ} {w : Λ × ℝ} (hmesh : 0 ≤ mesh)
    (hq : GridQualWitness Eref st Gs t0 h M mesh limit err dur w) :
    QualWitness Eref st Gs t0 h M (mesh*limit) err dur w := by
  obtain ⟨a,ha,hfit,hvol⟩ := hq
  let E := {s : ℝ | s∈Icc (0:ℝ) 1 ∧ (w.1,t0+h*s)∈Eref ∧
    ∀ i, |Gs (st (w.1,t0+h*s)) i-(gridPoly mesh (a i)).eval s| ≤ err}
  refine ⟨fun i => gridPoly mesh (a i),fun i => natDegree_gridPoly_le mesh (a i),
    fun i n => abs_coeff_gridPoly_le hmesh (ha i) n,hfit,E,?_,?_,hvol,?_⟩
  · have hm : Measurable (fun s : ℝ => (w.1,t0+h*s)) :=
      measurable_const.prodMk (measurable_const.add (measurable_const.mul measurable_id))
    exact measurableSet_Icc.inter ((hEref.preimage hm).inter
      (measurableSet_gridFit hG M mesh err a hm measurable_id))
  · exact fun _ hs => hs.1
  · exact fun _ hs => hs.2

/-- Enlarging the coefficient and fit budgets keeps the same polynomial
and the same measurable set of witness times. -/
theorem QualWitness.mono {Λ σ : Type*} {Eref : Set (Λ × ℝ)}
    {st : Λ × ℝ → σ} {Gs : σ → Fin 3 → ℝ} {t0 h K K' err err' dur dur' : ℝ}
    {M : ℕ} {w : Λ × ℝ}
    (hq : QualWitness Eref st Gs t0 h M K err dur w)
    (hK : K ≤ K') (he : err ≤ err') (hd : dur' ≤ dur) :
    QualWitness Eref st Gs t0 h M K' err' dur' w := by
  obtain ⟨P,hdeg,hcoeff,hfit,E,hEm,hE,hvol,hwit⟩ := hq
  exact ⟨P,hdeg,fun i n => (hcoeff i n).trans hK,
    fun i => (hfit i).trans he,E,hEm,hE,
    (ENNReal.ofReal_le_ofReal hd).trans hvol,
    fun s hs => ⟨(hwit s hs).1,fun i => ((hwit s hs).2 i).trans he⟩⟩

/-- A measurable envelope of all genuinely qualified occurrences in one
original block. Coefficient rounding increases the fit error by exactly
`(M+1)*mesh`; no occurrence or witness time is lost. -/
theorem exists_measurable_qualification_envelope {Λ σ : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hEref : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ) (hG : Measurable (Gs ∘ st))
    (t0 : ℝ) {h : ℝ} (hh : 0 < h) (M : ℕ) (K err dur : ℝ)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ Q : Set (Λ × ℝ), MeasurableSet Q ∧
      Q ⊆ Eref ∩ (univ ×ˢ Icc t0 (t0+h)) ∧
      (∀ w∈Eref, w.2∈Icc t0 (t0+h) →
        QualWitness Eref st Gs t0 h M K err dur w → w∈Q) ∧
      ∀ w∈Q, QualWitness Eref st Gs t0 h M (K+2*mesh)
        (err+(M+1)*mesh) dur w := by
  let limit : ℤ := ⌈K/mesh⌉+1
  let Q : Set (Λ × ℝ) := (Eref ∩ (univ ×ˢ Icc t0 (t0+h))) ∩
    {w | GridQualWitness Eref st Gs t0 h M mesh limit (err+(M+1)*mesh) dur w}
  have hlimit : mesh*(limit:ℝ) ≤ K+2*mesh := by
    have hc := mul_le_mul_of_nonneg_left (Int.ceil_lt_add_one (K/mesh)).le hmesh.le
    rw [mul_add,mul_div_cancel₀ _ hmesh.ne',mul_one] at hc
    dsimp only [limit]
    push_cast
    nlinarith
  refine ⟨Q,(hEref.inter (MeasurableSet.univ.prod measurableSet_Icc)).inter
    (measurableSet_gridQualWitness Eref hEref st Gs hG t0 h M mesh limit
      (err+(M+1)*mesh) dur),inter_subset_left,?_,?_⟩
  · intro w hw htime hq
    have ht : (w.2-t0)/h∈Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr htime.1) hh.le
      · rw [div_le_one hh]
        linarith [htime.2]
    exact ⟨⟨hw,mem_univ _,htime⟩,gridQualWitness_of_qualWitness hmesh ht hq⟩
  · intro w hw
    exact (qualWitness_of_gridQualWitness hEref hG hmesh.le hw.2).mono
      hlimit le_rfl le_rfl

/-- The form used by a row packet: arbitrarily chosen polynomial witnesses
can be replaced by one measurable qualifying set, with both budgets doubled. -/
theorem exists_measurable_qualification_double {Λ σ : Type*} [MeasurableSpace Λ]
    (Eref : Set (Λ × ℝ)) (hEref : MeasurableSet Eref)
    (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ) (hG : Measurable (Gs ∘ st))
    (t0 : ℝ) {h : ℝ} (hh : 0 < h) (M : ℕ) (K dur : ℝ)
    {err : ℝ} (herr : 0 < err) (hbudget : 2*err ≤ K) :
    ∃ Q : Set (Λ × ℝ), MeasurableSet Q ∧
      Q ⊆ Eref ∩ (univ ×ˢ Icc t0 (t0+h)) ∧
      (∀ w∈Eref, w.2∈Icc t0 (t0+h) →
        QualWitness Eref st Gs t0 h M K err dur w → w∈Q) ∧
      ∀ w∈Q, QualWitness Eref st Gs t0 h M (2*K) (2*err) dur w := by
  have hM : (0:ℝ) < M+1 := by positivity
  have hM1 : (1:ℝ) ≤ M+1 := by have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M; linarith
  have hmesh : 0 < err/(M+1) := div_pos herr hM
  have hmesherr : err/(M+1) ≤ err := div_le_self herr.le hM1
  obtain ⟨Q,hQ,hQE,hcover,hfit⟩ := exists_measurable_qualification_envelope
    Eref hEref st Gs hG t0 hh M K err dur hmesh
  refine ⟨Q,hQ,hQE,hcover,fun w hw => ?_⟩
  have herror : err+(M+1)*(err/(M+1)) = 2*err := by
    rw [mul_div_cancel₀ _ hM.ne']; ring
  have hcoeff : K+2*(err/(M+1)) ≤ 2*K := by linarith
  exact (hfit w hw).mono hcoeff herror.le le_rfl

/-- An outer-measure failure bound already supplies a measurable core of
successful points. No measurability of the property itself is needed. -/
theorem exists_measurable_property_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (property : Ω → Prop) :
    ∃ Q : Set Ω, MeasurableSet Q ∧ Q ⊆ E ∧
      (∀ w∈Q, property w) ∧ μ (E\Q) ≤ μ {w | ¬property w} := by
  classical
  let bad : Set Ω := {w | ¬property w}
  let Q := E\toMeasurable μ bad
  refine ⟨Q,hE.diff (measurableSet_toMeasurable μ bad),sdiff_subset,?_,?_⟩
  · intro w hw
    by_contra hn
    exact hw.2 (subset_toMeasurable μ bad hn)
  · calc
      μ (E\Q) ≤ μ (toMeasurable μ bad) := measure_mono (by
        intro w hw
        by_contra hn
        exact hw.2 ⟨hw.1,hn⟩)
      _ = μ {w | ¬property w} := measure_toMeasurable bad

/-- A measurable qualifying core with exactly the original polynomial,
error and duration budgets, even when the preceding reference is arbitrary. -/
theorem exists_measurable_qualification_core {Λ σ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (Eref : Set (Λ × ℝ)) (st : Λ × ℝ → σ) (Gs : σ → Fin 3 → ℝ)
    (t0 h : ℝ) (M : ℕ) (K err dur : ℝ) :
    ∃ Q : Set (Λ × ℝ), MeasurableSet Q ∧ Q ⊆ E ∧
      (∀ w∈Q, QualWitness Eref st Gs t0 h M K err dur w) ∧
      μ (E\Q) ≤ μ {w | ¬QualWitness Eref st Gs t0 h M K err dur w} :=
  exists_measurable_property_core μ E hE
    (QualWitness Eref st Gs t0 h M K err dur)

/-- For a law concentrated on the source, the measurable core's whole
complement costs at most the original outer measure of failure. -/
theorem exists_measurable_property_core_of_concentrated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (hfull : μ Eᶜ=0)
    (property : Ω → Prop) :
    ∃ Q : Set Ω, MeasurableSet Q ∧ Q ⊆ E ∧
      (∀ w∈Q, property w) ∧ μ Qᶜ ≤ μ {w | ¬property w} := by
  obtain ⟨Q,hQ,hQE,hprop,hloss⟩ := exists_measurable_property_core μ E hE property
  refine ⟨Q,hQ,hQE,hprop,?_⟩
  have hsub : Qᶜ ⊆ Eᶜ ∪ (E\Q) := by
    intro w hw
    by_cases hwe : w∈E
    · exact Or.inr ⟨hwe,hw⟩
    · exact Or.inl hwe
  calc
    μ Qᶜ ≤ μ Eᶜ+μ (E\Q) := (measure_mono hsub).trans (measure_union_le _ _)
    _ = μ (E\Q) := by rw [hfull,zero_add]
    _ ≤ μ {w | ¬property w} := hloss

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian
