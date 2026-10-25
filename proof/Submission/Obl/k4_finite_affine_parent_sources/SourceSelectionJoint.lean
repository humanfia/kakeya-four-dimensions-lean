-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceJoint
import Submission.Obl.k4_finite_affine_parent_sources.SourceQGroups
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionCaps

/-!
# Joint caps of a parent-normalised model from kept states

An `EH2` joint cell of a model `muE ... S` (base cube, signal bin, velocity bin) pulls back to an
original base-and-signal cell met with an original velocity event. If `S` lies in the kept part
of an original law `λ` (appended-state floors, `SourceStates`), and the end histories satisfy the
velocity numerator `λ ({end = h} ∩ b) ≤ C w(h) β`, then the joint cell has model mass at most
`(q₀ ν(A₀))⁻¹ (C / δ) β · 81 M`, where `M` bounds the original `λ`-mass of every cell.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The original base of an incidence in the coordinates of a frame. -/
def frameBase (Φ : PFrame) (x : Incidence) : EuclideanSpace ℝ (Fin 3) :=
  nativeBase (framePoint Φ x)

/-- The native signal of a frame's test at an incidence. -/
def frameSignal (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) (x : Incidence) : ℝ :=
  value P (framePoint Φ x)

theorem measurable_frameBase (Φ : PFrame) : Measurable (frameBase Φ) :=
  measurable_nativeBase.comp (measurable_framePoint Φ)

theorem measurable_frameSignal (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) :
    Measurable (frameSignal Φ P) :=
  (continuous_value P).measurable.comp (measurable_framePoint Φ)

/-- The pull-back of an `EH2` joint cell. -/
theorem tnorm_preimage_joint (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) (N u ε' ε'' : ℝ)
    (q : Fin 3 → ℤ) (j v₀ : ℤ) :
    tnorm Φ.F.t₀ Φ.F.q ⁻¹' {y | zS Φ.eb N u y = q ∧
        ⌊eval (exS Φ.eb y.1 y.2) P / ε'⌋ = j ∧ ⌊Φ.eb y.1 3 / ε''⌋ = v₀} =
      bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j ∩
        {x | ⌊Φ.eb x.1 3 / ε''⌋ = v₀} := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, bsCell]
  constructor
  · rintro ⟨hz, hs, hv⟩
    refine ⟨⟨fun i => ?_, hs⟩, hv⟩
    have := congrFun hz i
    fin_cases i <;> exact this
  · rintro ⟨⟨hb, hs⟩, hv⟩
    refine ⟨?_, hs, hv⟩
    funext i
    have := hb i
    fin_cases i <;> exact this

/-- **Joint cells of a model on kept states.** -/
theorem kept_model_joint {H : Type} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H]
    (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) (ν₀ : Measure Trajectory) (A₀ : Set Trajectory)
    (S2 S : Set Incidence) (hS2 : MeasurableSet S2)
    (endL : Incidence → H) (hend : Measurable endL) (w : H → ENNReal)
    {δ : ENNReal} (hδ0 : δ ≠ 0) (hδt : δ ≠ ⊤) {mesh : ℝ} (hmesh : 0 < mesh)
    (hS : S ⊆ S2 ∩ keptSet ((ν₀.prod volume).restrict S2) endL
      (stateCode (frameBase Φ) (frameSignal Φ P) mesh) w δ)
    {N u ε' ε'' : ℝ} (hε : 0 < N ^ (-u)) (hε' : 0 < ε') (hm : mesh ≤ N ^ (-u)) (hm' : mesh ≤ ε')
    (v₀ : ℤ) {C β : ENNReal}
    (hnum : ∀ h, (ν₀.prod volume) (S2 ∩ ({x | endL x = h} ∩ {x | ⌊Φ.eb x.1 3 / ε''⌋ = v₀})) ≤
      C * w h * β)
    (M : ENNReal) (hcell : ∀ q j,
      (ν₀.prod volume) (S2 ∩ bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j) ≤ M)
    (q : Fin 3 → ℤ) (j : ℤ) :
    muE ν₀ A₀ Φ.F.t₀ Φ.F.q S {y | zS Φ.eb N u y = q ∧
        ⌊eval (exS Φ.eb y.1 y.2) P / ε'⌋ = j ∧ ⌊Φ.eb y.1 3 / ε''⌋ = v₀} ≤
      (ENNReal.ofReal Φ.F.q * ν₀ A₀)⁻¹ * (C / δ * β * (81 * M)) := by
  set lam := (ν₀.prod volume).restrict S2 with hlam
  have hcode : Measurable (stateCode (frameBase Φ) (frameSignal Φ P) mesh) := by
    have hb := (WithLp.measurable_ofLp 2 _).comp (measurable_frameBase Φ)
    refine measurable_pi_iff.mpr fun e => Int.measurable_floor.comp ?_
    refine Measurable.div_const ?_ _
    fin_cases e
    · exact hb.eval (a := 0)
    · exact hb.eval (a := 1)
    · exact hb.eval (a := 2)
    · exact measurable_frameSignal Φ P
  have hbm : MeasurableSet {x : Incidence | ⌊Φ.eb x.1 3 / ε''⌋ = v₀} :=
    measurableSet_eq_fun (Int.measurable_floor.comp
      ((((measurable_pi_apply 3).comp Φ.measurable_eb).comp measurable_fst).div_const _))
      measurable_const
  have hx := measurable_exS Φ.measurable_eb
  have hzS : Measurable (fun y : Trajectory × ℝ => zS Φ.eb N u y) := by
    refine measurable_pi_iff.mpr fun e => Int.measurable_floor.comp (Measurable.div_const ?_ _)
    fin_cases e
    · exact measurable_snd
    · exact hx.eval (a := 1)
    · exact hx.eval (a := 2)
  have hEm : MeasurableSet {y : Trajectory × ℝ | zS Φ.eb N u y = q ∧
      ⌊eval (exS Φ.eb y.1 y.2) P / ε'⌋ = j ∧ ⌊Φ.eb y.1 3 / ε''⌋ = v₀} := by
    refine (hzS (measurableSet_singleton q)).inter
      ((measurableSet_eq_fun (Int.measurable_floor.comp
        (((MvPolynomial.continuous_eval P).measurable.comp hx).div_const _))
        measurable_const).inter ?_)
    exact measurableSet_eq_fun (Int.measurable_floor.comp
      ((((measurable_pi_apply 3).comp Φ.measurable_eb).comp measurable_fst).div_const _))
      measurable_const
  rw [muE_apply _ _ _ _ _ hEm, tnorm_preimage_joint]
  gcongr
  have hkm : MeasurableSet (keptSet lam endL (stateCode (frameBase Φ) (frameSignal Φ P) mesh) w δ) :=
    measurableSet_keptSet hend hcode w δ
  have hnum' : ∀ h, lam ({x | endL x = h} ∩ {x | ⌊Φ.eb x.1 3 / ε''⌋ = v₀}) ≤ C * w h * β := by
    intro h
    rw [hlam, Measure.restrict_apply' hS2, inter_comm]
    exact hnum h
  have hcell' : ∀ q j, lam (bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j) ≤ M := by
    intro q j
    rw [hlam, Measure.restrict_apply' hS2, inter_comm]
    exact hcell q j
  have hjoint := kept_cell_joint lam endL hend (frameBase Φ) (frameSignal Φ P) hcode w hδ0 hδt
    hbm hnum' hε hε' hmesh hm hm' M hcell' q j
  calc (ν₀.prod volume) ((bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j ∩
          {x | ⌊Φ.eb x.1 3 / ε''⌋ = v₀}) ∩ S)
      ≤ lam (keptSet lam endL (stateCode (frameBase Φ) (frameSignal Φ P) mesh) w δ ∩
          bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j ∩
          {x | ⌊Φ.eb x.1 3 / ε''⌋ = v₀}) := by
        rw [hlam, Measure.restrict_apply' hS2]
        refine measure_mono fun x hx => ?_
        obtain ⟨⟨hc, hb⟩, hxS⟩ := hx
        exact ⟨⟨⟨(hS hxS).2, hc⟩, hb⟩, (hS hxS).1⟩
    _ ≤ C / δ * β * (81 * M) := hjoint

end

end Submission.Obl.k4_finite_affine_parent_sources
