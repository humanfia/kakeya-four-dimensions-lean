-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionJoint
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionNumerator
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-!
# Joint cells of a source stage on kept states

For a source stage `D` whose prepared set lies in the kept part of a larger prepared set `S2`,
an `EH2` joint cell (base side `N^(-u)`, signal width `N^(-t)`, velocity bin of width `N^(-v)`)
has mass at most `(C / δ) β · 81 · (pure cell bound of S2)`, given the end-history velocity
numerators `(ν × dt)(S2 ∩ {end = h} ∩ bin) ≤ C w(h) β` (`source_joint_cell`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The pull-back of an `EH2` signal cell. -/
theorem tnorm_preimage_cell (Φ : PFrame) (P : MvPolynomial (Fin 4) ℝ) (N u ε' : ℝ)
    (q : Fin 3 → ℤ) (j : ℤ) :
    tnorm Φ.F.t₀ Φ.F.q ⁻¹' {y | zS Φ.eb N u y = q ∧
        ⌊(if true then eval (exS Φ.eb y.1 y.2) P else (exS Φ.eb y.1 y.2) 3) / ε'⌋ = j} =
      bsCell (frameBase Φ) (frameSignal Φ P) (N ^ (-u)) ε' q j := by
  ext x
  simp only [mem_preimage, mem_ofPred_eq, bsCell, ↓reduceIte]
  constructor
  · rintro ⟨hz, hs⟩
    refine ⟨fun i => ?_, hs⟩
    have := congrFun hz i
    fin_cases i <;> exact this
  · rintro ⟨hb, hs⟩
    refine ⟨?_, hs⟩
    funext i
    have := hb i
    fin_cases i <;> exact this

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The original mass of a model event of a source stage. -/
theorem stage_mu_apply (D : SourceData p) (unit : ℝ) {X : Set (Trajectory × ℝ)}
    (hX : MeasurableSet X) :
    (D.stage Nk L unit ν B).μ X =
      (ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ *
        ((ν D.w₀).prod volume) (tnorm D.t₀ D.q₀ ⁻¹' X ∩ D.S) := by
  show muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S X = _
  rw [muE_apply _ _ _ _ _ hX]

/-- **Joint cells of a source stage on kept states.** -/
theorem source_joint_cell {H : Type} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H] (D : SourceData p) (unit : ℝ)
    (S2 : Set Incidence) (hS2 : MeasurableSet S2)
    (endL : Incidence → H) (hend : Measurable endL) (w : H → ENNReal)
    {δs : ENNReal} (hδ0 : δs ≠ 0) (hδt : δs ≠ ⊤) {mesh : ℝ} (hmesh : 0 < mesh)
    (hDS : D.S ⊆ S2 ∩ keptSet ((ν D.w₀).prod volume |>.restrict S2) endL
      (stateCode (frameBase (D.frame Nk B))
        (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P) mesh) w δs)
    {u t v : ℝ} (hε : 0 < (Nk ^ (unit * L)) ^ (-u)) (hε' : 0 < (Nk ^ (unit * L)) ^ (-t))
    (hm : mesh ≤ (Nk ^ (unit * L)) ^ (-u)) (hm' : mesh ≤ (Nk ^ (unit * L)) ^ (-t))
    (v₀ : ℤ) {C β : ENNReal}
    (hnum : ∀ h, ((ν D.w₀).prod volume) (S2 ∩ ({x | endL x = h} ∩
      {x | ⌊(D.frame Nk B).eb x.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀})) ≤ C * w h * β)
    (M : ENNReal)
    (hcell : ∀ q j, ((ν D.w₀).prod volume) (S2 ∩ bsCell (frameBase (D.frame Nk B))
      (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
      ((Nk ^ (unit * L)) ^ (-u)) ((Nk ^ (unit * L)) ^ (-t)) q j) ≤ M)
    (q : Fin 3 → ℤ) (j : ℤ) :
    (D.stage Nk L unit ν B).μ {y | zS (D.stage Nk L unit ν B).b (D.stage Nk L unit ν B).N u y = q ∧
        ⌊eval (exS (D.stage Nk L unit ν B).b y.1 y.2) (D.stage Nk L unit ν B).P /
          ((D.stage Nk L unit ν B).N ^ (-t))⌋ = j ∧
        ⌊(D.stage Nk L unit ν B).b y.1 3 / ((D.stage Nk L unit ν B).N ^ (-v))⌋ = v₀} ≤
      (ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ * (C / δs * β * (81 * M)) := by
  have hF : (D.frame Nk B).F.t₀ = D.t₀ ∧ (D.frame Nk B).F.q = D.q₀ := by
    rw [D.frame_F]; exact ⟨rfl, rfl⟩
  have h := kept_model_joint (D.frame Nk B) (D.stage Nk L unit ν B).P (ν D.w₀)
    (p.assigned D.parent) S2 D.S hS2 endL hend w hδ0 hδt hmesh hDS hε hε' hm hm' v₀ hnum M
    hcell q j
  rw [hF.1, hF.2] at h
  exact h

/-- The original mass of a signal cell of a prepared set, from the model cell bound. -/
theorem cell_original_le (D : SourceData p) (unit : ℝ) {u t : ℝ} (q : Fin 3 → ℤ) (j : ℤ)
    (Mmod : ENNReal)
    (hmod : (D.stage Nk L unit ν B).μ {y | zS (D.stage Nk L unit ν B).b
        (D.stage Nk L unit ν B).N u y = q ∧
        ⌊(if true then eval (exS (D.stage Nk L unit ν B).b y.1 y.2) (D.stage Nk L unit ν B).P
          else (exS (D.stage Nk L unit ν B).b y.1 y.2) 3) /
          ((D.stage Nk L unit ν B).N ^ (-t))⌋ = j} ≤ Mmod)
    (hA : ν D.w₀ (p.assigned D.parent) ≠ ⊤) (hA0 : ν D.w₀ (p.assigned D.parent) ≠ 0) :
    ((ν D.w₀).prod volume) (D.S ∩ bsCell (frameBase (D.frame Nk B))
      (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
      ((Nk ^ (unit * L)) ^ (-u)) ((Nk ^ (unit * L)) ^ (-t)) q j) ≤
      ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent) * Mmod := by
  have hF : (D.frame Nk B).F.t₀ = D.t₀ ∧ (D.frame Nk B).F.q = D.q₀ := by
    rw [D.frame_F]; exact ⟨rfl, rfl⟩
  have hb := SourceData.stage_b_measurable D unit (Nk := Nk) (L := L) (ν := ν) (B := B)
  have hx := measurable_exS hb
  have hzS : Measurable (fun y : Trajectory × ℝ =>
      zS (D.stage Nk L unit ν B).b (D.stage Nk L unit ν B).N u y) := by
    refine measurable_pi_iff.mpr fun e => Int.measurable_floor.comp (Measurable.div_const ?_ _)
    fin_cases e
    · exact measurable_snd
    · exact hx.eval (a := 1)
    · exact hx.eval (a := 2)
  have hXm : MeasurableSet {y : Trajectory × ℝ | zS (D.stage Nk L unit ν B).b
      (D.stage Nk L unit ν B).N u y = q ∧
      ⌊(if true then eval (exS (D.stage Nk L unit ν B).b y.1 y.2) (D.stage Nk L unit ν B).P
        else (exS (D.stage Nk L unit ν B).b y.1 y.2) 3) /
        ((D.stage Nk L unit ν B).N ^ (-t))⌋ = j} := by
    simp only [↓reduceIte]
    exact (hzS (measurableSet_singleton q)).inter
      (measurableSet_eq_fun (Int.measurable_floor.comp
        (((MvPolynomial.continuous_eval _).measurable.comp hx).div_const _)) measurable_const)
  have hμ := stage_mu_apply hp D unit hXm
  have hpre := tnorm_preimage_cell (D.frame Nk B) (D.stage Nk L unit ν B).P
    (Nk ^ (unit * L)) u ((Nk ^ (unit * L)) ^ (-t)) q j
  rw [hF.1, hF.2] at hpre
  have hpre' : tnorm D.t₀ D.q₀ ⁻¹' {y : Trajectory × ℝ | zS (D.stage Nk L unit ν B).b
      (D.stage Nk L unit ν B).N u y = q ∧
      ⌊(if true then eval (exS (D.stage Nk L unit ν B).b y.1 y.2) (D.stage Nk L unit ν B).P
        else (exS (D.stage Nk L unit ν B).b y.1 y.2) 3) /
        ((D.stage Nk L unit ν B).N ^ (-t))⌋ = j} =
      bsCell (frameBase (D.frame Nk B)) (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
        ((Nk ^ (unit * L)) ^ (-u)) ((Nk ^ (unit * L)) ^ (-t)) q j := hpre
  rw [hpre'] at hμ
  have hq0 : 0 < D.q₀ := D.q₀_pos
  set c := ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent)
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  rw [inter_comm]
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr hq0).ne' hA0
  calc ((ν D.w₀).prod volume) (bsCell (frameBase (D.frame Nk B))
          (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
          ((Nk ^ (unit * L)) ^ (-u)) ((Nk ^ (unit * L)) ^ (-t)) q j ∩ D.S)
        = c * (c⁻¹ * ((ν D.w₀).prod volume) (bsCell (frameBase (D.frame Nk B))
          (frameSignal (D.frame Nk B) (D.stage Nk L unit ν B).P)
          ((Nk ^ (unit * L)) ^ (-u)) ((Nk ^ (unit * L)) ^ (-t)) q j ∩ D.S)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
      _ ≤ c * Mmod := by rw [← hμ]; gcongr

/-- The stage's frame is the parent's label frame. -/
theorem frame_eq_labelFrame (D : SourceData p) (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) :
    D.frame Nk B = labelFrame p D.parent (B (p.world D.parent)) (δ Nk (p.r (p.lev D.parent))) := by
  show affineSourceFrame D.t₀ D.q₀ (B D.w₀ / δ Nk (p.r D.i₀)) (p.center D.parent)
    (p.velocity D.parent) D.D₀ = _
  rw [hD₀]
  rfl

/-- **Native bounds of a source stage** almost everywhere: base coordinates, the parent test
and its hidden derivatives are at most `7 κ`. -/
theorem stage_good_bounds (D : SourceData p) (unit : ℝ) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hScount : D.S ⊆ p.counted D.parent) :
    ∀ᵐ y ∂(D.stage Nk L unit ν B).μ,
      (∀ i : Fin 3, |exS (D.stage Nk L unit ν B).b y.1 y.2 i.castSucc| ≤ 7 * p.κ) ∧
      |eval (exS (D.stage Nk L unit ν B).b y.1 y.2) (D.stage Nk L unit ν B).P| ≤ 7 * p.κ ∧
      |eval (exS (D.stage Nk L unit ν B).b y.1 y.2)
        (pderiv (3 : Fin 4) (D.stage Nk L unit ν B).P)| ≤ 7 * p.κ ∧
      |eval (exS (D.stage Nk L unit ν B).b y.1 y.2)
        (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (D.stage Nk L unit ν B).P))| ≤ 7 * p.κ := by
  have hq : 0 < (D.frame Nk B).F.q := by rw [D.frame_F]; exact D.q₀_pos
  have hμ : (D.stage Nk L unit ν B).μ =
      muE (ν D.w₀) (p.assigned D.parent) (D.frame Nk B).F.t₀ (D.frame Nk B).F.q D.S := by
    rw [D.frame_F]; rfl
  have hbeq : (D.stage Nk L unit ν B).b = (D.frame Nk B).eb := rfl
  have hPeq : (D.stage Nk L unit ν B).P =
      (D.frame Nk B).normTest (δ Nk (p.r (p.lev D.parent))) (p.test D.parent) := rfl
  rw [hμ, hbeq, hPeq]
  refine ae_muE_of_forall _ _ _ _ hq.ne' hSm fun x hx => ?_
  have hg := label_framePoint_good hp D.parent D.parent
    (Submission.Obl.k4_finite_forest_width_selection.forestAncestor_self p.lev p.par D.parent)
    le_rfl hBw (hScount hx)
  rw [← frame_eq_labelFrame hp D hD₀] at hg
  obtain ⟨h1, -, -, -, -, h6, h7, h8⟩ := hg
  have hdeg : ((D.frame Nk B).normTest (δ Nk (p.r (p.lev D.parent))) (p.test D.parent)).totalDegree
      ≤ 2 :=
    ((D.frame Nk B).totalDegree_normTest_le _ _).trans (hp.chart D.parent).2.2.2.2.1
  refine ⟨fun i => ?_, h6, h7, ?_⟩
  · have hle : |(nativeBase (framePoint (D.frame Nk B) x)) i| ≤
        ‖nativeBase (framePoint (D.frame Nk B) x)‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (nativeBase (framePoint (D.frame Nk B) x)) i
    refine le_trans (le_of_eq ?_) (hle.trans h1)
    fin_cases i <;> rfl
  · have hc := Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature _ hdeg 3
    rw [hc, eval_C]
    exact h8

end

end

end Submission.Obl.k4_finite_affine_parent_sources
