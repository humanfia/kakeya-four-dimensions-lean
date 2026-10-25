-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Frame, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Frame.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Tangent frames for returning isotropic (l = 0) candidates to the original problem.
-- Written by x1078 (o204). Builds on the accepted o280 `k4_finite_affine_candidate_return`
-- (its `PFrame`, `hiddenShear`, `nuE`, `muE`, imported, not copied).
import Submission.Obl.k4_finite_affine_candidate_return.AffineHiddenReturn
import Submission.Obl.k4_finite_affine_candidate_return.MassReturn
import Submission.Obl.k4_finite_affine_candidate_return.ModelEH1
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.StagedInterface

/-!
# Tangent instances in the frozen line coordinates

A parent frame `Φ` (o280's `PFrame`: time `(t - t₀)/q`, base `D⁻¹ (y - c - t u)`, hidden
coordinate rescaled by `sc`) followed by an affine hidden shear `a` sends each original line
`l` to the line `tanLine Φ a l = (l.1, hiddenShear Φ.eb a l)` of the frozen type `Ln`. Its frozen
point `xp (tanLine Φ a l) τ` is exactly o280's model point `exS (hiddenShear Φ.eb a) l τ`.

The tangent prior `tanPrior Φ a ν A₀` is the parent's conditioned prior `nuE ν A₀` pushed to
tangent lines. Its product with Lebesgue time is, on measurable sets, o280's model measure
`muE ν A₀ t₀ q (A₀ ×ˢ univ)` of the pulled-back set (`tanPrior_prod_apply`). This is what lets
the frozen isotropic engines (o295, o288), which are stated for arbitrary data in frozen
coordinates, be applied to a tangent instance and their outputs be returned.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

/-- The tangent line of an original line. -/
def tanLine (Φ : PFrame) (a : Fin 4 → ℝ) (l : Ln) : Ln := (l.1, hiddenShear Φ.eb a l)

lemma xp_tanLine (Φ : PFrame) (a : Fin 4 → ℝ) (l : Ln) (t : ℝ) :
    xp (tanLine Φ a l) t = exS (hiddenShear Φ.eb a) l t := rfl

lemma measurable_tanLine (Φ : PFrame) (a : Fin 4 → ℝ) : Measurable (tanLine Φ a) :=
  measurable_fst.prodMk (measurable_hiddenShear Φ.eb Φ.measurable_eb a)

/-- The tangent event of an original incidence. -/
def tanEvent (Φ : PFrame) (a : Fin 4 → ℝ) (p : Ev) : Ev :=
  (tanLine Φ a p.1, (p.2 - Φ.F.t₀) / Φ.F.q)

/-- The tangent prior: the parent world's conditioned prior on tangent lines. -/
def tanPrior (Φ : PFrame) (a : Fin 4 → ℝ) (ν : Measure Ln) (A₀ : Set Ln) : Measure Ln :=
  Measure.map (tanLine Φ a) (nuE ν A₀)

lemma tanPrior_apply (Φ : PFrame) (a : Fin 4 → ℝ) (ν : Measure Ln) (A₀ : Set Ln)
    {X : Set Ln} (hX : MeasurableSet X) :
    tanPrior Φ a ν A₀ X = nuE ν A₀ (tanLine Φ a ⁻¹' X) :=
  Measure.map_apply (measurable_tanLine Φ a) hX

lemma isProbability_tanPrior (Φ : PFrame) (a : Fin 4 → ℝ) (ν : Measure Ln) (A₀ : Set Ln)
    (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤) : IsProbabilityMeasure (tanPrior Φ a ν A₀) := by
  have := nuE_isProb ν A₀ h0 hT
  unfold tanPrior
  infer_instance

/-- The conditioned prior times Lebesgue time is o280's model measure of the whole parent. -/
lemma nuE_prod_eq_muE (ν : Measure Ln) [SFinite ν] (A₀ : Set Ln) (t₀ q : ℝ) (hq : 0 < q) :
    (nuE ν A₀).prod volume = muE ν A₀ t₀ q (A₀ ×ˢ Set.univ) := by
  have hg : Measurable (fun t : ℝ => (t - t₀) / q) := (measurable_id.sub_const t₀).div_const q
  have hmap : Measure.map (tnorm t₀ q) ((ν.prod volume).restrict (A₀ ×ˢ Set.univ)) =
      ENNReal.ofReal q • ((ν.restrict A₀).prod volume) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ, show tnorm (α := Ln) t₀ q =
      Prod.map id (fun t : ℝ => (t - t₀) / q) from rfl,
      ← Measure.map_prod_map (ν.restrict A₀) volume measurable_id hg, Measure.map_id,
      map_volume_tnorm t₀ q hq, Measure.prod_smul_right]
  rw [muE, hmap, nuE, Measure.prod_smul_left, smul_smul]
  congr 1
  have hq' : ENNReal.ofReal q ≠ 0 := by simpa using hq
  rw [ENNReal.mul_inv (Or.inl hq') (Or.inl ENNReal.ofReal_ne_top), mul_comm _ (ν A₀)⁻¹,
    mul_assoc, ENNReal.inv_mul_cancel hq' ENNReal.ofReal_ne_top, mul_one]

/-- Tangent product mass of a measurable set of tangent events, in o280's model measure. -/
lemma tanPrior_prod_apply (Φ : PFrame) (a : Fin 4 → ℝ) (ν : Measure Ln) [SFinite ν]
    (A₀ : Set Ln) (hq : 0 < Φ.F.q) {X : Set Ev} (hX : MeasurableSet X) :
    ((tanPrior Φ a ν A₀).prod volume) X =
      muE ν A₀ Φ.F.t₀ Φ.F.q (A₀ ×ˢ Set.univ) (Prod.map (tanLine Φ a) id ⁻¹' X) := by
  have hm : Measurable (Prod.map (tanLine Φ a) (id : ℝ → ℝ)) :=
    (measurable_tanLine Φ a).prodMap measurable_id
  have : SFinite (nuE ν A₀) := by unfold nuE; infer_instance
  rw [tanPrior, ← Measure.map_id (μ := volume),
    Measure.map_prod_map (nuE ν A₀) volume (measurable_tanLine Φ a) measurable_id,
    Measure.map_apply hm hX, nuE_prod_eq_muE ν A₀ _ _ hq]

/-- A lower bound for a tangent product mass returns to the unchanged original prior: the
parent mass and the parent time length cancel exactly (o280's `muE_floor_return`). -/
theorem tan_floor_return (Φ : PFrame) (a : Fin 4 → ℝ) (ν : Measure Ln) [SFinite ν]
    (A₀ A : Set Ln) (hA : MeasurableSet A) (hsub : A ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (hq : 0 < Φ.F.q) {X : Set Ev} (hX : MeasurableSet X) (c : ENNReal)
    (hfloor : c * nuE ν A₀ A ≤ ((tanPrior Φ a ν A₀).prod volume) X) :
    ENNReal.ofReal Φ.F.q * c * ν A ≤
      (ν.prod volume) {p | p.1 ∈ A₀ ∧ tanEvent Φ a p ∈ X} := by
  have hm : Measurable (Prod.map (tanLine Φ a) (id : ℝ → ℝ)) :=
    (measurable_tanLine Φ a).prodMap measurable_id
  rw [tanPrior_prod_apply Φ a ν A₀ hq hX] at hfloor
  refine (muE_floor_return ν A₀ A hA hsub h0 hT Φ.F.t₀ Φ.F.q hq _ _ (hm hX) c hfloor).trans
    (measure_mono ?_)
  rintro p ⟨hpX, hpS⟩
  exact ⟨hpS.1, hpX⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
