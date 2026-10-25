-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/DenseJet/RealJets.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/RealJets.lean.
import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry

/-!
# Real jets of the real slice of a holomorphic function

A real function which is the real slice of a complex-smooth function has real
Fréchet jets dominated by the complex Fréchet jets at the same point.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.DenseJet

open Set Metric Filter
open scoped Topology ContDiff

/-- The real slice of complex Euclidean space, as a continuous real-linear map. -/
noncomputable def realSlice : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℂ (Fin 3) :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).toContinuousLinearMap

lemma realSlice_apply (x : EuclideanSpace ℝ (Fin 3)) :
    realSlice x = WithLp.toLp 2 (fun i => (x i : ℂ)) := rfl

lemma norm_realSlice_apply (x : EuclideanSpace ℝ (Fin 3)) : ‖realSlice x‖ = ‖x‖ :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding 3).norm_map x

lemma norm_realSlice_le : ‖realSlice‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

lemma iteratedFDeriv_real_eq_restrictScalars {F : EuclideanSpace ℂ (Fin 3) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin 3))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {z : EuclideanSpace ℂ (Fin 3)} (hz : z ∈ U) :
    iteratedFDeriv ℝ j F z = (iteratedFDeriv ℂ j F z).restrictScalars ℝ := by
  have hFat : ContDiffAt ℂ j F z :=
    (hF.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  exact (hFat.restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm

lemma iteratedFDeriv_comp_realSlice {F : EuclideanSpace ℂ (Fin 3) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin 3))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin 3)} (hgx : realSlice x ∈ U) :
    iteratedFDeriv ℝ j (F ∘ realSlice) x =
      (iteratedFDeriv ℝ j F (realSlice x)).compContinuousLinearMap fun _ => realSlice := by
  have hFR : ContDiffOn ℝ ∞ F U := hF.restrict_scalars ℝ
  have hpre : IsOpen (realSlice ⁻¹' U) := hU.preimage realSlice.continuous
  have h := realSlice.iteratedFDerivWithin_comp_right hFR hU.uniqueDiffOn hpre.uniqueDiffOn
      hgx (i := j) (by exact_mod_cast le_top)
  rwa [iteratedFDerivWithin_of_isOpen j hpre hgx,
      iteratedFDerivWithin_of_isOpen j hU hgx] at h

lemma iteratedFDeriv_re_comp_realSlice {F : EuclideanSpace ℂ (Fin 3) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin 3))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin 3)} (hgx : realSlice x ∈ U) :
    iteratedFDeriv ℝ j (Complex.reCLM ∘ (F ∘ realSlice)) x =
      Complex.reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j (F ∘ realSlice) x) := by
  have hFR : ContDiffOn ℝ ∞ F U := hF.restrict_scalars ℝ
  have hpre : IsOpen (realSlice ⁻¹' U) := hU.preimage realSlice.continuous
  have hcompOn : ContDiffOn ℝ ∞ (F ∘ realSlice) (realSlice ⁻¹' U) :=
    hFR.comp_continuousLinearMap realSlice
  have hcompAt : ContDiffAt ℝ ∞ (F ∘ realSlice) x :=
    hcompOn.contDiffAt (hpre.mem_nhds hgx)
  exact Complex.reCLM.iteratedFDeriv_comp_left hcompAt (by exact_mod_cast le_top)

lemma norm_re_comp_le {j : ℕ}
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin j => EuclideanSpace ℂ (Fin 3)) ℂ) :
    ‖Complex.reCLM.compContinuousMultilinearMap
        ((T.restrictScalars ℝ).compContinuousLinearMap fun _ => realSlice)‖ ≤ ‖T‖ := by
  have h1 := Complex.reCLM.norm_compContinuousMultilinearMap_le
    ((T.restrictScalars ℝ).compContinuousLinearMap fun _ => realSlice)
  have h2 := (T.restrictScalars ℝ).norm_compContinuousLinearMap_le fun _ => realSlice
  have h3 : ∏ _i : Fin j, ‖realSlice‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_realSlice_le
  have h4 : ‖Complex.reCLM‖ ≤ 1 := Complex.reCLM_norm.le
  rw [ContinuousMultilinearMap.norm_restrictScalars] at h2
  have h5 : ‖T‖ * ∏ _i : Fin j, ‖realSlice‖ ≤ ‖T‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h3
  calc
    _ ≤ ‖Complex.reCLM‖ * ‖(T.restrictScalars ℝ).compContinuousLinearMap fun _ => realSlice‖ := h1
    _ ≤ 1 * ‖T‖ := by
      apply mul_le_mul h4 (h2.trans h5) (norm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

/-- Real iterated derivatives of the real slice are dominated by the complex
iterated derivatives of a complex-smooth extension. -/
theorem norm_iteratedFDeriv_real_le
    {F : EuclideanSpace ℂ (Fin 3) → ℂ} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℂ (Fin 3))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    (hVU : ∀ x ∈ V, realSlice x ∈ U)
    (hfF : ∀ x ∈ V, F (realSlice x) = (f x : ℂ)) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ V) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℂ j F (realSlice x)‖ := by
  have hev : f =ᶠ[𝓝 x] (Complex.reCLM ∘ (F ∘ realSlice)) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    simp [hfF y hy]
  have heq : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j (Complex.reCLM ∘ (F ∘ realSlice)) x :=
    (hev.iteratedFDeriv ℝ j).eq_of_nhds
  have hgx : realSlice x ∈ U := hVU x hx
  rw [heq, iteratedFDeriv_re_comp_realSlice hU hF j hgx, iteratedFDeriv_comp_realSlice hU hF j hgx,
    iteratedFDeriv_real_eq_restrictScalars hU hF j hgx]
  exact norm_re_comp_le _

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.DenseJet
