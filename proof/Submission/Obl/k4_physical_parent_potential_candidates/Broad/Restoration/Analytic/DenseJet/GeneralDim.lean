-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/DenseJet/GeneralDim.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/DenseJet/GeneralDim.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/GeneralDim.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds
import Submission.Obl.k4_algebraic_real_jet_comparison.RealGeometry
import Submission.Obl.k4_quadratic_sheet_continuation.CauchyEstimates
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.EighthBall

/-!
# Jets of real algebraic sheets in any dimension

The dimension-free form of `DenseJet.core_jet_bound`: from the sheet Remez assertion (o172),
a degree-`D` sheet on `EuclideanSpace ℂ (Fin n)` with a complex-smooth extension, bounded by
`v` on a measurable subset of the closed real unit ball of volume at least `θ`, has all real
jets of order at most six bounded by `K θ^(-C) v` on the closed real ball of radius two.
The case `n = 1` is the one-variable algebraic norm bound used along trajectories.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Dim

open Set Metric Filter MeasureTheory
open Submission.Obl.k4_algebraic_real_jet_comparison
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet (SheetRemezAssertion)
open scoped Topology ContDiff ENNReal

variable {n : ℕ}

/-- The real slice of complex Euclidean space, as a continuous real-linear map. -/
noncomputable def realSlice {n : ℕ} : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding n).toContinuousLinearMap

lemma realSlice_apply (x : EuclideanSpace ℝ (Fin n)) :
    realSlice x = WithLp.toLp 2 (fun i => (x i : ℂ)) := rfl

lemma norm_realSlice_apply (x : EuclideanSpace ℝ (Fin n)) : ‖realSlice x‖ = ‖x‖ :=
  (Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding n).norm_map x

lemma norm_realSlice_le : ‖(realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

lemma iteratedFDeriv_real_eq_restrictScalars {F : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) :
    iteratedFDeriv ℝ j F z = (iteratedFDeriv ℂ j F z).restrictScalars ℝ := by
  have hFat : ContDiffAt ℂ j F z :=
    (hF.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast le_top)
  exact (hFat.restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm

lemma iteratedFDeriv_comp_realSlice {F : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hgx : realSlice x ∈ U) :
    iteratedFDeriv ℝ j (F ∘ realSlice) x =
      (iteratedFDeriv ℝ j F (realSlice x)).compContinuousLinearMap fun _ => realSlice := by
  have hFR : ContDiffOn ℝ ∞ F U := hF.restrict_scalars ℝ
  have hpre : IsOpen (realSlice ⁻¹' U) := hU.preimage realSlice.continuous
  have h := realSlice.iteratedFDerivWithin_comp_right hFR hU.uniqueDiffOn hpre.uniqueDiffOn
      hgx (i := j) (by exact_mod_cast le_top)
  rwa [iteratedFDerivWithin_of_isOpen j hpre hgx,
      iteratedFDerivWithin_of_isOpen j hU hgx] at h

lemma iteratedFDeriv_re_comp_realSlice {F : EuclideanSpace ℂ (Fin n) → ℂ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hgx : realSlice x ∈ U) :
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
    (T : ContinuousMultilinearMap ℂ (fun _ : Fin j => EuclideanSpace ℂ (Fin n)) ℂ) :
    ‖Complex.reCLM.compContinuousMultilinearMap
        ((T.restrictScalars ℝ).compContinuousLinearMap fun _ =>
          (realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)))‖ ≤ ‖T‖ := by
  have h1 := Complex.reCLM.norm_compContinuousMultilinearMap_le
    ((T.restrictScalars ℝ).compContinuousLinearMap fun _ =>
      (realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)))
  have h2 := (T.restrictScalars ℝ).norm_compContinuousLinearMap_le fun _ =>
    (realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
  have h3 : ∏ _i : Fin j,
      ‖(realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_realSlice_le
  have h4 : ‖Complex.reCLM‖ ≤ 1 := Complex.reCLM_norm.le
  rw [ContinuousMultilinearMap.norm_restrictScalars] at h2
  have h5 : ‖T‖ * ∏ _i : Fin j,
      ‖(realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))‖ ≤ ‖T‖ :=
    mul_le_of_le_one_right (norm_nonneg _) h3
  calc
    _ ≤ ‖Complex.reCLM‖ * ‖(T.restrictScalars ℝ).compContinuousLinearMap fun _ =>
          (realSlice : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))‖ := h1
    _ ≤ 1 * ‖T‖ := by
      apply mul_le_mul h4 (h2.trans h5) (norm_nonneg _) zero_le_one
    _ = ‖T‖ := one_mul _

/-- Real iterated derivatives of the real slice are dominated by the complex
iterated derivatives of a complex-smooth extension. -/
theorem norm_iteratedFDeriv_real_le
    {F : EuclideanSpace ℂ (Fin n) → ℂ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    (hVU : ∀ x ∈ V, realSlice x ∈ U)
    (hfF : ∀ x ∈ V, F (realSlice x) = (f x : ℂ)) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ V) :
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

/-- One step: a bound on the real ball of radius `1/8` around a real center of norm
less than `3` gives a bound on the complex ball of radius `1/2` around it. -/
theorem sheet_step (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (F : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D F →
      DifferentiableOn ℂ F (ball 0 4) →
      ∀ (c : EuclideanSpace ℝ (Fin n)), ‖c‖ < 3 → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x - c‖ ≤ 1 / 8 → ‖F (realSlice x)‖ ≤ B) →
      ∀ w : EuclideanSpace ℂ (Fin n), ‖w - realSlice c‖ ≤ 1 / 2 → ‖F w‖ ≤ C * B := by
  obtain ⟨C, hC, hnorm⟩ := exists_sheet_norm_constant_two n D
  refine ⟨C, hC, ?_⟩
  intro F hrel hF c hc B hB hbase w hw
  let a : EuclideanSpace ℂ (Fin n) := realSlice c
  have ha : ‖a‖ = ‖c‖ := norm_realSlice_apply c
  have hr : ((1 / 4 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hmap : MapsTo (fun z => a + ((1 / 4 : ℝ) : ℂ) • z) (ball 0 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    have hsm : ‖((1 / 4 : ℝ) : ℂ) • z‖ = ‖z‖ / 4 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      ring
    calc
      ‖a + ((1 / 4 : ℝ) : ℂ) • z‖ ≤ ‖a‖ + ‖((1 / 4 : ℝ) : ℂ) • z‖ := norm_add_le _ _
      _ < 4 := by rw [hsm, ha]; linarith
  have hrelG := hrel.comp_affine a hr hmap
  have hdG : DifferentiableOn ℂ (fun z => F (a + ((1 / 4 : ℝ) : ℂ) • z)) (ball 0 4) := by
    have hlin : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => a + ((1 / 4 : ℝ) : ℂ) • z) := by
      fun_prop
    exact hF.comp hlin.differentiableOn hmap
  have hbaseG : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖(fun z => F (a + ((1 / 4 : ℝ) : ℂ) • z)) (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B := by
    intro x hx
    have heq : a + ((1 / 4 : ℝ) : ℂ) • (WithLp.toLp 2 (fun i => (x i : ℂ)) :
        EuclideanSpace ℂ (Fin n)) = realSlice (c + (1 / 4 : ℝ) • x) := by
      ext i
      simp [a, realSlice_apply]
    simp only [heq]
    apply hbase
    have : c + (1 / 4 : ℝ) • x - c = (1 / 4 : ℝ) • x := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have hbound := hnorm _ hrelG hdG B hB hbaseG
  have hz : ‖(4 : ℂ) • (w - a)‖ ≤ 2 := by
    rw [norm_smul]
    have : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [this]
    linarith
  have h := hbound _ hz
  have heq : a + ((1 / 4 : ℝ) : ℂ) • ((4 : ℂ) • (w - a)) = w := by
    rw [smul_smul]
    norm_num
  simpa only [heq] using h

/-- The chain: a bound on the real ball of radius `1/8` around a point of the closed
unit ball propagates to the complex balls of radius `1/2` around every real point of
norm at most `2`. -/
theorem sheet_chain (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (F : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D F →
      DifferentiableOn ℂ F (ball 0 4) →
      ∀ (y : EuclideanSpace ℝ (Fin n)), ‖y‖ ≤ 1 → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x - y‖ ≤ 1 / 8 → ‖F (realSlice x)‖ ≤ B) →
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 2 →
      ∀ w : EuclideanSpace ℂ (Fin n), ‖w - realSlice x‖ ≤ 1 / 2 → ‖F w‖ ≤ C * B := by
  obtain ⟨C, hC, hstep⟩ := sheet_step (n := n) D
  refine ⟨C ^ 9, by positivity, ?_⟩
  intro F hrel hF y hy B hB hbase x hx
  let c : ℕ → EuclideanSpace ℝ (Fin n) := fun k => y + ((k : ℝ) / 8) • (x - y)
  have hc_norm : ∀ k : ℕ, k ≤ 8 → ‖c k‖ ≤ 2 := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / 8 := by positivity
    have hk1 : (k : ℝ) / 8 ≤ 1 := by
      rw [div_le_one (by norm_num)]
      exact_mod_cast hk
    have heq : c k = (1 - (k : ℝ) / 8) • y + ((k : ℝ) / 8) • x := by
      simp only [c, smul_sub, sub_smul, one_smul]
      abel
    rw [heq]
    calc
      _ ≤ ‖(1 - (k : ℝ) / 8) • y‖ + ‖((k : ℝ) / 8) • x‖ := norm_add_le _ _
      _ = (1 - (k : ℝ) / 8) * ‖y‖ + ((k : ℝ) / 8) * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hk0]
      _ ≤ (1 - (k : ℝ) / 8) * 2 + ((k : ℝ) / 8) * 2 := by
        gcongr
        linarith
      _ = 2 := by ring
  have hc_step : ∀ k : ℕ, ‖c (k + 1) - c k‖ ≤ 3 / 8 := by
    intro k
    have heq : c (k + 1) - c k = (1 / 8 : ℝ) • (x - y) := by
      simp only [c]
      push_cast
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have : ‖x - y‖ ≤ 3 := (norm_sub_le x y).trans (by linarith)
    linarith
  have hc8 : c 8 = x := by
    simp only [c]
    norm_num
  have hcomplex : ∀ k : ℕ, k ≤ 8 → ∀ w : EuclideanSpace ℂ (Fin n),
      ‖w - realSlice (c k)‖ ≤ 1 / 2 → ‖F w‖ ≤ C ^ (k + 1) * B := by
    intro k
    induction k with
    | zero =>
      intro _ w hw
      have h := hstep F hrel hF (c 0) (by linarith [hc_norm 0 (by norm_num)]) B hB
        (by
          intro z hz
          apply hbase z
          simpa [c] using hz) w hw
      simpa using h
    | succ k ih =>
      intro hk w hw
      have hprev := ih (by omega)
      have hreal : ∀ z : EuclideanSpace ℝ (Fin n), ‖z - c (k + 1)‖ ≤ 1 / 8 →
          ‖F (realSlice z)‖ ≤ C ^ (k + 1) * B := by
        intro z hz
        apply hprev
        rw [← map_sub, norm_realSlice_apply]
        calc
          ‖z - c k‖ = ‖(z - c (k + 1)) + (c (k + 1) - c k)‖ := by abel_nf
          _ ≤ ‖z - c (k + 1)‖ + ‖c (k + 1) - c k‖ := norm_add_le _ _
          _ ≤ 1 / 8 + 3 / 8 := add_le_add hz (hc_step k)
          _ = 1 / 2 := by norm_num
      have h := hstep F hrel hF (c (k + 1)) (by linarith [hc_norm (k + 1) hk])
        (C ^ (k + 1) * B) (by positivity) hreal w hw
      calc
        ‖F w‖ ≤ C * (C ^ (k + 1) * B) := h
        _ = C ^ (k + 1 + 1) * B := by ring
  intro w hw
  have h := hcomplex 8 le_rfl w (by rwa [hc8])
  simpa using h

lemma realSlice_affine (y x : EuclideanSpace ℝ (Fin n)) :
    realSlice y + ((1 / 4 : ℝ) : ℂ) • (WithLp.toLp 2 (fun i => (x i : ℂ)) :
      EuclideanSpace ℂ (Fin n)) = realSlice (y + (1 / 4 : ℝ) • x) := by
  ext i
  simp [realSlice_apply]

lemma mapsTo_quarter {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ < 3) :
    MapsTo (fun z => realSlice y + ((1 / 4 : ℝ) : ℂ) • z) (ball 0 4) (ball 0 4) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz ⊢
  have hsm : ‖((1 / 4 : ℝ) : ℂ) • z‖ = ‖z‖ / 4 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    ring
  calc
    ‖realSlice y + ((1 / 4 : ℝ) : ℂ) • z‖ ≤ ‖realSlice y‖ + ‖((1 / 4 : ℝ) : ℂ) • z‖ :=
      norm_add_le _ _
    _ < 4 := by rw [hsm, norm_realSlice_apply]; linarith

/-- Rescaled preimage of a set near `y`: its volume is multiplied by `64`. -/
lemma volume_quarter_preimage (y : EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((fun x : EuclideanSpace ℝ (Fin n) => y + (1 / 4 : ℝ) • x) ⁻¹' S) = (4 : ℝ≥0∞) ^ n * volume S := by
  have hcomp : ((fun x : EuclideanSpace ℝ (Fin n) => y + (1 / 4 : ℝ) • x) ⁻¹' S) =
      (fun x : EuclideanSpace ℝ (Fin n) => (1 / 4 : ℝ) • x) ⁻¹'
        ((fun z : EuclideanSpace ℝ (Fin n) => y + z) ⁻¹' S) := rfl
  rw [hcomp, Measure.addHaar_preimage_smul volume (by norm_num : (1 / 4 : ℝ) ≠ 0),
    measure_preimage_add, finrank_euclideanSpace_fin]
  congr 1
  have h : |(((1 : ℝ) / 4) ^ n)⁻¹| = (4 : ℝ) ^ n := by
    rw [abs_of_pos (by positivity), one_div, inv_pow, inv_inv]
  rw [h, ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- o172 on the real ball of radius `1/8` around a point of the closed unit ball. -/
theorem eighth_ball_remez (hR : SheetRemezAssertion) (D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D F →
      DifferentiableOn ℂ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ < 4 → (F (realSlice x)).im = 0) →
      ∀ (y : EuclideanSpace ℝ (Fin n)), ‖y‖ ≤ 1 →
      ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ), MeasurableSet S →
        S ⊆ closedBall y (1 / 8) → 0 < θ → θ ≤ 1 → 0 ≤ V →
        ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤
          (4 : ℝ≥0∞) ^ n * volume S →
        (∀ x ∈ S, ‖F (realSlice x)‖ ≤ V) →
        ∀ x : EuclideanSpace ℝ (Fin n), ‖x - y‖ ≤ 1 / 8 →
          ‖F (realSlice x)‖ ≤ C * θ ^ (-C) * V := by
  obtain ⟨C, hC, hrem⟩ := hR n D
  refine ⟨C, hC, ?_⟩
  intro F hrel hF hreal y hy S θ V hS hSsub hθ hθ1 hV hmass hbound x hx
  have hy3 : ‖y‖ < 3 := by linarith
  have hmap := mapsTo_quarter hy3
  obtain ⟨P, hP, hdeg, hroot⟩ :=
    hrel.comp_affine (realSlice y) (by norm_num : ((1 / 4 : ℝ) : ℂ) ≠ 0) hmap
  have hdG : DifferentiableOn ℂ (fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z)) (ball 0 4) := by
    have hlin : Differentiable ℂ
        (fun z : EuclideanSpace ℂ (Fin n) => realSlice y + ((1 / 4 : ℝ) : ℂ) • z) := by
      fun_prop
    exact hF.comp hlin.differentiableOn hmap
  let E' : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x' : EuclideanSpace ℝ (Fin n) => y + (1 / 4 : ℝ) • x') ⁻¹' S
  have hE' : MeasurableSet E' := by
    have hc : Continuous (fun x' : EuclideanSpace ℝ (Fin n) => y + (1 / 4 : ℝ) • x') := by
      fun_prop
    exact hc.measurable hS
  have hE'sub : E' ⊆ closedBall 0 (1 / 2) := by
    intro x' hx'
    have h := hSsub hx'
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num)] at h
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hE'mass : ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤
      volume E' := by
    rw [volume_quarter_preimage y S]
    exact hmass
  have hrealG : ∀ x' : EuclideanSpace ℝ (Fin n), ‖x'‖ ≤ 1 →
      ((fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z))
        (WithLp.toLp 2 (fun j => (x' j : ℂ)))).im = 0 := by
    intro x' hx'
    simp only [realSlice_affine]
    apply hreal
    calc
      ‖y + (1 / 4 : ℝ) • x'‖ ≤ ‖y‖ + ‖(1 / 4 : ℝ) • x'‖ := norm_add_le _ _
      _ = ‖y‖ + ‖x'‖ / 4 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        ring
      _ < 4 := by linarith
  have hboundG : ∀ x' ∈ E', ‖(fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z))
      (WithLp.toLp 2 (fun j => (x' j : ℂ)))‖ ≤ V := by
    intro x' hx'
    simp only [realSlice_affine]
    exact hbound _ hx'
  have hmain := hrem P _ hP hdeg hdG hroot hrealG E' θ V hE' hE'sub hθ hθ1 hV hE'mass hboundG
  have hx' : ‖(4 : ℝ) • (x - y)‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have h := hmain _ hx'
  simp only [realSlice_affine] at h
  have heq : y + (1 / 4 : ℝ) • ((4 : ℝ) • (x - y)) = x := by
    rw [smul_smul]
    norm_num
  rwa [heq] at h

/-- A fixed finite cover of the closed unit ball by closed balls of radius `1/8`
centered in the closed unit ball. -/
theorem exists_eighth_cover : ∃ s : Finset (EuclideanSpace ℝ (Fin n)),
    (∀ y ∈ s, ‖y‖ ≤ 1) ∧
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ y ∈ s, closedBall y (1 / 8) := by
  obtain ⟨t, hts, htfin, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨htfin.toFinset, ?_, ?_⟩
  · intro y hy
    have h := hts (htfin.mem_toFinset.mp hy)
    simpa only [mem_closedBall, dist_zero_right] using h
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨y, htfin.mem_toFinset.mpr hy, ball_subset_closedBall hxy⟩

/-- Some ball of the cover carries a proportional share of a subset of the unit ball. -/
theorem exists_heavy_eighth_ball {s : Finset (EuclideanSpace ℝ (Fin n))}
    (hcover : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ ⋃ y ∈ s, closedBall y (1 / 8))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : E ⊆ closedBall 0 1) (hEne : E.Nonempty) :
    ∃ y ∈ s, volume E ≤ (s.card : ℝ≥0∞) * volume (E ∩ closedBall y (1 / 8)) := by
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    obtain ⟨y, hy, _⟩ := mem_iUnion₂.mp (hcover (hE hx))
    exact ⟨y, hy⟩
  obtain ⟨y, hy, hmax⟩ := s.exists_max_image (fun y => volume (E ∩ closedBall y (1 / 8))) hsne
  refine ⟨y, hy, ?_⟩
  have hsub : E ⊆ ⋃ z ∈ s, E ∩ closedBall z (1 / 8) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (hE hx))
    exact mem_iUnion₂.mpr ⟨z, hz, hx, hxz⟩
  calc
    volume E ≤ volume (⋃ z ∈ s, E ∩ closedBall z (1 / 8)) := measure_mono hsub
    _ ≤ ∑ z ∈ s, volume (E ∩ closedBall z (1 / 8)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ s, volume (E ∩ closedBall y (1 / 8)) := Finset.sum_le_sum fun z hz => hmax z hz
    _ = (s.card : ℝ≥0∞) * volume (E ∩ closedBall y (1 / 8)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Jets of a real algebraic sheet from its values on a set of positive measure. -/
theorem core_jet_bound (hR : SheetRemezAssertion) (D : ℕ) : ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (F : EuclideanSpace ℂ (Fin n) → ℂ) (f : EuclideanSpace ℝ (Fin n) → ℝ),
      HasSheetRelation n D F → ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ)) →
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ v : ℝ), MeasurableSet E →
        E ⊆ closedBall 0 1 → 0 < θ → θ ≤ 1 → 0 ≤ v → ENNReal.ofReal θ ≤ volume E →
        (∀ x ∈ E, |f x| ≤ v) →
        ∀ j : ℕ, j ≤ 6 → ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 2 →
          ‖iteratedFDeriv ℝ j f x‖ ≤ K * θ ^ (-C) * v := by
  obtain ⟨CR, hCR, hremez⟩ := eighth_ball_remez (n := n) hR D
  obtain ⟨Cch, hCch, hchain⟩ := sheet_chain (n := n) D
  obtain ⟨s, hs, hcover⟩ := exists_eighth_cover (n := n)
  choose Cc hCc_pos hCc using
    Submission.Obl.k4_quadratic_sheet_continuation.exists_iteratedFDeriv_ball_bound
  let Kc : ℝ := ∑ j ∈ Finset.range 7, Cc j * 4 ^ j
  have hKc : ∀ j : ℕ, j ≤ 6 → Cc j * 4 ^ j ≤ Kc := by
    intro j hj
    apply Finset.single_le_sum (f := fun j => Cc j * 4 ^ j)
      (fun i _ => mul_nonneg (hCc_pos i).le (by positivity))
    simp only [Finset.mem_range]
    omega
  have hKc_pos : 0 < Kc := lt_of_lt_of_le (mul_pos (hCc_pos 0) (by norm_num)) (hKc 0 (by norm_num))
  let N₀ : ℝ := s.card
  obtain ⟨V₁, hV₁, hvolhalf⟩ : ∃ V₁ : ℝ, 1 ≤ V₁ ∧
      volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ ENNReal.ofReal V₁ := by
    refine ⟨(volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal + 1, ?_, ?_⟩
    · linarith [ENNReal.toReal_nonneg (a := volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)))]
    · have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≠ ⊤ :=
        measure_closedBall_lt_top.ne
      calc
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) =
            ENNReal.ofReal (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal
            ((volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))).toReal + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  have hV₁pos : 0 < V₁ := by linarith
  have hN₀0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  have hKpos : 0 < Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR :=
    mul_pos (mul_pos (mul_pos hKc_pos hCch) (by linarith))
      (Real.rpow_pos_of_pos (mul_pos (mul_pos two_pos (by linarith)) hV₁pos) _)
  refine ⟨Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR, CR, hKpos, hCR, ?_⟩
  intro F f hrel hF hfF E θ v hE hEsub hθ hθ1 hv hvol hbound j hj x hx
  have hF' : DifferentiableOn ℂ F (ball 0 4) := hF.differentiableOn (by simp)
  have hreal : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ < 4 → (F (realSlice z)).im = 0 := by
    intro z hz
    rw [hfF z hz, Complex.ofReal_im]
  -- the positive case
  have hpos : ∀ v' : ℝ, 0 < v' → (∀ x ∈ E, |f x| ≤ v') →
      ‖iteratedFDeriv ℝ j f x‖ ≤ Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) * v' := by
    intro v' hv' hbound'
    have hEne : E.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hvol
      linarith
    obtain ⟨y, hy, hpig⟩ := exists_heavy_eighth_ball hcover hEsub hEne
    let S := E ∩ closedBall y (1 / 8)
    have hSmeas : MeasurableSet S := hE.inter measurableSet_closedBall
    have hSfin : volume S ≠ ⊤ :=
      (measure_mono (Set.inter_subset_right) |>.trans_lt measure_closedBall_lt_top).ne
    let sR : ℝ := (volume S).toReal
    have hsR : volume S = ENNReal.ofReal sR := (ENNReal.ofReal_toReal hSfin).symm
    have hN₀ : 0 ≤ N₀ := Nat.cast_nonneg _
    have hθsR : θ ≤ N₀ * sR := by
      have h := hvol.trans hpig
      rw [hsR, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hN₀ ENNReal.toReal_nonneg)).mp h
    let θ' : ℝ := θ / (2 * (N₀ + 1) * V₁)
    have hden : 0 < 2 * (N₀ + 1) * V₁ := mul_pos (mul_pos two_pos (by linarith)) hV₁pos
    have hθ' : 0 < θ' := div_pos hθ hden
    have hθ'1 : θ' ≤ 1 := by
      rw [div_le_one hden]
      nlinarith
    have hmass : ENNReal.ofReal θ' * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤
        (4 : ℝ≥0∞) ^ n * volume S := by
      calc
        ENNReal.ofReal θ' * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤
            ENNReal.ofReal θ' * ENNReal.ofReal V₁ := by gcongr
        _ = ENNReal.ofReal (θ' * V₁) := (ENNReal.ofReal_mul hθ'.le).symm
        _ ≤ ENNReal.ofReal sR := by
          apply ENNReal.ofReal_le_ofReal
          have hsR0 : 0 ≤ sR := ENNReal.toReal_nonneg
          have h1 : θ' * V₁ = θ / (2 * (N₀ + 1)) := by
            simp only [θ']
            field_simp
          rw [h1, div_le_iff₀ (by linarith)]
          nlinarith
        _ = volume S := hsR.symm
        _ ≤ (4 : ℝ≥0∞) ^ n * volume S :=
          le_mul_of_one_le_left (by simp) (one_le_pow₀ (by norm_num))
    have hSbound : ∀ z ∈ S, ‖F (realSlice z)‖ ≤ v' := by
      intro z hz
      have hz1 : ‖z‖ < 4 := by
        have := hEsub hz.1
        rw [mem_closedBall, dist_zero_right] at this
        linarith
      rw [hfF z hz1, Complex.norm_real, Real.norm_eq_abs]
      exact hbound' z hz.1
    have hsmall := hremez F hrel hF' hreal y (hs y hy) S θ' v' hSmeas Set.inter_subset_right
      hθ' hθ'1 hv'.le hmass hSbound
    let B : ℝ := CR * θ' ^ (-CR) * v'
    have hB : 0 < B := mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hθ' _)) hv'
    have hcomplex := hchain F hrel hF' y (hs y hy) B hB hsmall x hx
    -- Cauchy estimate at the real point
    have hballsub : ball (realSlice x) (2 * (1 / 4)) ⊆ ball 0 4 := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      have h1 : ‖w‖ ≤ ‖w - realSlice x‖ + ‖realSlice x‖ := by
        simpa using norm_add_le (w - realSlice x) (realSlice x)
      rw [norm_realSlice_apply] at h1
      linarith
    have hcauchy := hCc j F (realSlice x) (1 / 4) (Cch * B) (by norm_num) (mul_pos hCch hB).le
      (hF.mono hballsub) (by
        intro w hw
        apply hcomplex
        rw [mem_ball, dist_eq_norm] at hw
        linarith)
    have hrealjet := norm_iteratedFDeriv_real_le (V := ball (0 : EuclideanSpace ℝ (Fin n)) 4)
      isOpen_ball hF isOpen_ball
      (fun z hz => by
        rw [mem_ball, dist_zero_right] at hz ⊢
        rwa [norm_realSlice_apply])
      (fun z hz => hfF z (by rwa [mem_ball, dist_zero_right] at hz)) j
      (show x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 4 by
        rw [mem_ball, dist_zero_right]; linarith)
    have hθ'pow : θ' ^ (-CR) = (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) := by
      simp only [θ']
      rw [Real.div_rpow hθ.le hden.le, Real.rpow_neg hden.le, div_eq_mul_inv, inv_inv]
      ring
    calc
      ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℂ j F (realSlice x)‖ := hrealjet
      _ ≤ Cc j * (Cch * B) / (1 / 4) ^ j := hcauchy
      _ = (Cc j * 4 ^ j) * Cch * CR * θ' ^ (-CR) * v' := by
        simp only [B]
        rw [one_div, inv_pow, div_inv_eq_mul]
        ring
      _ ≤ Kc * Cch * CR * θ' ^ (-CR) * v' := by
        have h0 : 0 ≤ Cch * CR * θ' ^ (-CR) * v' :=
          (mul_pos (mul_pos (mul_pos hCch (by linarith)) (Real.rpow_pos_of_pos hθ' _)) hv').le
        have := mul_le_mul_of_nonneg_right (hKc j hj) h0
        linarith [this]
      _ = Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR) * v' := by
        rw [hθ'pow]
        ring
  -- conclude, also when `v = 0`
  rcases hv.lt_or_eq with hv0 | hv0
  · exact hpos v hv0 hbound
  · subst hv0
    rw [mul_zero]
    by_contra hcon
    push Not at hcon
    set a := ‖iteratedFDeriv ℝ j f x‖
    set K' := Kc * Cch * CR * (2 * (N₀ + 1) * V₁) ^ CR * θ ^ (-CR)
    have hK'pos : 0 < K' := mul_pos hKpos (Real.rpow_pos_of_pos hθ _)
    have hpa : 0 < a / (2 * K') := div_pos hcon (mul_pos two_pos hK'pos)
    have h := hpos (a / (2 * K')) hpa (fun z hz => (hbound z hz).trans hpa.le)
    have : K' * (a / (2 * K')) = a / 2 := by field_simp
    linarith

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Dim
