-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Restoration.Analytic.DenseJet.Line, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Restoration/Analytic/DenseJet/Line.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/DenseJet/Line.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/DenseJet/Line.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Line.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Mathlib
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Restoration.Analytic.DenseJet.GeneralDim
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.RealJets

/-!
# The one-variable algebraic norm bound

A one-variable algebraic function of degree at most `D`, complex-smooth on the disc of
radius four and real on the real axis, bounded by `v` on a measurable subset of `[-1, 1]`
of length at least `θ`, has all derivatives of order at most six bounded by `K θ^(-C) v`
on `[-2, 2]`. This is `Dim.core_jet_bound` for `n = 1`, read on `ℝ`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Line

open Set Metric MeasureTheory
open Submission.Obl.k4_algebraic_real_jet_comparison
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet (SheetRemezAssertion)
open scoped ContDiff ENNReal

lemma norm_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]

/-- The coordinate of the one-dimensional real Euclidean space. -/
noncomputable def coord : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv.trans
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
  norm_map' x := by
    rw [norm_eq_abs_coord x, Real.norm_eq_abs]
    rfl

lemma coord_apply (x : EuclideanSpace ℝ (Fin 1)) : coord x = x 0 := rfl

lemma norm_eq_abs_coord_complex (z : EuclideanSpace ℂ (Fin 1)) : ‖z‖ = ‖z 0‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]

lemma volume_coord_preimage (S : Set ℝ) :
    volume ((fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' S) = volume S := by
  have h1 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).measure_preimage_equiv
  have h2 := (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage_equiv
  calc
    volume ((fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' S) =
        volume ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm ⁻¹'
          ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' S)) := rfl
    _ = volume ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' S) := h1 _
    _ = volume S := h2 _

/-- The one-variable algebraic norm bound with jets. -/
theorem line_jet_bound (hR : SheetRemezAssertion) (D : ℕ) : ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (G : ℂ → ℂ) (g : ℝ → ℝ),
      HasSheetRelation 1 D (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) →
      ContDiffOn ℂ ∞ G (ball 0 4) →
      (∀ t : ℝ, |t| < 4 → G t = (g t : ℂ)) →
      ∀ (S : Set ℝ) (θ v : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ v → ENNReal.ofReal θ ≤ volume S → (∀ t ∈ S, |g t| ≤ v) →
        ∀ k : ℕ, k ≤ 6 → ∀ t ∈ Icc (-2 : ℝ) 2, |iteratedDeriv k g t| ≤ K * θ ^ (-C) * v := by
  obtain ⟨K, C, hK, hC, hcore⟩ := Dim.core_jet_bound (n := 1) hR D
  refine ⟨K, C, hK, hC, ?_⟩
  intro G g hrel hG hGg S θ v hS hSsub hθ hθ1 hv hvol hbound k hk t ht
  let p : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ := EuclideanSpace.proj 0
  have hmaps : MapsTo p (ball (0 : EuclideanSpace ℂ (Fin 1)) 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_eq_abs_coord_complex] at hz
    exact hz
  have hF : ContDiffOn ℂ ∞ (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) (ball 0 4) :=
    hG.comp p.contDiff.contDiffOn hmaps
  have hslice : ∀ x : EuclideanSpace ℝ (Fin 1), ‖x‖ < 4 →
      (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) (Dim.realSlice x) = ((g ∘ coord) x : ℂ) := by
    intro x hx
    rw [norm_eq_abs_coord] at hx
    simp only [Dim.realSlice_apply, Function.comp_apply, coord_apply]
    exact hGg (x 0) hx
  let E₁ : Set (EuclideanSpace ℝ (Fin 1)) := (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' S
  have hE₁ : MeasurableSet E₁ :=
    ((MeasurableEquiv.funUnique (Fin 1) ℝ).measurable.comp
      (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.measurable) hS
  have hE₁sub : E₁ ⊆ closedBall 0 1 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right, norm_eq_abs_coord]
    have := hSsub hx
    exact abs_le.mpr ⟨this.1, this.2⟩
  have hE₁vol : ENNReal.ofReal θ ≤ volume E₁ := by
    rw [volume_coord_preimage]
    exact hvol
  have hE₁bound : ∀ x ∈ E₁, |(g ∘ coord) x| ≤ v := fun x hx => hbound (x 0) hx
  let x : EuclideanSpace ℝ (Fin 1) := coord.symm t
  have hx : ‖x‖ ≤ 2 := by
    rw [coord.symm.norm_map, Real.norm_eq_abs]
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  have h := hcore _ (g ∘ coord) hrel hF hslice E₁ θ v hE₁ hE₁sub hθ hθ1 hv hE₁vol hE₁bound
    k hk x hx
  have hnorm : ‖iteratedFDeriv ℝ k (g ∘ coord) x‖ = |iteratedDeriv k g t| := by
    rw [coord.norm_iteratedFDeriv_comp_right g x k, LinearIsometryEquiv.apply_symm_apply,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  rw [← hnorm]
  exact h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Line

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Line

open Set Metric MeasureTheory
open Submission.Obl.k4_algebraic_real_jet_comparison
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet
  (SheetRemezAssertion realSlice realSlice_apply norm_realSlice_apply)
open scoped ContDiff ENNReal

/-- The directional algebraic norm bound along a line. If a branch is within `ε` of an
affine function of the line parameter on a set of parameters of length at least `θ`, then
its derivatives of order two to six along the line are at most `K θ^(-C) ε`. The
one-variable relation of the line restriction is a hypothesis. -/
theorem directional_jet_bound (hR : SheetRemezAssertion) (D : ℕ) : ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
      (a v : EuclideanSpace ℝ (Fin 3)) (α β : ℝ),
      ‖a‖ + 4 * ‖v‖ < 4 → ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ)) →
      HasSheetRelation 1 D (fun z : EuclideanSpace ℂ (Fin 1) =>
        F (realSlice a + z 0 • realSlice v) - α - β * z 0) →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (a + t • v) - α - β * t| ≤ ε) →
        ∀ k : ℕ, 2 ≤ k → k ≤ 6 → ∀ t ∈ Icc (-2 : ℝ) 2,
          |iteratedDeriv k (fun s : ℝ => f (a + s • v)) t| ≤ K * θ ^ (-C) * ε := by
  obtain ⟨K, C, hK, hC, hline⟩ := line_jet_bound hR D
  refine ⟨K, C, hK, hC, ?_⟩
  intro F f a v α β hav hF hfF hrel S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk2 hk6 t ht
  let G : ℂ → ℂ := fun ζ => F (realSlice a + ζ • realSlice v) - α - β * ζ
  let g : ℝ → ℝ := fun s => f (a + s • v) - α - β * s
  have hline_pt : ∀ ζ : ℂ, ‖ζ‖ < 4 → ‖realSlice a + ζ • realSlice v‖ < 4 := by
    intro ζ hζ
    calc
      ‖realSlice a + ζ • realSlice v‖ ≤ ‖realSlice a‖ + ‖ζ‖ * ‖realSlice v‖ := by
        simpa only [norm_smul] using norm_add_le (realSlice a) (ζ • realSlice v)
      _ ≤ ‖a‖ + 4 * ‖v‖ := by
        rw [norm_realSlice_apply, norm_realSlice_apply]
        gcongr
      _ < 4 := hav
  have hG : ContDiffOn ℂ ∞ G (ball 0 4) := by
    have hlin : ContDiff ℂ ∞ (fun ζ : ℂ => realSlice a + ζ • realSlice v) := by fun_prop
    have hmaps : MapsTo (fun ζ : ℂ => realSlice a + ζ • realSlice v) (ball 0 4) (ball 0 4) := by
      intro ζ hζ
      rw [mem_ball, dist_zero_right] at hζ ⊢
      exact hline_pt ζ hζ
    exact ((hF.comp hlin.contDiffOn hmaps).sub contDiffOn_const).sub
      (contDiffOn_const.mul contDiffOn_id)
  have hGg : ∀ s : ℝ, |s| < 4 → G s = (g s : ℂ) := by
    intro s hs
    have hpt : realSlice a + (s : ℂ) • realSlice v = realSlice (a + s • v) := by
      ext i
      simp [realSlice_apply]
    have hnorm : ‖a + s • v‖ < 4 := by
      rw [← norm_realSlice_apply, ← hpt]
      exact hline_pt s (by rwa [Complex.norm_real, Real.norm_eq_abs])
    simp only [G, g, hpt, hfF _ hnorm]
    push_cast
    ring
  have hrelG : HasSheetRelation 1 D (fun z : EuclideanSpace ℂ (Fin 1) => G (z 0)) := hrel
  have h := hline G g hrelG hG hGg S θ ε hS hSsub hθ hθ1 hε hvol hbound k hk6 t ht
  -- the affine part does not contribute from order two on
  have hsmooth : ContDiffAt ℝ k (fun s : ℝ => f (a + s • v)) t := by
    have h1 : ∀ s : ℝ, |s| < 4 → f (a + s • v) = (G s).re + α + β * s := by
      intro s hs
      rw [hGg s hs]
      simp only [g, Complex.ofReal_re]
      ring
    have hGR : ContDiffAt ℝ ∞ (fun s : ℝ => (G s).re + α + β * s) t := by
      have hball : (t : ℂ) ∈ ball (0 : ℂ) 4 := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans_lt (by norm_num)
      have hGat : ContDiffAt ℂ ∞ G t := hG.contDiffAt (isOpen_ball.mem_nhds hball)
      have hGatR : ContDiffAt ℝ ∞ G t := hGat.restrict_scalars ℝ
      have hre : ContDiffAt ℝ ∞ (fun s : ℝ => (G s).re) t :=
        Complex.reCLM.contDiff.contDiffAt.comp t
          (hGatR.comp t Complex.ofRealCLM.contDiff.contDiffAt)
      exact (hre.add contDiffAt_const).add (contDiffAt_const.mul contDiffAt_id)
    have hev : (fun s : ℝ => f (a + s • v)) =ᶠ[nhds t]
        (fun s : ℝ => (G s).re + α + β * s) := by
      have hopen : IsOpen {s : ℝ | |s| < 4} := isOpen_lt continuous_abs continuous_const
      have htin : t ∈ {s : ℝ | |s| < 4} :=
        (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans_lt (by norm_num)
      filter_upwards [hopen.mem_nhds htin] with s hs
      exact h1 s hs
    exact (hGR.congr_of_eventuallyEq hev).of_le (by exact_mod_cast le_top)
  have haff : ContDiffAt ℝ k (fun s : ℝ => α + β * s) t := by fun_prop
  have hgeq : g = (fun s : ℝ => f (a + s • v)) - (fun s : ℝ => α + β * s) := by
    funext s
    simp only [g, Pi.sub_apply]
    ring
  have hderiv : iteratedDeriv k g t = iteratedDeriv k (fun s : ℝ => f (a + s • v)) t := by
    rw [hgeq, iteratedDeriv_sub hsmooth haff]
    have hzero : iteratedDeriv k (fun s : ℝ => α + β * s) t = 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      have hd : deriv (fun s : ℝ => α + β * s) = fun _ => β := by
        funext s
        simp
      rw [hd]
      have hd2 : deriv (fun _ : ℝ => β) = fun _ => 0 := by
        funext s
        simp
      rw [hd2]
      simp
    rw [hzero, sub_zero]
  rw [← hderiv]
  exact h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Line
