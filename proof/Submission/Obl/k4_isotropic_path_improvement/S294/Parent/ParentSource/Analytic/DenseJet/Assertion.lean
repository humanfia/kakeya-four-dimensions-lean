-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.DenseJet.Assertion, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/DenseJet/Assertion.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DenseJet/Assertion.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DenseJet/Assertion.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Assertion.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.Core

/-!
# Dense jet bounds for real algebraic sheets with smooth extensions

From the sheet Remez assertion (o172) we obtain, for every relation degree `D`, one
exponent `J` controlling all real jets of order at most six on the closed ball of
radius two:

* by `A ^ J * v`, when the function is bounded by `v` on a measurable subset of the
  closed unit ball of volume at least `A⁻¹`;
* by `A ^ J * ε` for the jets of order two to six, when the function is within `ε` of an
  affine function on the closed unit ball.

The extension is required to be complex-smooth on the radius-four ball.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet

open Set Metric MeasureTheory MvPolynomial
open Submission.Obl.k4_algebraic_real_jet_comparison
open scoped ContDiff ENNReal

/-- A real function with a complex-smooth algebraic extension on the radius-four ball. -/
def HasSmoothRealExtension (D : ℕ) (f : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (P : MvPolynomial (Fin 4) ℂ),
    P ≠ 0 ∧ P.totalDegree ≤ D ∧
    ContDiffOn ℂ ∞ F (Metric.ball 0 4) ∧
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z)) P = 0) ∧
    ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 4,
      F (WithLp.toLp 2 (fun i : Fin 3 => (x i : ℂ))) = (f x : ℂ)

/-- The dense jet bound, for smooth extensions. -/
def DenseJetBoundSmooth (D J : ℕ) : Prop :=
  ∀ (A : ℝ), 2 ≤ A → ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ), HasSmoothRealExtension D f →
    (∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (v : ℝ), MeasurableSet E →
      E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 →
      ENNReal.ofReal A⁻¹ ≤ volume E → 0 ≤ v →
      (∀ x ∈ E, |f x| ≤ v) →
      ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * v) ∧
    (∀ (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, |f x - c - L x| ≤ ε) →
      ∀ j : ℕ, 2 ≤ j → j ≤ 6 →
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * ε)

/-- Affine functions have vanishing iterated derivatives from order two on. -/
lemma iteratedFDeriv_affine_eq_zero {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (c : F) (L : E →L[𝕜] F) {j : ℕ} (hj : 2 ≤ j) (x : E) :
    iteratedFDeriv 𝕜 j (fun y => c + L y) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 + 1 := ⟨j - 2, by omega⟩
  have hfd : fderiv 𝕜 (fun y => c + L y) = fun _ => L := by
    funext y
    rw [fderiv_const_add, L.fderiv]
  have h := norm_iteratedFDeriv_fderiv (𝕜 := 𝕜) (f := fun y => c + L y) (x := x) (n := n + 1)
  rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n), Pi.zero_apply, norm_zero] at h
  exact norm_eq_zero.mp h.symm

/-- The complexified affine function, as a sheet of degree one. -/
noncomputable def complexAffine (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin 3) → ℂ :=
  fun z => (c : ℂ) + ∑ i : Fin 3, (L (EuclideanSpace.single i 1) : ℂ) * z i

lemma complexAffine_real (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    complexAffine c L (WithLp.toLp 2 (fun i => (x i : ℂ))) = ((c + L x : ℝ) : ℂ) := by
  have hL : L x = ∑ i : Fin 3, L (EuclideanSpace.single i 1) * x i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp [map_sum, mul_comm]
  simp only [complexAffine, hL]
  push_cast
  rfl

lemma contDiff_complexAffine (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ContDiff ℂ ∞ (complexAffine c L) := by
  unfold complexAffine
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  apply contDiff_const.mul
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).contDiff

lemma hasSheetRelation_complexAffine (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) {D : ℕ}
    (hD : 1 ≤ D) : HasSheetRelation 3 D (complexAffine c L) := by
  let P : MvPolynomial (Fin 4) ℂ := X (Fin.last 3) - C (c : ℂ) -
    ∑ i : Fin 3, C (L (EuclideanSpace.single i 1) : ℂ) * X i.castSucc
  have heval : ∀ (z : EuclideanSpace ℂ (Fin 3)) (w : ℂ),
      eval (Fin.snoc (fun i : Fin 3 => z i) w) P =
        w - (c : ℂ) - ∑ i : Fin 3, (L (EuclideanSpace.single i 1) : ℂ) * z i := by
    intro z w
    have hlast : (Fin.snoc (fun i : Fin 3 => z i) w : Fin 4 → ℂ) (Fin.last 3) = w :=
      Fin.snoc_last _ _
    simp only [P, map_sub, map_sum, map_mul, eval_X, eval_C, Fin.snoc_castSucc, hlast]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro hP
    have h := heval 0 ((c : ℂ) + 1)
    rw [hP, map_zero] at h
    simp at h
  · have h1 : P.totalDegree ≤ 1 := by
      apply (totalDegree_sub _ _).trans
      apply max_le
      · apply (totalDegree_sub _ _).trans
        apply max_le
        · rw [totalDegree_X]
        · rw [totalDegree_C]
          norm_num
      · apply (totalDegree_finsetSum _ _).trans
        apply Finset.sup_le
        intro i _
        apply (totalDegree_mul _ _).trans
        rw [totalDegree_C, totalDegree_X]
    exact h1.trans hD
  · intro z _
    rw [heval]
    simp [complexAffine]

lemma HasSheetRelation.mono_degree {n D D' : ℕ} {F : EuclideanSpace ℂ (Fin n) → ℂ}
    (h : HasSheetRelation n D F) (hD : D ≤ D') : HasSheetRelation n D' F := by
  obtain ⟨P, hP, hdeg, hroot⟩ := h
  exact ⟨P, hP, hdeg.trans hD, hroot⟩

/-- The real slice of a complex-smooth function is real-smooth inside the ball. -/
lemma contDiffAt_real_slice {F : EuclideanSpace ℂ (Fin 3) → ℂ} {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : ContDiffOn ℂ ∞ F (ball 0 4))
    (hfF : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 4) : ContDiffAt ℝ ∞ f x := by
  have hFR : ContDiffOn ℝ ∞ F (ball 0 4) := hF.restrict_scalars ℝ
  have hpre : IsOpen (realSlice ⁻¹' ball (0 : EuclideanSpace ℂ (Fin 3)) 4) :=
    isOpen_ball.preimage realSlice.continuous
  have hgx : realSlice x ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4 := by
    rw [mem_ball, dist_zero_right, norm_realSlice_apply]
    exact hx
  have hcompAt : ContDiffAt ℝ ∞ (F ∘ realSlice) x :=
    (hFR.comp_continuousLinearMap realSlice).contDiffAt (hpre.mem_nhds hgx)
  have hre : ContDiffAt ℝ ∞ (Complex.reCLM ∘ (F ∘ realSlice)) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hcompAt
  apply hre.congr_of_eventuallyEq
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < 4} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  simp [hfF y hy]

/-- From the sheet Remez assertion: dense jet bounds for every relation degree. -/
theorem denseJetBoundSmooth_of_sheetRemez (hR : SheetRemezAssertion) (D : ℕ) :
    ∃ J : ℕ, 1 ≤ J ∧ DenseJetBoundSmooth D J := by
  obtain ⟨K₁, C₁, hK₁, hC₁, hcore₁⟩ := core_jet_bound hR D
  obtain ⟨E₂, hE₂⟩ := exists_sheet_difference_degree 3 (max D 1)
  obtain ⟨K₂, C₂, hK₂, hC₂, hcore₂⟩ := core_jet_bound hR E₂
  obtain ⟨θ₁, hθ₁, hθ₁1, hθ₁vol⟩ : ∃ θ₁ : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 ∧
      ENNReal.ofReal θ₁ ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    have hpos : 0 < volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      measure_closedBall_pos volume 0 (by norm_num)
    have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ≠ ⊤ :=
      measure_closedBall_lt_top.ne
    refine ⟨min 1 (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal,
      lt_min one_pos (ENNReal.toReal_pos hpos.ne' hfin), min_le_left _ _, ?_⟩
    calc
      ENNReal.ofReal (min 1 (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal) ≤
          ENNReal.ofReal (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal :=
        ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := ENNReal.ofReal_toReal hfin
  let M₁ : ℕ := ⌈C₁⌉₊
  obtain ⟨P, hP⟩ : ∃ P : ℕ, max K₁ (K₂ * θ₁ ^ (-C₂)) ≤ 2 ^ P := by
    obtain ⟨P, hP⟩ := pow_unbounded_of_one_lt (max K₁ (K₂ * θ₁ ^ (-C₂))) (by norm_num : (1 : ℝ) < 2)
    exact ⟨P, hP.le⟩
  have hM₁ : 1 ≤ M₁ := by
    have : (1 : ℝ) ≤ ⌈C₁⌉₊ := hC₁.trans (Nat.le_ceil C₁)
    exact_mod_cast this
  refine ⟨M₁ + P, by omega, ?_⟩
  intro A hA f hf
  obtain ⟨F, Pr, hPr, hdeg, hF, hroot, hfF⟩ := hf
  have hrel : HasSheetRelation 3 D F := ⟨Pr, hPr, hdeg, hroot⟩
  have hfF' : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ) := by
    intro x hx
    exact hfF x (by rwa [mem_ball, dist_zero_right])
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have h2P : (2 : ℝ) ^ P ≤ A ^ P := pow_le_pow_left₀ (by norm_num) hA (P)
  have hAP : A ^ P ≤ A ^ (M₁ + P) := pow_le_pow_right₀ hA1 (by omega)
  have hkey₁ : K₁ * (A⁻¹) ^ (-C₁) ≤ A ^ (M₁ + P) := by
    have hinv : (A⁻¹) ^ (-C₁) = A ^ C₁ := by
      rw [Real.inv_rpow hA0, Real.rpow_neg hA0, inv_inv]
    have hpow : A ^ C₁ ≤ A ^ M₁ := by
      calc
        A ^ C₁ ≤ A ^ (M₁ : ℝ) := Real.rpow_le_rpow_of_exponent_le hA1 (Nat.le_ceil C₁)
        _ = A ^ M₁ := Real.rpow_natCast A M₁
    rw [hinv, pow_add]
    have hK : K₁ ≤ A ^ P := ((le_max_left _ _).trans hP).trans h2P
    calc
      K₁ * A ^ C₁ ≤ A ^ P * A ^ M₁ :=
        mul_le_mul hK hpow (Real.rpow_nonneg hA0 _) (pow_nonneg hA0 _)
      _ = A ^ M₁ * A ^ P := mul_comm _ _
  have hkey₂ : K₂ * θ₁ ^ (-C₂) ≤ A ^ (M₁ + P) :=
    (((le_max_right _ _).trans hP).trans h2P).trans hAP
  constructor
  · intro E v hE hEsub hvol hv hbound j hj x hx
    have hx' : ‖x‖ ≤ 2 := by rwa [mem_closedBall, dist_zero_right] at hx
    have h := hcore₁ F f hrel hF hfF' E A⁻¹ v hE hEsub (inv_pos.mpr (by linarith))
      (inv_le_one_of_one_le₀ hA1) hv hvol hbound j hj x hx'
    exact h.trans (mul_le_mul_of_nonneg_right hkey₁ hv)
  · intro c L ε hε happrox j hj2 hj6 x hx
    have hx' : ‖x‖ ≤ 2 := by rwa [mem_closedBall, dist_zero_right] at hx
    let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => f y - c - L y
    let G : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => F z - complexAffine c L z
    have hrelG : HasSheetRelation 3 E₂ G :=
      hE₂ F (complexAffine c L) (HasSheetRelation.mono_degree hrel (le_max_left _ _))
        (hasSheetRelation_complexAffine c L (le_max_right _ _))
    have hG : ContDiffOn ℂ ∞ G (ball 0 4) := hF.sub (contDiff_complexAffine c L).contDiffOn
    have hgG : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ < 4 → G (realSlice y) = (g y : ℂ) := by
      intro y hy
      have h1 : F (realSlice y) = (f y : ℂ) := hfF' y hy
      have h2 : complexAffine c L (realSlice y) = ((c + L y : ℝ) : ℂ) := complexAffine_real c L y
      simp only [G, g, h1, h2]
      push_cast
      ring
    have h := hcore₂ G g hrelG hG hgG (closedBall 0 1) θ₁ ε measurableSet_closedBall subset_rfl
      hθ₁ hθ₁1 hε.le hθ₁vol (fun y hy => by simpa only [g] using happrox y hy) j hj6 x hx'
    have hx4 : ‖x‖ < 4 := by linarith
    have hfsmooth : ContDiffAt ℝ j f x :=
      (contDiffAt_real_slice hF hfF' hx4).of_le (by exact_mod_cast le_top)
    have haff : ContDiffAt ℝ j (fun y : EuclideanSpace ℝ (Fin 3) => c + L y) x :=
      (contDiff_const.add L.contDiff).contDiffAt
    have hgeq : g = f - (fun y : EuclideanSpace ℝ (Fin 3) => c + L y) := by
      funext y
      simp only [g, Pi.sub_apply]
      ring
    have heq : iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
      rw [hgeq, iteratedFDeriv_sub_apply hfsmooth haff, iteratedFDeriv_affine_eq_zero c L hj2 x,
        sub_zero]
    rw [heq]
    exact h.trans (mul_le_mul_of_nonneg_right hkey₂ hε.le)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet
