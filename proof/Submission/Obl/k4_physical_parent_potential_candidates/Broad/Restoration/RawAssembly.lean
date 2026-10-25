-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/RawAssembly.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/RawAssembly.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenTests
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.Expanded

/-!
# The analytic part of the sampled certificate

`rawBranchData_of_witnesses` assembles the thirty analytic fields of the frozen sampled
alternative (`RawBranchData`) from: an algebraic branch with its rational presentation and
extensions, the old native quadratic `S`, seven directions in general position, a common
base set `E` of controlled volume on which the residual is bounded, and, at every point of
`E` and for every direction, a long native line witness nearby (`NativeLineWitness`).
The time scale is `h₀ = b / (a (A^(J+1))^Cloc)`, the largest one allowed, and the affine
distance scale of the branch is the exact one of `exists_affine_distance_scale`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open scoped ContDiff

theorem rawBranchData_of_witnesses (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ) (hDp : 2 ≤ Dp) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ Dp → U.totalDegree ≤ Dp →
      V.totalDegree ≤ Dp → W.totalDegree ≤ Dp → W ≠ 0 →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ContDiffOn ℝ 6 f (ball 0 3) →
      ∀ (Cloc J Dr : ℕ), DenseJetBound Dr J →
      ∀ (S : Poly) (p : Fin 7 → Base) (E : Set Base) (A At Z a b θ h Vr : ℝ),
      HasRealExtension Dr f →
      (∀ i, HasRealExtension Dr (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i))) →
      HasRealExtension Dr (fun v => eval ![v 0, v 1, v 2, f v] S / a) →
      (∀ i, HasRealExtension Dr (fun v => iteratedFDeriv ℝ 3
        (fun z => eval ![z 0, z 1, z 2, f z] S / a) v (fun _ => p i))) →
      S.totalDegree ≤ 2 → (∀ e, |S.coeff e| ≤ Z) →
      (∀ (u : Base) (w : ℝ), |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 S))| ≤ A / a) →
      2 ≤ At → At ≤ A → 0 < b → b ≤ a → a ≤ 1 → 0 < θ → θ ≤ 1 → 0 ≤ h → 0 ≤ Vr → Vr ≤ A →
      A ^ (J + 1) ≤ Z → b⁻¹ ≤ Z → |f 0| ≤ Z → ‖fderiv ℝ f 0‖ ≤ Z →
      ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z →
      K * θ ^ (-C) * At ^ 28 ≤ A / 2 →
      At ^ (J + 9) * h * ((A ^ (J + 1)) ^ Cloc * a) ≤ A * b →
      A ^ J * Vr * At ^ 9 * h ≤ A / 2 * (b / a) →
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ At) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      MeasurableSet E → E ⊆ closedBall (0 : Base) 1 → ENNReal.ofReal A⁻¹ ≤ volume E →
      (∀ u ∈ E, |eval ![u 0, u 1, u 2, f u] S / a| ≤ Vr) →
      (∀ u ∈ E, ∀ i, NativeLineWitness f S At a b θ h u (p i)) →
      ∃ h₀ s₀ : ℝ, RawBranchData Cloc J Dr A Z a b h₀ s₀ S f p E := by
  obtain ⟨K₂, C₂, hK₂, hC₂, hsecond⟩ := second_test_of_line_witness hR Dp
  obtain ⟨K₃, C₃, hK₃, hC₃, hthird⟩ := third_test_of_line_witness hR Dp hDp
  refine ⟨max K₂ K₃, max C₂ C₃, lt_max_of_lt_left hK₂, le_max_of_le_left hC₂, ?_⟩
  intro Δ U V W hΔ hU hV hW hW0 sq F f hsq hpres hF hmatch hWne hf6 Cloc J Dr hjet S p E A At Z
    a b θ h Vr hfext hf2ext hRext hR3ext hS hSZ hScurv hAt hAtA hb hba ha1 hθ hθ1 hh hVr hVrA
    hAZ hbZ hf0 hDf0 hD2f0 hconst hsmall2 hsmall3 hp hdet hEm hEsub hEvol hEval hwit
  have hA : 2 ≤ A := hAt.trans hAtA
  have hA0 : 0 < A := by linarith
  have hAt0 : 0 < At := by linarith
  have ha : 0 < a := hb.trans_le hba
  -- the affine-distance scale of the branch
  have hfcont : ContinuousOn f (closedBall (0 : Base) 1) :=
    (hf6.continuousOn).mono (closedBall_subset_ball (by norm_num))
  obtain ⟨s₀, hs₀, hdist, happrox⟩ := exists_affine_distance_scale f hfcont
  -- the largest permitted time scale
  set L := (A ^ (J + 1)) ^ Cloc with hL
  have hL0 : 0 < L := pow_pos (pow_pos hA0 _) _
  set h₀ := b / (a * L) with hh₀
  have hh₀pos : 0 < h₀ := div_pos hb (mul_pos ha hL0)
  have hh₀scale : h₀ * L ≤ b / a := by
    rw [hh₀, div_mul_eq_mul_div, mul_comm a L, ← div_div, mul_div_assoc, div_self hL0.ne',
      mul_one]
  -- constants of the two test lemmas
  have hθC₂ : θ ^ (-C₂) ≤ θ ^ (-max C₂ C₃) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (neg_le_neg (le_max_left _ _))
  have hθC₃ : θ ^ (-C₃) ≤ θ ^ (-max C₂ C₃) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (neg_le_neg (le_max_right _ _))
  have hθpos : ∀ c : ℝ, 0 ≤ θ ^ c := fun c => (Real.rpow_pos_of_pos hθ c).le
  have hAt25 : At ^ 25 ≤ At ^ 28 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hK2 : K₂ * θ ^ (-C₂) * At ^ 25 ≤ A / 2 := by
    refine le_trans ?_ hconst
    gcongr
    · exact le_max_left _ _
  have hK3 : K₃ * θ ^ (-C₃) * At ^ 28 ≤ A / 2 := by
    refine le_trans ?_ hconst
    gcongr
    · exact le_max_right _ _
  -- the transfer cost of the second test fits in `A s₀ h₀`
  have htransfer2 : At ^ J * s₀ * At ^ 9 * h ≤ A * (s₀ * h₀) := by
    have hkey : At ^ (J + 9) * h ≤ A * h₀ := by
      rw [hh₀, mul_div_assoc']
      rw [le_div_iff₀ (mul_pos ha hL0)]
      calc At ^ (J + 9) * h * (a * L) = At ^ (J + 9) * h * (L * a) := by ring
        _ ≤ A * b := hsmall2
    calc At ^ J * s₀ * At ^ 9 * h = s₀ * (At ^ (J + 9) * h) := by rw [pow_add]; ring
      _ ≤ s₀ * (A * h₀) := mul_le_mul_of_nonneg_left hkey hs₀
      _ = A * (s₀ * h₀) := by ring
  refine ⟨h₀, s₀, hA, hAZ, hb, hba, ha1, hh₀pos, hh₀scale, hs₀, hbZ, hS, hSZ, hScurv, hf6,
    hf0, hDf0, hD2f0, hdist, happrox, fun i => ⟨(hp i).1, (hp i).2.trans hAtA⟩, hdet, hEm,
    hEsub, hEvol, hfext, hf2ext, hRext, hR3ext, ?_, fun u hu => (hEval u hu).trans hVrA, ?_⟩
  · -- second tests
    intro i u hu
    have hb2 := hsecond Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hfext At b θ h
      s₀ hAt hb.le hθ hθ1 hh hs₀ happrox u (p i) (hEsub hu) (hp i).2
      ((hwit u hu i).toLineWitness)
    calc |iteratedFDeriv ℝ 2 f u (fun _ => p i)|
        ≤ K₂ * θ ^ (-C₂) * At ^ 25 * b + At ^ J * s₀ * At ^ 9 * h := hb2
      _ ≤ A / 2 * b + A * (s₀ * h₀) := by
          gcongr
      _ ≤ A * (b + s₀ * h₀) := by nlinarith [hb.le]
  · -- third tests
    intro i u hu
    have hb3 := hthird Δ U V W hΔ hU hV hW hW0 sq F f hsq hpres hF hmatch hWne S hS hjet hfext
      At A a b θ h Vr hAt hA ha hb.le hba hθ hθ1 hh hVr hRext E hEm hEsub hEvol hEval u (p i)
      (hEsub hu) (hp i).2 (hwit u hu i)
    calc |iteratedFDeriv ℝ 3 (fun z => eval ![z 0, z 1, z 2, f z] S / a) u (fun _ => p i)|
        ≤ K₃ * θ ^ (-C₃) * At ^ 28 * b / a + A ^ J * Vr * At ^ 9 * h := hb3
      _ ≤ A / 2 * (b / a) + A / 2 * (b / a) := by
          gcongr
          · rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right hK3 (div_nonneg hb.le ha.le)
      _ = A * b / a := by ring

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
