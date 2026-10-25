-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/SevenTests.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/SevenTests.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.TrajectoryTests
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RobustTests
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineDistance
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Bridge

/-!
# Second-derivative tests at a point from a nearby long line witness

The sampled certificate asks for `|D²f u (p,p)| ≤ A (b + s h)` at every point `u` of a
common base set and for seven fixed directions `p`. A group line passing within `h₀` of
`u`, in a direction within `h₀` of `p`, whose hidden coordinate stays within `A b` of the
branch on a time set of measure `θ`, gives this test: `branch_jets_of_long_affine_tube`
bounds the jet at the line's anchor along its own direction, and the jet bound of the
algebraic branch pays the move of point and direction (`bounded_order_directional_sample_transfer`).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory
open scoped ContDiff

/-- A long affine line witness for the branch `f` near the point `u` and direction `p`. -/
def LineWitness (f : Base → ℝ) (A b θ h : ℝ) (u p : Base) : Prop :=
  ∃ (y v : Base) (w₀ w₁ : ℝ) (Et : Set ℝ),
    y ∈ closedBall (0 : Base) 1 ∧ ‖v‖ ≤ A ∧ ‖u - y‖ ≤ h ∧ ‖p - v‖ ≤ h ∧
    MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧ ENNReal.ofReal θ ≤ volume Et ∧
    ∀ t ∈ Et, |w₀ + w₁ * t - f (y + t • ((8 * A)⁻¹ • v))| ≤ A * b

/-- Higher jets of an algebraic branch are bounded on the doubled ball by its
affine-distance scale (the jet hypothesis of the frozen statement). -/
theorem jet_le_of_affine_scale {D J : ℕ} (hjet : DenseJetBound D J) {A s : ℝ} (hA : 2 ≤ A)
    {f : Base → ℝ} (hf : HasRealExtension D f) (hs : 0 ≤ s)
    (happrox : ∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε)
    {j : ℕ} (hj2 : 2 ≤ j) (hj6 : j ≤ 6) {x : Base} (hx : x ∈ closedBall (0 : Base) 2) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * s :=
  bound_by_affine_distance_scale f s (A ^ J) _ hs (pow_nonneg (by linarith) _) happrox
    (fun c L ε hε hc => (hjet A hA f hf).2 c L ε hε hc j hj2 hj6 x hx)

/-- The second directional test at `u` along `p`, from a line witness near `(u, p)`. -/
theorem second_test_of_line_witness (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ Dp → U.totalDegree ≤ Dp →
      V.totalDegree ≤ Dp → W.totalDegree ≤ Dp →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = MvPolynomial.eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        MvPolynomial.eval (fun i => z i) W * F z =
          MvPolynomial.eval (fun i => z i) U + MvPolynomial.eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1,
        MvPolynomial.eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr J : ℕ}, DenseJetBound Dr J → HasRealExtension Dr f →
      ∀ (A b θ h s : ℝ), 2 ≤ A → 0 ≤ b → 0 < θ → θ ≤ 1 → 0 ≤ h → 0 ≤ s →
      (∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ (u p : Base), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      LineWitness f A b θ h u p →
      |iteratedFDeriv ℝ 2 f u (fun _ => p)| ≤
        K * θ ^ (-C) * A ^ 25 * b + A ^ J * s * A ^ 9 * h := by
  obtain ⟨K, C, hK, hC, hjets⟩ := branch_jets_of_long_affine_tube hR Dp
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr J hjet hext A b θ h s hA hb
    hθ hθ1 hh hs happrox u p hu hp hwit
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, htube⟩ := hwit
  have hsmooth : ContDiffOn ℝ ∞ f (ball 0 4) := hext.contDiffOn
  -- the jet at the anchor along the line's own direction
  have hanchor := hjets Δ U V W hΔ hU hV hW sq F f hsq hpres hF hsmooth hmatch A b hA hb y v
    w₀ w₁ hy hv (hWne y hy) Et θ hEt hEtsub hθ hθ1 hEtvol htube 2 le_rfl (by norm_num)
  -- move point and direction inside the doubled open ball
  have hU2 : IsOpen (ball (0 : Base) 2) := isOpen_ball
  have hconv : Convex ℝ (ball (0 : Base) 2) := convex_ball _ _
  have hsmooth2 : ContDiffOn ℝ ∞ f (ball 0 2) :=
    hsmooth.mono (ball_subset_ball (by norm_num))
  have hin1 : ∀ {z : Base}, z ∈ closedBall (0 : Base) 1 → z ∈ ball (0 : Base) 2 :=
    fun hz => closedBall_subset_ball (by norm_num) hz
  have hclosed : ∀ {z : Base}, z ∈ ball (0 : Base) 2 → z ∈ closedBall (0 : Base) 2 :=
    fun hz => ball_subset_closedBall hz
  have hnext : ∀ z ∈ ball (0 : Base) 2, ‖iteratedFDeriv ℝ (2 + 1) f z‖ ≤ A ^ J * s :=
    fun z hz => jet_le_of_affine_scale hjet hA hext hs happrox (by norm_num) (by norm_num)
      (hclosed hz)
  have hcur : ‖iteratedFDeriv ℝ 2 f y‖ ≤ A ^ J * s :=
    jet_le_of_affine_scale hjet hA hext hs happrox le_rfl (by norm_num) (hclosed (hin1 hy))
  exact bounded_order_directional_sample_transfer hU2 hconv hsmooth2 2 (by norm_num) hA hh
    hnext (hin1 hu) (hin1 hy) hcur hp hv huy hpv hanchor

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open scoped ContDiff

/-- A long line witness that also carries the native bounds of the old quadratic `S`
along its tube, as needed for the residual jets. -/
def NativeLineWitness (f : Base → ℝ) (S : Poly) (A a b θ h : ℝ) (u p : Base) : Prop :=
  ∃ (y v : Base) (w₀ w₁ : ℝ) (Et : Set ℝ),
    y ∈ closedBall (0 : Base) 1 ∧ ‖v‖ ≤ A ∧ ‖u - y‖ ≤ h ∧ ‖p - v‖ ≤ h ∧
    MeasurableSet Et ∧ Et ⊆ Icc (-1) 1 ∧ ENNReal.ofReal θ ≤ volume Et ∧
    (∀ t ∈ Et, |w₀ + w₁ * t - f (y + t • ((8 * A)⁻¹ • v))| ≤ A * b) ∧
    (∀ t ∈ Et,
      |eval ![(y + t • ((8 * A)⁻¹ • v)) 0, (y + t • ((8 * A)⁻¹ • v)) 1,
        (y + t • ((8 * A)⁻¹ • v)) 2, w₀ + w₁ * t] (pderiv 3 S)| ≤ A) ∧
    (∀ t ∈ Et,
      |eval ![(y + t • ((8 * A)⁻¹ • v)) 0, (y + t • ((8 * A)⁻¹ • v)) 1,
        (y + t • ((8 * A)⁻¹ • v)) 2, w₀ + w₁ * t] (pderiv 3 (pderiv 3 S))| ≤ A / a)

theorem NativeLineWitness.toLineWitness {f : Base → ℝ} {S : Poly} {A a b θ h : ℝ} {u p : Base}
    (hw : NativeLineWitness f S A a b θ h u p) : LineWitness f A b θ h u p := by
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, htube, -, -⟩ := hw
  exact ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, htube⟩

/-- The third residual test at `u` along `p`, from a native line witness near `(u, p)`;
`V` bounds the residual on a dense set `E`, which controls its fourth jet. -/
theorem third_test_of_line_witness (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ)
    (hDp : 2 ≤ Dp) :
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
      ∀ (S : Poly), S.totalDegree ≤ 2 →
      ∀ {Dr J : ℕ}, DenseJetBound Dr J → HasRealExtension Dr f →
      ∀ (A AE a b θ h Vr : ℝ), 2 ≤ A → 2 ≤ AE → 0 < a → 0 ≤ b → b ≤ a → 0 < θ → θ ≤ 1 →
      0 ≤ h → 0 ≤ Vr →
      HasRealExtension Dr (fun x => eval ![x 0, x 1, x 2, f x] S / a) →
      ∀ (E : Set Base), MeasurableSet E → E ⊆ closedBall (0 : Base) 1 →
      ENNReal.ofReal AE⁻¹ ≤ volume E →
      (∀ x ∈ E, |eval ![x 0, x 1, x 2, f x] S / a| ≤ Vr) →
      ∀ (u p : Base), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      NativeLineWitness f S A a b θ h u p →
      |iteratedFDeriv ℝ 3 (fun x => eval ![x 0, x 1, x 2, f x] S / a) u (fun _ => p)| ≤
        K * θ ^ (-C) * A ^ 28 * b / a + AE ^ J * Vr * A ^ 9 * h := by
  obtain ⟨K, C, hK, hC, hjets⟩ := residual_jets_of_long_affine_tube hR Dp hDp
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW hW0 sq F f hsq hpres hF hmatch hWne S hS Dr J hjet hext A AE a b θ h
    Vr hA hAE ha hb hba hθ hθ1 hh hVr hRext E hEm hEsub hEvol hEval u p hu hp hwit
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, htube, hfirst, hsecond⟩ :=
    hwit
  have hsmooth : ContDiffOn ℝ ∞ f (ball 0 4) := hext.contDiffOn
  have hanchor := hjets Δ U V W hΔ hU hV hW hW0 sq F f hsq hpres hF hsmooth hmatch S hS A a b
    hA ha hb hba y v w₀ w₁ hy hv (hWne y hy) Et θ hEt hEtsub hθ hθ1 hEtvol htube hfirst hsecond
    3 le_rfl (by norm_num)
  set Rf : Base → ℝ := fun x => eval ![x 0, x 1, x 2, f x] S / a with hRf
  have hRsmooth : ContDiffOn ℝ ∞ Rf (ball 0 4) := hRext.contDiffOn
  have hRjet : ∀ {j : ℕ}, j ≤ 6 → ∀ {x : Base}, x ∈ closedBall (0 : Base) 2 →
      ‖iteratedFDeriv ℝ j Rf x‖ ≤ AE ^ J * Vr :=
    fun hj x hx => (hjet AE hAE Rf hRext).1 E Vr hEm hEsub hEvol hVr hEval _ hj x hx
  have hU2 : IsOpen (ball (0 : Base) 2) := isOpen_ball
  have hconv : Convex ℝ (ball (0 : Base) 2) := convex_ball _ _
  have hRsmooth2 : ContDiffOn ℝ ∞ Rf (ball 0 2) :=
    hRsmooth.mono (ball_subset_ball (by norm_num))
  have hin1 : ∀ {z : Base}, z ∈ closedBall (0 : Base) 1 → z ∈ ball (0 : Base) 2 :=
    fun hz => closedBall_subset_ball (by norm_num) hz
  have hnext : ∀ z ∈ ball (0 : Base) 2, ‖iteratedFDeriv ℝ (3 + 1) Rf z‖ ≤ AE ^ J * Vr :=
    fun z hz => hRjet (by norm_num) (ball_subset_closedBall hz)
  have hcur : ‖iteratedFDeriv ℝ 3 Rf y‖ ≤ AE ^ J * Vr :=
    hRjet (by norm_num) (ball_subset_closedBall (hin1 hy))
  have hfinal := bounded_order_directional_sample_transfer hU2 hconv hRsmooth2 3 (by norm_num) hA
    hh hnext (hin1 hu) (hin1 hy) hcur hp hv huy hpv hanchor
  simpa only [mul_div_assoc] using hfinal

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
