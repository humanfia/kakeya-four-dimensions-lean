-- Lane B: tubes of group points through single events, and the graph tests they give at nearby points.
-- `certifiedTube_of_event` is the tube built in the proof of `seven_directions_of_group`
-- (Broad/Restoration/SevenFromGroup.lean), for one event; the jet tests follow
-- `second_test_of_line_witness` (Broad/Restoration/SevenTests.lean) of the adapted back end
-- (this LOT tree, o265 x1031 2bb8b824, itself from o267 x0945 7135e2fb).
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenFromGroup
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SevenTests

/-!
# Tubes through single events, and the graph tests at nearby points (lane B)

* `certifiedTube_of_event`: an event whose line stays a physical group point for the time
  `(8 At D₀)⁻¹` about it (`D₀` the time component of its normalized direction) gives, in any
  normalization with explicit inverse, a certified tube witness of time measure `1` at every
  point within `h` of its normalized base point, in the direction of its lifted normalized
  velocity.
* `jet_test_of_line_witness`: a line witness near `(u, p)` bounds the directional jets of the
  branch of orders `2, …, 5` at `(u, p)`; `third_test_of_line_witness_graph` is order three
  (`second_test_of_line_witness` is order two).
* `lineWitness_of_certifiedTube`, `graph_tests_at_point`: a certified tube witness near `(u, p)`
  gives the second- and third-order tests of the branch at `(u, p)`, with common constants.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open scoped ContDiff

/-- **The certified tube of a single event.** The event's line, for the time `(8 At D₀)⁻¹`
about it, is a tube of certified group points: base point the event's normalized base point,
direction the lift of its normalized velocity, hidden coordinate affine in the tube time, time
set `[-1, 1]`. -/
theorem certifiedTube_of_event {c c' : Fin 3 → ℝ} {M M' : Matrix (Fin 3) (Fin 3) ℝ}
    {B B' : ℝ} (hM : M' * M = 1) (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j)
    (hB : B' * B = 1) {R0 Rc : Poly} {Pot : MvPolynomial (Fin 3) ℝ}
    {εfit A₁ σ Vc At τw h : ℝ} (p : Event)
    (hD0 : 0 < lineDir M p.1 0) (hτ : (8 * At * lineDir M p.1 0)⁻¹ ≤ τw)
    (hgp : ∀ s, |s - p.2| ≤ τw → PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc (graphPoint p.1 s))
    (hZ : normalizedBase c M B (graphPoint p.1 p.2) ∈ closedBall (0 : Base) 1)
    (hAt : 1 ≤ At) (hlift : ‖GeneralPositionSampling.lift (lineVelocity M p.1)‖ ≤ At)
    (u : Base) (hu : ‖u - normalizedBase c M B (graphPoint p.1 p.2)‖ ≤ h) (hh : 0 ≤ h) :
    CertifiedTubeWitness (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)
      (transportPolynomial c' M' B' Rc) εfit A₁ σ Vc At 1 h u
      (GeneralPositionSampling.lift (lineVelocity M p.1)) := by
  set D₀ := lineDir M p.1 0 with hD₀
  have hAtpos : 0 < At := by linarith
  refine ⟨normalizedBase c M B (graphPoint p.1 p.2),
    GeneralPositionSampling.lift (lineVelocity M p.1),
    (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 p.2))).2,
    (B * p.1.2 5) / (8 * At * D₀), Icc (-1) 1, hZ, hlift, hu, ?_, measurableSet_Icc, le_rfl,
    ?_, ?_⟩
  · rw [sub_self, norm_zero]
    exact hh
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  · intro t ht
    set s' := p.2 + t / (8 * At * D₀) with hs'
    have hdt : |s' - p.2| ≤ τw := by
      rw [hs', add_sub_cancel_left, abs_div, abs_of_pos (by positivity : 0 < 8 * At * D₀)]
      calc |t| / (8 * At * D₀) ≤ 1 / (8 * At * D₀) := by
            gcongr; exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        _ = (8 * At * D₀)⁻¹ := one_div _
        _ ≤ τw := hτ
    have hphys := hgp s' hdt
    have hbase : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).1 =
        normalizedBase c M B (graphPoint p.1 p.2) +
          t • ((8 * At)⁻¹ • GeneralPositionSampling.lift (lineVelocity M p.1)) := by
      have h1 := normalizedBase_graphPoint c M B p.1 s' p.2
      have h2 := lineDir_eq_smul_lift M p.1 hD0.ne'
      change normalizedBase c M B (graphPoint p.1 s') = _
      have hD0' : D₀ ≠ 0 := hD0.ne'
      have hAt' : At ≠ 0 := hAtpos.ne'
      have hcoef : t / (8 * At * D₀) * D₀ = t * (8 * At)⁻¹ := by
        field_simp
      rw [h1, h2, hs', add_sub_cancel_left, smul_smul, smul_smul, ← hD₀, hcoef]
    have hhid : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).2 =
        (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 p.2))).2 +
          (B * p.1.2 5) / (8 * At * D₀) * t := by
      rw [hidden_graphPoint c M B p.1 s' p.2, hs', add_sub_cancel_left]
      ring
    have hball : (pointOfCoordinates (coordinateMap c M B (graphPoint p.1 s'))).1 ∈
        ball (0 : Base) 4 := by
      rw [hbase, mem_ball, dist_zero_right]
      have hZ1 := hZ
      rw [mem_closedBall, dist_zero_right] at hZ1
      calc ‖normalizedBase c M B (graphPoint p.1 p.2) +
            t • ((8 * At)⁻¹ • GeneralPositionSampling.lift (lineVelocity M p.1))‖
          ≤ ‖normalizedBase c M B (graphPoint p.1 p.2)‖ +
              |t| * ((8 * At)⁻¹ * ‖GeneralPositionSampling.lift (lineVelocity M p.1)‖) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 8 * At))]
        _ ≤ 1 + 1 * ((8 * At)⁻¹ * At) := by
            gcongr
            · exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        _ < 4 := by
            have : (8 * At)⁻¹ * At = 1 / 8 := by field_simp
            rw [this]; norm_num
    have hcg := certifiedGroupPoint_of_physical hM hc hB hphys hball
    rw [hbase, hhid] at hcg
    exact hcg

/-- The directional jets of orders `2, …, 5` at `u` along `p`, from a line witness near
`(u, p)`: the jet at the anchor along the line's own direction
(`branch_jets_of_long_affine_tube`), moved to `(u, p)` by the jet bound of the algebraic branch
(`bounded_order_directional_sample_transfer`). -/
theorem jet_test_of_line_witness (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ Dp → U.totalDegree ≤ Dp →
      V.totalDegree ≤ Dp → W.totalDegree ≤ Dp →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr J : ℕ}, DenseJetBound Dr J → HasRealExtension Dr f →
      ∀ (A b θ h s : ℝ), 2 ≤ A → 0 ≤ b → 0 < θ → θ ≤ 1 → 0 ≤ h → 0 ≤ s →
      (∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ (u p : Base), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      LineWitness f A b θ h u p →
      ∀ k : ℕ, 2 ≤ k → k ≤ 5 →
      |iteratedFDeriv ℝ k f u (fun _ => p)| ≤
        K * θ ^ (-C) * A ^ 25 * b + A ^ J * s * A ^ 9 * h := by
  obtain ⟨K, C, hK, hC, hjets⟩ := branch_jets_of_long_affine_tube hR Dp
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr J hjet hext A b θ h s hA hb
    hθ hθ1 hh hs happrox u p hu hp hwit k hk2 hk5
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, htube⟩ := hwit
  have hsmooth : ContDiffOn ℝ ∞ f (ball 0 4) := hext.contDiffOn
  -- the jet at the anchor along the line's own direction
  have hanchor := hjets Δ U V W hΔ hU hV hW sq F f hsq hpres hF hsmooth hmatch A b hA hb y v
    w₀ w₁ hy hv (hWne y hy) Et θ hEt hEtsub hθ hθ1 hEtvol htube k hk2 (by omega)
  -- move point and direction inside the doubled open ball
  have hU2 : IsOpen (ball (0 : Base) 2) := isOpen_ball
  have hconv : Convex ℝ (ball (0 : Base) 2) := convex_ball _ _
  have hsmooth2 : ContDiffOn ℝ ∞ f (ball 0 2) :=
    hsmooth.mono (ball_subset_ball (by norm_num))
  have hin1 : ∀ {z : Base}, z ∈ closedBall (0 : Base) 1 → z ∈ ball (0 : Base) 2 :=
    fun hz => closedBall_subset_ball (by norm_num) hz
  have hnext : ∀ z ∈ ball (0 : Base) 2, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ A ^ J * s :=
    fun z hz => jet_le_of_affine_scale hjet hA hext hs happrox (by omega) (by omega)
      (ball_subset_closedBall hz)
  have hcur : ‖iteratedFDeriv ℝ k f y‖ ≤ A ^ J * s :=
    jet_le_of_affine_scale hjet hA hext hs happrox hk2 (by omega)
      (ball_subset_closedBall (hin1 hy))
  exact bounded_order_directional_sample_transfer hU2 hconv hsmooth2 k (by omega) hA hh
    hnext (hin1 hu) (hin1 hy) hcur hp hv huy hpv hanchor

/-- The third directional test of the branch at `u` along `p`, from a line witness near
`(u, p)` (the branch itself, not the residual of `third_test_of_line_witness`). -/
theorem third_test_of_line_witness_graph (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ Dp → U.totalDegree ≤ Dp →
      V.totalDegree ≤ Dp → W.totalDegree ≤ Dp →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr J : ℕ}, DenseJetBound Dr J → HasRealExtension Dr f →
      ∀ (A b θ h s : ℝ), 2 ≤ A → 0 ≤ b → 0 < θ → θ ≤ 1 → 0 ≤ h → 0 ≤ s →
      (∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ (u p : Base), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      LineWitness f A b θ h u p →
      |iteratedFDeriv ℝ 3 f u (fun _ => p)| ≤
        K * θ ^ (-C) * A ^ 25 * b + A ^ J * s * A ^ 9 * h := by
  obtain ⟨K, C, hK, hC, htest⟩ := jet_test_of_line_witness hR Dp
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr J hjet hext A b θ h s hA hb
    hθ hθ1 hh hs happrox u p hu hp hwit
  exact htest Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hext A b θ h s hA hb
    hθ hθ1 hh hs happrox u p hu hp hwit 3 (by norm_num) (by norm_num)

/-- A tube of certified group points is a line witness for the branch (the band part of
`nativeLineWitness_of_certifiedTube`, which alone needs no bound on the test `Sc`). -/
theorem lineWitness_of_certifiedTube {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly}
    {εfit A₁ σ Vc a At b θ h : ℝ} {Bδ Cδ : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA₁ : 2 ≤ A₁) (hε : 0 < εfit) (hsmall : 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹)
    (hband : εfit * A₁ ^ 19 ≤ At * b)
    (hroot : ∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
      eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ)
    (hSeq : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
      a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ)
    (hSd : ∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
      2 * a * w + eval (fun i => z i) Bδ)
    {u p : Base} (hw : CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc At θ h u p) :
    LineWitness f At b θ h u p := by
  obtain ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, hpts⟩ := hw
  refine ⟨y, v, w₀, w₁, Et, hy, hv, huy, hpv, hEt, hEtsub, hEtvol, fun t ht => ?_⟩
  exact (band_of_normalizedGroupPoint hA₁ hε hsmall hroot hSeq hSd (hpts t ht).1).trans hband

/-- **The graph tests at a point.** A tube of certified group points near `(u, p)` gives the
second- and the third-order directional tests of the branch at `(u, p)`, with the same
constants. -/
theorem graph_tests_at_point (hR : DenseJet.SheetRemezAssertion) (Dp : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ Dp → U.totalDegree ≤ Dp →
      V.totalDegree ≤ Dp → W.totalDegree ≤ Dp →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr J : ℕ}, DenseJetBound Dr J → HasRealExtension Dr f →
      ∀ (A b θ h s : ℝ), 2 ≤ A → 0 ≤ b → 0 < θ → θ ≤ 1 → 0 ≤ h → 0 ≤ s →
      (∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ Vc a : ℝ}
        {Bδ Cδ : MvPolynomial (Fin 3) ℝ},
      2 ≤ A₁ → 0 < εfit → 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹ → εfit * A₁ ^ 19 ≤ A * b →
      (∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
        eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
        a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
        2 * a * w + eval (fun i => z i) Bδ) →
      ∀ (u p : Base), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc A θ h u p →
      |iteratedFDeriv ℝ 2 f u (fun _ => p)| ≤
          K * θ ^ (-C) * A ^ 25 * b + A ^ J * s * A ^ 9 * h ∧
        |iteratedFDeriv ℝ 3 f u (fun _ => p)| ≤
          K * θ ^ (-C) * A ^ 25 * b + A ^ J * s * A ^ 9 * h := by
  obtain ⟨K, C, hK, hC, htest⟩ := jet_test_of_line_witness hR Dp
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr J hjet hext A b θ h s hA hb
    hθ hθ1 hh hs happrox S0 P0 Sc εfit A₁ σ Vc a Bδ Cδ hA₁ hε hsmall hband hroot hSeq hSd
    u p hu hp hw
  have hwit : LineWitness f A b θ h u p :=
    lineWitness_of_certifiedTube hA₁ hε hsmall hband hroot hSeq hSd hw
  exact ⟨htest Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hext A b θ h s hA hb
      hθ hθ1 hh hs happrox u p hu hp hwit 2 le_rfl (by norm_num),
    htest Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hext A b θ h s hA hb
      hθ hθ1 hh hs happrox u p hu hp hwit 3 (by norm_num) (by norm_num)⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
