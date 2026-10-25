-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/StableRootCover.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit 4f6b438039a1d3c89379a078b58a83c2c1314a02,
   Submission/Obl/k4_finite_projected_horizontal_candidates/StableRootCover.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_stable_quadratic_hidden_sheets
import Submission.Obl.k4_quadratic_mesh_coefficient_calibration
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials
import Submission.Obl.k4_algebraic_real_jet_comparison.AffineRelations
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetJets

/-!
# Stable hidden sheets on balls of controlled radius

A law of points `(u, w)`, base `u ∈ ℝ³` with base density at most `H`, on which a quadratic test
`F(u, w)` satisfies the chart bounds `|F| ≤ K a`, `K⁻¹ ≤ |∂_w F| ≤ K`, `|∂_w² F| ≤ K / a`
(the true-label fit of the prepared model, or `P - G` for a projected label's graph `G` and the
native polynomial `P`).

`stable_root_cover`: the points are covered by at most `(K H) ^ C` balls of radius
`r ≥ (K H) ^ (-C)`, each carrying a sheet in the sense of `IsSheet` (after normalizing the ball
to the unit ball), such that every point lies in a quarter ball with hidden coordinate within
`(K H) ^ C * a` of the sheet.

Proof. The discriminant `b² - 4 c a` of `F = a w² + b(u) w + c(u)` is at most `3 K²` at the
points, so the accepted mesh coefficient calibration (o242) bounds its coefficients by a power
of `K H`. At low curvature the accepted stable hidden sheets (o171) give a holomorphic root on a
ball around each point, chosen once per grid cell and branch; at high curvature the points lie
near the affine critical center (accepted o176), a global polynomial sheet.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set Filter MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The Euclidean point of a coordinate vector. -/
abbrev toEuc (v : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v

/-! ### The hidden-variable coefficients of a quadratic test -/

/-- The coefficient of `w²`. -/
def qa (F : MvPolynomial (Fin 4) ℝ) : ℝ := curvature F 3 / 2

/-- The coefficient of `w`, a base polynomial. -/
def qb (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ := restrictBase (pderiv 3 F)

/-- The constant coefficient, a base polynomial. -/
def qc (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ := restrictBase F

/-- The discriminant `b² - 4 a c` in the form of the accepted o171. -/
def qdisc (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  qb F * qb F - MvPolynomial.C (4 * qa F) * qc F

theorem last_three : (3 : Fin 4) = Fin.last 3 := rfl

theorem eval_snoc_qF {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (x : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc x w) F = qa F * w ^ 2 + eval x (qb F) * w + eval x (qc F) := by
  have h := eval_snoc_quadratic F hF x w
  rw [← last_three] at h
  rw [h, qa, qb, qc]
  ring

theorem eval_snoc_qFw {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (x : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc x w) (pderiv 3 F) = 2 * qa F * w + eval x (qb F) := by
  have h := quadratic_coordinate_derivative F hF (Fin.snoc x 0) (Fin.last 3) w
  rw [Fin.snoc_last, zero_add, update_snoc_hidden] at h
  rw [last_three, h, qa, qb, eval_restrictBase, ← last_three]
  ring

theorem eval_qdisc {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (x : Fin 3 → ℝ) (w : ℝ) :
    eval x (qdisc F) =
      (eval (Fin.snoc x w) (pderiv 3 F)) ^ 2 - 4 * qa F * eval (Fin.snoc x w) F := by
  rw [eval_snoc_qFw hF, eval_snoc_qF hF, qdisc]
  simp only [eval_sub, eval_mul, eval_C]
  ring

theorem qb_degree {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) :
    (qb F).totalDegree ≤ 1 :=
  (totalDegree_restrictBase _).trans
    ((Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le F _).trans (by omega))

theorem qc_degree {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) :
    (qc F).totalDegree ≤ 2 :=
  (totalDegree_restrictBase _).trans hF

theorem qdisc_degree {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) :
    (qdisc F).totalDegree ≤ 2 := by
  unfold qdisc
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by have := qb_degree hF; omega)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; simpa using qc_degree hF)

/-- At a point with the chart bounds the discriminant is at most `3 K²`. -/
theorem abs_eval_qdisc_le {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    {K a : ℝ} (ha : 0 < a) (x : Fin 3 → ℝ) (w : ℝ)
    (h1 : |eval (Fin.snoc x w) F| ≤ K * a) (h2 : |eval (Fin.snoc x w) (pderiv 3 F)| ≤ K)
    (h3 : |curvature F 3| ≤ K / a) :
    |eval x (qdisc F)| ≤ 3 * K ^ 2 := by
  rw [eval_qdisc hF x w]
  have hK : 0 ≤ K := le_trans (abs_nonneg _) h2
  have hsq : (eval (Fin.snoc x w) (pderiv 3 F)) ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hprod : |4 * qa F * eval (Fin.snoc x w) F| ≤ 2 * K ^ 2 := by
    rw [qa, abs_mul, abs_mul]
    have : |curvature F 3 / 2| = |curvature F 3| / 2 := by rw [abs_div]; norm_num
    rw [this]
    calc |4| * (|curvature F 3| / 2) * |eval (Fin.snoc x w) F|
        ≤ 4 * ((K / a) / 2) * (K * a) := by
          rw [show |(4 : ℝ)| = 4 by norm_num]
          gcongr
      _ = 2 * K ^ 2 := by field_simp; ring
  calc |(eval (Fin.snoc x w) (pderiv 3 F)) ^ 2 - 4 * qa F * eval (Fin.snoc x w) F|
      ≤ |(eval (Fin.snoc x w) (pderiv 3 F)) ^ 2| + |4 * qa F * eval (Fin.snoc x w) F| :=
        abs_sub _ _
    _ ≤ K ^ 2 + 2 * K ^ 2 := by
        gcongr
        rw [abs_of_nonneg (sq_nonneg _)]; exact hsq
    _ = 3 * K ^ 2 := by ring

/-! ### Coefficient bound from base density (accepted o242) -/

theorem volume_floor_cell (δ : ℝ) (hδ : 0 < δ) (q : Fin 3 → ℤ) :
    volume {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} = ENNReal.ofReal (δ ^ 3) := by
  have hset : {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} =
      Set.pi univ (fun i => Ico ((q i : ℝ) * δ) (((q i : ℝ) + 1) * δ)) := by
    ext z
    simp only [mem_setOf_eq, Set.mem_pi, mem_univ, true_implies, mem_Ico, funext_iff,
      Int.floor_eq_iff]
    refine forall_congr' fun i => ?_
    rw [le_div_iff₀ hδ, div_lt_iff₀ hδ]
  rw [hset, Real.volume_pi_Ico]
  simp only [Fin.prod_univ_three]
  have : ∀ i : Fin 3, ((q i : ℝ) + 1) * δ - (q i : ℝ) * δ = δ := fun i => by ring
  simp only [this]
  rw [← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

theorem coeff_bound_of_density :
    ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ K H E : ℝ, 1 ≤ K → 1 ≤ H → 0 ≤ E →
    ∀ (D : MvPolynomial (Fin 3) ℝ), D.totalDegree ≤ 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
    ∀ (u : Ω → Fin 3 → ℝ), Measurable u →
    (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
      lam (u ⁻¹' U) ≤ ENNReal.ofReal H * volume U) →
    (∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧ |eval (u ω) D| ≤ E) →
    ∀ e, |D.coeff e| ≤ C₂ * (1 + K) ^ C₂ * (1 + H) ^ (6 : ℕ) * E := by
  obtain ⟨C, hC1, h242⟩ := Submission.k4_quadratic_mesh_coefficient_calibration
  refine ⟨C, hC1, ?_⟩
  intro K H E hK hH hE D hD Ω _ lam hlam u hu hdom hae
  have hpos : 0 < C * (1 + K) ^ C * (1 + H / 1) ^ (6 : ℕ) := by positivity
  set δ := 1 / (2 * (C * (1 + K) ^ C * (1 + H / 1) ^ (6 : ℕ))) with hδdef
  have hδ : 0 < δ := by positivity
  have hsmall : C * (1 + K) ^ C * (1 + H / 1) ^ (6 : ℕ) * δ ≤ 1 / 2 := by
    rw [hδdef]; field_simp; norm_num
  have hmeas : ∀ (S : Set (Fin 3 → ℝ)), MeasurableSet S →
      (lam.map u) S = lam (u ⁻¹' S) := fun S hS => Measure.map_apply hu hS
  have hgood : MeasurableSet {z : Fin 3 → ℝ | (∀ i, |z i| ≤ K) ∧ |eval z D| ≤ E} := by
    have hset : {z : Fin 3 → ℝ | (∀ i, |z i| ≤ K) ∧ |eval z D| ≤ E} =
        (⋂ i, {z : Fin 3 → ℝ | |z i| ≤ K}) ∩ {z | |eval z D| ≤ E} := by
      ext z; simp
    rw [hset]
    exact ((isClosed_iInter fun i => isClosed_le ((continuous_apply i).abs) continuous_const).inter
      (isClosed_le (MvPolynomial.continuous_eval D).abs continuous_const)).measurableSet
  have key := h242 K H 1 E δ hK (by linarith) one_pos hE hδ hsmall (lam.map u) inferInstance
    (by rw [hmeas _ MeasurableSet.univ, preimage_univ, measure_univ, ENNReal.ofReal_one])
    (fun q => by
      have hcell : MeasurableSet {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} := by
        have : {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} =
            ⋂ i, {z : Fin 3 → ℝ | ⌊z i / δ⌋ = q i} := by
          ext z; simp [_root_.funext_iff]
        rw [this]
        exact MeasurableSet.iInter fun i =>
          (measurableSet_singleton (q i)).preimage
            (Int.measurable_floor.comp (by fun_prop : Measurable fun z : Fin 3 → ℝ => z i / δ))
      rw [hmeas _ hcell]
      calc lam (u ⁻¹' {z | (fun i : Fin 3 => ⌊z i / δ⌋) = q})
          ≤ ENNReal.ofReal H * volume {z : Fin 3 → ℝ | (fun i : Fin 3 => ⌊z i / δ⌋) = q} :=
            hdom _ hcell
        _ = ENNReal.ofReal (H * δ ^ (3 : ℕ)) := by
            rw [volume_floor_cell δ hδ q, ← ENNReal.ofReal_mul (by linarith)])
    D hD ((ae_map_iff hu.aemeasurable hgood).mpr hae)
  intro e
  simpa using key e

/-! ### One stable sheet (accepted o171) and the vertex sheet (accepted o176) -/

theorem eval_map_snoc_qF {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) (w : ℂ) :
    eval (Fin.snoc z w) (F.map (algebraMap ℝ ℂ)) =
      (qa F : ℂ) * w ^ 2 + eval₂ (algebraMap ℝ ℂ) z (qb F) * w +
        eval₂ (algebraMap ℝ ℂ) z (qc F) := by
  have hdec := quadratic_decomposition F hF
  rw [← last_three] at hdec
  have hcomp : (Fin.snoc z w : Fin 4 → ℂ) ∘ Fin.castSucc = z := by
    funext i; simp
  have h3 : (Fin.snoc z w : Fin 4 → ℂ) 3 = w := by
    rw [last_three, Fin.snoc_last]
  rw [MvPolynomial.eval_map]
  conv_lhs => rw [hdec]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_rename, eval₂_C, eval₂_X, hcomp, h3]
  simp only [qa, qb, qc]
  have hc : (algebraMap ℝ ℂ) (curvature F 3 / 2) = ((curvature F 3 / 2 : ℝ) : ℂ) := rfl
  rw [hc]
  ring

theorem local_stable_sheet :
    ∃ C₁ : ℕ, 20 ≤ C₁ ∧ ∀ (A a_fit : ℝ), 2 ≤ A → 0 < a_fit →
    ∀ (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
    (∀ e, |(qdisc F).coeff e| ≤ A) → |qa F| * a_fit ≤ A ^ (-20 : ℝ) →
    ∀ (u₀ : Fin 3 → ℝ) (w₀ : ℝ), ‖toEuc u₀‖ ≤ A →
    |eval (Fin.snoc u₀ w₀) F| ≤ a_fit * A →
    A⁻¹ ≤ |eval (Fin.snoc u₀ w₀) (pderiv 3 F)| → |eval (Fin.snoc u₀ w₀) (pderiv 3 F)| ≤ A →
    ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
      DifferentiableOn ℂ f (ball (emb (toEuc u₀)) (A ^ (-(C₁ : ℝ)))) ∧
      (∀ z ∈ ball (emb (toEuc u₀)) (A ^ (-(C₁ : ℝ))),
        eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) (F.map (algebraMap ℝ ℂ)) = 0) ∧
      (∀ u : Fin 3 → ℝ, ‖toEuc u - toEuc u₀‖ < A ^ (-(C₁ : ℝ)) →
        (f (emb (toEuc u))).im = 0) ∧
      (∀ (u : Fin 3 → ℝ) (w : ℝ), ‖toEuc u - toEuc u₀‖ < A ^ (-(C₁ : ℝ)) →
        |eval (Fin.snoc u w) F| ≤ a_fit * A →
        0 < eval (Fin.snoc u w) (pderiv 3 F) * eval (Fin.snoc u₀ w₀) (pderiv 3 F) →
        |w - (f (emb (toEuc u))).re| ≤ a_fit * A ^ (C₁ : ℝ)) := by
  obtain ⟨C₁, hC₁, H171⟩ := Submission.k4_stable_quadratic_hidden_sheets
  refine ⟨C₁, hC₁, ?_⟩
  intro A a_fit hA ha_fit F hF hdisc hcurv u₀ w₀ hu₀ hF0 hFw0 hFw0'
  have hq0 := eval_snoc_qF hF u₀ w₀
  have hqw0 := eval_snoc_qFw hF u₀ w₀
  obtain ⟨f, hfd, hfrel, hfreal, hfclose⟩ := H171 A a_fit (qa F) hA ha_fit (qb F) (qc F)
    (qb_degree hF) (qc_degree hF) hdisc hcurv (toEuc u₀) w₀ hu₀
    (by
      have : eval (fun j => (toEuc u₀) j) (qb F) = eval u₀ (qb F) := rfl
      simpa [hq0, this, add_comm, add_left_comm, mul_comm] using hF0)
    (by
      rw [Real.rpow_neg_one]
      have : eval (fun j => (toEuc u₀) j) (qb F) = eval u₀ (qb F) := rfl
      rw [this]
      simpa [hqw0, mul_comm] using hFw0)
    (by
      have : eval (fun j => (toEuc u₀) j) (qb F) = eval u₀ (qb F) := rfl
      rw [this]
      simpa [hqw0, mul_comm] using hFw0')
  refine ⟨f, hfd, ?_, ?_, ?_⟩
  · intro z hz
    rw [eval_map_snoc_qF hF]
    have := hfrel z hz
    linear_combination this
  · intro u hu
    exact (hfreal (toEuc u) hu).1
  · intro u w hu hFuw hsign
    have hq := eval_snoc_qF hF u w
    have hqw := eval_snoc_qFw hF u w
    apply hfclose (toEuc u) w hu
    · simpa [hq, add_comm, add_left_comm, mul_comm] using hFuw
    · simpa [hqw, hqw0, mul_comm] using hsign

/-- The critical center of a quadratic test, as a sheet over the complex base. -/
def vertexSheet (F : MvPolynomial (Fin 4) ℝ) : EuclideanSpace ℂ (Fin 3) → ℂ :=
  fun z => eval₂ (algebraMap ℝ ℂ) (fun i : Fin 3 => z i) (centerPoly F)

theorem differentiable_vertexSheet (F : MvPolynomial (Fin 4) ℝ) :
    Differentiable ℂ (vertexSheet F) := by
  unfold vertexSheet
  have h := Submission.Obl.k4_stable_quadratic_hidden_sheets.differentiable_eval₂ (centerPoly F)
  exact h

/-- The relation of the vertex sheet. -/
def vertexRel (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 - rename Fin.castSucc ((centerPoly F).map (algebraMap ℝ ℂ))

theorem vertexRel_ne_zero (F : MvPolynomial (Fin 4) ℝ) : vertexRel F ≠ 0 := by
  intro h
  have h1 := congrArg (fun p => eval (Fin.snoc (0 : Fin 3 → ℂ) 1) p) h
  have h2 := congrArg (fun p => eval (Fin.snoc (0 : Fin 3 → ℂ) 0) p) h
  simp only [vertexRel, eval_sub, eval_X, eval_rename, map_zero] at h1 h2
  have hc : ∀ t : ℂ, (Fin.snoc (0 : Fin 3 → ℂ) t : Fin 4 → ℂ) ∘ Fin.castSucc = 0 := by
    intro t; funext i; simp
  rw [hc] at h1 h2
  have e1 : (Fin.snoc (0 : Fin 3 → ℂ) 1 : Fin 4 → ℂ) 3 = 1 := by
    rw [last_three, Fin.snoc_last]
  have e2 : (Fin.snoc (0 : Fin 3 → ℂ) 0 : Fin 4 → ℂ) 3 = 0 := by
    rw [last_three, Fin.snoc_last]
  rw [e1] at h1
  rw [e2] at h2
  have : (1 : ℂ) = 0 := by linear_combination h1 - h2
  exact one_ne_zero this

theorem vertexRel_degree {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) :
    (vertexRel F).totalDegree ≤ 2 := by
  unfold vertexRel
  apply (totalDegree_sub _ _).trans
  apply max_le
  · rw [totalDegree_X]; norm_num
  · apply (totalDegree_rename_le _ _).trans
    have hmap : ((centerPoly F).map (algebraMap ℝ ℂ)).totalDegree ≤ (centerPoly F).totalDegree :=
      Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) (centerPoly F))
    exact hmap.trans ((centerPoly_degree F hF).trans (by norm_num))

theorem eval_vertexRel (F : MvPolynomial (Fin 4) ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    eval (Fin.snoc (fun i : Fin 3 => z i) (vertexSheet F z)) (vertexRel F) = 0 := by
  simp only [vertexRel, eval_sub, eval_X, eval_rename]
  have hc : (Fin.snoc (fun i : Fin 3 => z i) (vertexSheet F z) : Fin 4 → ℂ) ∘ Fin.castSucc =
      fun i : Fin 3 => z i := by
    funext i; simp
  have h3 : (Fin.snoc (fun i : Fin 3 => z i) (vertexSheet F z) : Fin 4 → ℂ) 3 =
      vertexSheet F z := by
    rw [last_three, Fin.snoc_last]
  rw [hc, h3, eval_map]
  simp [vertexSheet]

theorem vertexSheet_emb (F : MvPolynomial (Fin 4) ℝ) (u : Fin 3 → ℝ) :
    vertexSheet F (emb (toEuc u)) = ((eval u (centerPoly F) : ℝ) : ℂ) := by
  unfold vertexSheet emb
  have : (fun i : Fin 3 => (WithLp.toLp 2 (fun i => ((toEuc u) i : ℂ)) :
      EuclideanSpace ℂ (Fin 3)) i) = fun i => ((u i : ℝ) : ℂ) := by
    funext i; rfl
  rw [this]
  exact (MvPolynomial.eval₂_comp_left (algebraMap ℝ ℂ) _ _ _).symm.trans
    (by simp)

/-- At high curvature the hidden coordinate is within `|∂_w F| / |∂_w² F|` of the vertex. -/
theorem abs_sub_vertex_le {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (hc : curvature F 3 ≠ 0) (u : Fin 3 → ℝ) (w : ℝ) :
    |w - eval u (centerPoly F)| = |eval (Fin.snoc u w) (pderiv 3 F)| / |curvature F 3| := by
  rw [eval_snoc_qFw hF, centerPoly, eval_mul, eval_C, qa, qb, ← last_three]
  rw [eq_div_iff (abs_pos.mpr hc).ne', ← abs_mul]
  congr 1
  field_simp
  ring

/-- Normalizing a local sheet to the unit ball. -/
theorem isSheet_of_local {f : EuclideanSpace ℂ (Fin 3) → ℂ} {R : MvPolynomial (Fin 4) ℂ}
    (hR0 : R ≠ 0) (hRd : R.totalDegree ≤ 2) {c : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hr : 0 < r) (hhol : DifferentiableOn ℂ f (ball (emb c) (4 * r)))
    (hrel : ∀ z ∈ ball (emb c) (4 * r),
      eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) R = 0)
    (hreal : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x - c‖ ≤ r → (f (emb x)).im = 0) :
    IsSheet 2 (fun z => f (emb c + ((r : ℝ) : ℂ) • z)) := by
  have hmaps : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      emb c + ((r : ℝ) : ℂ) • z ∈ ball (emb c) (4 * r) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    nlinarith
  refine ⟨Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation
      (fun i => (emb c) i) (r : ℂ) 1 R, fun h => hR0 ?_,
    (Submission.Obl.k4_algebraic_real_jet_comparison.totalDegree_affineRelation_le _ _ _ _).trans
      hRd, ?_, ?_, ?_⟩
  · exact Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation_injective _
      (by exact_mod_cast hr.ne') one_ne_zero (h.trans (map_zero _).symm)
  · exact hhol.comp (by fun_prop) hmaps
  · intro z hz
    rw [Submission.Obl.k4_algebraic_real_jet_comparison.eval_affineRelation, one_mul]
    have h := hrel _ (hmaps z hz)
    have hfun : (fun i : Fin 3 => (emb c) i + (r : ℂ) * z i) =
        fun i : Fin 3 => (emb c + ((r : ℝ) : ℂ) • z) i := by
      funext i; simp
    rw [hfun]
    exact h
  · intro x hx
    have hpt : emb c + ((r : ℝ) : ℂ) • emb x = emb (c + r • x) := by
      rw [emb_add, emb_smul]
    simp only [hpt]
    apply hreal
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]

/-! ### Numerics -/

theorem le_pow_of_two_le {X : ℝ} (hX : 2 ≤ X) (n : ℕ) : (n : ℝ) ≤ X ^ n := by
  have h2n : (n : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this.le
  exact h2n.trans (pow_le_pow_left₀ (by norm_num) hX n)

/-- The discriminant calibration constant is a fixed power of `K H`. -/
theorem calib_le_pow {C₂ K H : ℝ} (hC₂ : 1 ≤ C₂) (hK : 2 ≤ K) (hH : 1 ≤ H) :
    C₂ * (1 + K) ^ C₂ * (1 + H) ^ (6 : ℕ) * (3 * K ^ 2) ≤
      (K * H) ^ (3 * ⌈C₂⌉₊ + 10) := by
  set N := ⌈C₂⌉₊ with hN
  have hX : 2 ≤ K * H := by nlinarith
  have hX1 : 1 ≤ K * H := by linarith
  have hC₂N : C₂ ≤ N := Nat.le_ceil C₂
  have hKX : K ≤ K * H := by nlinarith
  have h1 : C₂ ≤ (K * H) ^ N := hC₂N.trans (le_pow_of_two_le hX N)
  have h2 : (1 + K) ^ C₂ ≤ (K * H) ^ (2 * N) := by
    have h1K : 1 + K ≤ (K * H) ^ 2 := by nlinarith
    calc (1 + K) ^ C₂ ≤ (1 + K) ^ (N : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hC₂N
      _ = (1 + K) ^ N := Real.rpow_natCast _ _
      _ ≤ ((K * H) ^ 2) ^ N := pow_le_pow_left₀ (by linarith) h1K N
      _ = (K * H) ^ (2 * N) := by rw [← pow_mul]
  have h3 : (1 + H) ^ (6 : ℕ) ≤ (K * H) ^ 6 := by
    apply pow_le_pow_left₀ (by linarith); nlinarith
  have h4 : 3 * K ^ 2 ≤ (K * H) ^ 4 := by
    have : K ^ 2 ≤ (K * H) ^ 2 := pow_le_pow_left₀ (by linarith) hKX 2
    have h5 : (3 : ℝ) ≤ (K * H) ^ 2 := by nlinarith
    calc 3 * K ^ 2 ≤ (K * H) ^ 2 * (K * H) ^ 2 := by gcongr
      _ = (K * H) ^ 4 := by ring
  calc C₂ * (1 + K) ^ C₂ * (1 + H) ^ (6 : ℕ) * (3 * K ^ 2)
      ≤ (K * H) ^ N * (K * H) ^ (2 * N) * (K * H) ^ 6 * (K * H) ^ 4 := by
        gcongr
    _ = (K * H) ^ (3 * N + 10) := by
        rw [← pow_add, ← pow_add, ← pow_add]; ring_nf

/-! ### The covering grid -/

theorem emb_sub (x y : EuclideanSpace ℝ (Fin 3)) : emb (x - y) = emb x - emb y := by
  ext i; simp [emb]

theorem dist_emb (x y : EuclideanSpace ℝ (Fin 3)) : dist (emb x) (emb y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← emb_sub, norm_emb]

theorem norm_toEuc_le {x : Fin 3 → ℝ} {s : ℝ} (hs : 0 ≤ s) (hx : ∀ i, |x i| ≤ s / 2) :
    ‖toEuc x‖ ≤ s := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hs, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs]
  have h : ∀ i, (toEuc x) i ^ 2 ≤ (s / 2) ^ 2 := fun i => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
  calc ∑ i, (toEuc x) i ^ 2 ≤ ∑ _i : Fin 3, (s / 2) ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = 3 * (s / 2) ^ 2 := by simp
    _ ≤ s ^ 2 := by nlinarith

/-- Grid points of spacing `s`, indexed from `-M` to `M` in each coordinate. -/
def gridPt (s : ℝ) (M : ℕ) (m : Fin 3 → Fin (2 * M + 1)) : EuclideanSpace ℝ (Fin 3) :=
  toEuc fun i => s * (((m i : ℕ) : ℝ) - M)

theorem exists_gridPt_near {s K : ℝ} (hs : 0 < s) (hK : 0 ≤ K) (v : Fin 3 → ℝ)
    (hv : ∀ i, |v i| ≤ K) :
    ∃ m : Fin 3 → Fin (2 * (⌈K / s⌉₊ + 1) + 1),
      ‖toEuc v - gridPt s (⌈K / s⌉₊ + 1) m‖ ≤ s := by
  set M := ⌈K / s⌉₊ + 1 with hM
  have hround : ∀ i, |round (v i / s)| ≤ (⌈K / s⌉₊ : ℤ) := by
    intro i
    have h1 : |v i / s| ≤ K / s := by
      rw [abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right (hv i) hs.le
    have h2 := abs_sub_round (v i / s)
    have h3 : (|round (v i / s)| : ℝ) ≤ K / s + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub ((round (v i / s) : ℝ)) (v i / s)
      rw [abs_sub_comm] at h2
      push_cast at this ⊢
      linarith
    have h4 : (|round (v i / s)| : ℝ) < (⌈K / s⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil (K / s)
      linarith
    have h5 : (|round (v i / s)| : ℤ) < (⌈K / s⌉₊ : ℤ) + 1 := by exact_mod_cast h4
    omega
  have hlt : ∀ i, (round (v i / s) + M).toNat < 2 * M + 1 := by
    intro i
    have := hround i
    rw [abs_le] at this
    omega
  refine ⟨fun i => ⟨(round (v i / s) + M).toNat, hlt i⟩, ?_⟩
  apply norm_toEuc_le hs.le
  intro i
  have hnn : 0 ≤ round (v i / s) + M := by
    have := hround i
    rw [abs_le] at this
    omega
  have hcast : (((round (v i / s) + M).toNat : ℕ) : ℝ) - M = (round (v i / s) : ℝ) := by
    have : (((round (v i / s) + M).toNat : ℕ) : ℤ) = round (v i / s) + M := Int.toNat_of_nonneg hnn
    have h' : ((((round (v i / s) + M).toNat : ℕ) : ℤ) : ℝ) = ((round (v i / s) + M : ℤ) : ℝ) := by
      rw [this]
    push_cast at h'
    linarith
  show |v i - s * ((((round (v i / s) + M).toNat : ℕ) : ℝ) - M)| ≤ s / 2
  rw [hcast]
  have h2 := abs_sub_round (v i / s)
  calc |v i - s * (round (v i / s) : ℝ)| = s * |v i / s - round (v i / s)| := by
        rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]
        congr 1
        field_simp
    _ ≤ s * (1 / 2) := by gcongr
    _ = s / 2 := by ring

/-- **Stable root cover.** -/
theorem stable_root_cover :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K H a : ℝ), 2 ≤ K → 1 ≤ H → 0 < a → a ≤ 1 →
    ∀ (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
    ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u →
    (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
      lam (u ⁻¹' U) ≤ ENNReal.ofReal H * volume U) →
    (∀ᵐ ω ∂lam, (∀ i, |u ω i| ≤ K) ∧
      |eval (Fin.snoc (u ω) (w ω)) F| ≤ K * a ∧
      K⁻¹ ≤ |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ∧
      |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ≤ K ∧
      |curvature F 3| ≤ K / a) →
    ∃ (r : ℝ) (n : ℕ) (c : Fin n → EuclideanSpace ℝ (Fin 3))
      (f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ),
      (K * H) ^ (-(C : ℝ)) ≤ r ∧ r ≤ 1 ∧ (n : ℝ) ≤ (K * H) ^ (C : ℝ) ∧
      (∀ j, IsSheet 2 (fun z => f j (emb (c j) + ((r : ℝ) : ℂ) • z))) ∧
      ∀ᵐ ω ∂lam, ∃ j, ‖toEuc (u ω) - c j‖ ≤ r / 4 ∧
        |w ω - (f j (emb (toEuc (u ω)))).re| ≤ (K * H) ^ (C : ℝ) * a := by
  classical
  obtain ⟨C₂, hC₂, hcal⟩ := coeff_bound_of_density
  obtain ⟨C₁, hC₁, hloc⟩ := local_stable_sheet
  set cA : ℕ := 3 * ⌈C₂⌉₊ + 10 with hcA
  set e : ℕ := cA * C₁ with he
  set Cfin : ℕ := 3 * e + 20 * cA + 25 with hCfin
  refine ⟨Cfin, by omega, ?_⟩
  intro K H a hK hH ha ha1 F hF Ω _ lam hlam u w hu hdom hae
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = K * H := ⟨_, rfl⟩
  have hX : 2 ≤ X := by
    rw [hXdef]
    calc (2 : ℝ) = 2 * 1 := by norm_num
      _ ≤ K * H := mul_le_mul hK hH (by norm_num) (by linarith only [hK])
  have hXpos : 0 < X := by linarith only [hX]
  have hX1 : 1 ≤ X := by linarith only [hX]
  have hKX : K ≤ X := by rw [hXdef]; exact le_mul_of_one_le_right (by linarith only [hK]) hH
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = X ^ cA := ⟨_, rfl⟩
  have hA2 : 2 ≤ A := by rw [hAdef]; exact hX.trans (le_self_pow₀ hX1 (by omega))
  have hApos : 0 < A := by linarith only [hA2]
  have hKA : 2 * K ≤ A := by
    have : X ^ 2 ≤ A := by rw [hAdef]; exact pow_le_pow_right₀ hX1 (by omega)
    calc 2 * K ≤ 2 * X := by linarith only [hKX]
      _ ≤ X * X := mul_le_mul_of_nonneg_right hX hXpos.le
      _ = X ^ 2 := by ring
      _ ≤ A := this
  -- the good set
  set G : Set Ω := {ω | (∀ i, |u ω i| ≤ K) ∧ |eval (Fin.snoc (u ω) (w ω)) F| ≤ K * a ∧
      K⁻¹ ≤ |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ∧
      |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| ≤ K ∧ |curvature F 3| ≤ K / a} with hGdef
  have haeG : ∀ᵐ ω ∂lam, ω ∈ G := hae
  -- the discriminant coefficients
  have hdisc : ∀ e', |(qdisc F).coeff e'| ≤ A := by
    intro e'
    have h := hcal K H (3 * K ^ 2) (by linarith) hH (by positivity) (qdisc F) (qdisc_degree hF)
      Ω lam hlam u hu hdom (by
        filter_upwards [hae] with ω hω
        exact ⟨hω.1, abs_eval_qdisc_le hF ha (u ω) (w ω) hω.2.1 hω.2.2.2.1 hω.2.2.2.2⟩) e'
    exact h.trans (by rw [hAdef, hXdef]; exact calib_le_pow hC₂ hK hH)
  -- the radius and the grid
  have hXe : 0 < X ^ e := by positivity
  set r : ℝ := (X ^ e)⁻¹ / 8 with hrdef
  have hr : 0 < r := by positivity
  have hAr : A ^ (-(C₁ : ℝ)) = 8 * r := by
    rw [hrdef, Real.rpow_neg hApos.le, Real.rpow_natCast, hAdef, ← pow_mul]
    ring
  set s : ℝ := r / 4 with hsdef
  have hs : 0 < s := by positivity
  set M : ℕ := ⌈K / s⌉₊ + 1 with hMdef
  have hnear : ∀ ω ∈ G, ∃ m : Fin 3 → Fin (2 * M + 1),
      ‖toEuc (u ω) - gridPt s M m‖ ≤ r / 4 := by
    intro ω hω
    obtain ⟨m, hm⟩ := exists_gridPt_near hs (by linarith) (u ω) hω.1
    exact ⟨m, hm.trans (le_of_eq hsdef)⟩
  have hnormu : ∀ ω ∈ G, ‖toEuc (u ω)‖ ≤ A := by
    intro ω hω
    have : ‖toEuc (u ω)‖ ≤ 2 * K := norm_toEuc_le (by linarith) fun i => by
      have := hω.1 i; linarith
    linarith
  -- the index set
  let I := (Fin 3 → Fin (2 * M + 1)) × Bool
  set n := Fintype.card I with hn
  let eI : I ≃ Fin n := Fintype.equivFin I
  have hFne : F ≠ 0 := by
    intro h0
    obtain ⟨ω, hω⟩ := haeG.exists
    have := hω.2.2.1
    simp only [h0, map_zero, abs_zero] at this
    have : (0 : ℝ) < K⁻¹ := by positivity
    linarith
  have hFmap0 : F.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h0
    apply hFne
    exact MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective ℝ ℂ)
      (h0.trans (map_zero _).symm)
  have hFmapdeg : (F.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 :=
    (Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) F)).trans hF
  -- counting
  have hcount : (n : ℝ) ≤ X ^ Cfin := by
    have hcard : n = (2 * M + 1) ^ 3 * 2 := by
      simp only [hn, I, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hceil : (⌈K / s⌉₊ : ℝ) ≤ K / s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hKs : K / s = 32 * K * X ^ e := by
      rw [hsdef, hrdef]; field_simp; ring
    have hX7 : (69 : ℝ) ≤ X ^ 7 := by
      have : (2 : ℝ) ^ 7 ≤ X ^ 7 := pow_le_pow_left₀ (by norm_num) hX 7
      norm_num at this; linarith only [this]
    have hXe1 : (1 : ℝ) ≤ X ^ (e + 1) := one_le_pow₀ hX1
    have hKXe : K * X ^ e ≤ X ^ (e + 1) := by
      rw [pow_succ, mul_comm (X ^ e) X]; exact mul_le_mul_of_nonneg_right hKX hXe.le
    have hM8 : ((2 * M + 1 : ℕ) : ℝ) ≤ X ^ (e + 8) := by
      push_cast [hMdef]
      calc 2 * ((⌈K / s⌉₊ : ℝ) + 1) + 1 ≤ 2 * (K / s + 1 + 1) + 1 := by linarith only [hceil]
        _ = 64 * (K * X ^ e) + 5 := by rw [hKs]; ring
        _ ≤ 64 * X ^ (e + 1) + 5 * X ^ (e + 1) := by linarith only [hKXe, hXe1]
        _ = 69 * X ^ (e + 1) := by ring
        _ ≤ X ^ 7 * X ^ (e + 1) := mul_le_mul_of_nonneg_right hX7 (by positivity)
        _ = X ^ (e + 8) := by rw [← pow_add]; ring_nf
    rw [hcard]
    push_cast
    calc ((2 * (M : ℝ) + 1)) ^ 3 * 2 ≤ (X ^ (e + 8)) ^ 3 * X := by
          have hM8' : 2 * (M : ℝ) + 1 ≤ X ^ (e + 8) := by exact_mod_cast hM8
          gcongr
      _ = X ^ (3 * e + 25) := by rw [← pow_mul, ← pow_succ]; ring_nf
      _ ≤ X ^ Cfin := pow_le_pow_right₀ hX1 (by omega)
  have hrX : X ^ (-(Cfin : ℝ)) ≤ r := by
    rw [Real.rpow_neg hXpos.le, Real.rpow_natCast, hrdef]
    have h8 : (8 : ℝ) ≤ X ^ 3 := by
      have : (2 : ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
      norm_num at this; linarith only [this]
    have hle : X ^ e * 8 ≤ X ^ Cfin := by
      calc X ^ e * 8 ≤ X ^ e * X ^ 3 := mul_le_mul_of_nonneg_left h8 hXe.le
        _ = X ^ (e + 3) := by rw [← pow_add]
        _ ≤ X ^ Cfin := pow_le_pow_right₀ hX1 (by omega)
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) hle
  have hr1 : r ≤ 1 := by
    rw [hrdef]
    have : (X ^ e)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hX1)
    linarith
  by_cases hlow : |qa F| * (K * a) ≤ A ^ (-20 : ℝ)
  · -- low curvature: one stable sheet per grid cell and branch
    have hex : ∀ ω ∈ G, ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
        DifferentiableOn ℂ f (ball (emb (toEuc (u ω))) (A ^ (-(C₁ : ℝ)))) ∧
        (∀ z ∈ ball (emb (toEuc (u ω))) (A ^ (-(C₁ : ℝ))),
          eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) (F.map (algebraMap ℝ ℂ)) = 0) ∧
        (∀ v : Fin 3 → ℝ, ‖toEuc v - toEuc (u ω)‖ < A ^ (-(C₁ : ℝ)) →
          (f (emb (toEuc v))).im = 0) ∧
        (∀ (v : Fin 3 → ℝ) (w' : ℝ), ‖toEuc v - toEuc (u ω)‖ < A ^ (-(C₁ : ℝ)) →
          |eval (Fin.snoc v w') F| ≤ (K * a) * A →
          0 < eval (Fin.snoc v w') (pderiv 3 F) * eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) →
          |w' - (f (emb (toEuc v))).re| ≤ (K * a) * A ^ (C₁ : ℝ)) := by
      intro ω hω
      obtain ⟨hu1, hF1, hFw1, hFw2, hc1⟩ := hω
      exact hloc A (K * a) hA2 (by positivity) F hF hdisc hlow (u ω) (w ω) (hnormu ω ⟨hu1, hF1, hFw1, hFw2, hc1⟩)
        (hF1.trans (le_mul_of_one_le_right (by positivity) (by linarith)))
        ((inv_anti₀ (by linarith) (by linarith : K ≤ A)).trans hFw1) (hFw2.trans (by linarith))
    choose! sheetAt hsheetAt using hex
    let wit : I → Ω → Prop := fun mσ ω => ω ∈ G ∧ ‖toEuc (u ω) - gridPt s M mσ.1‖ ≤ r ∧
      (0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) ↔ mσ.2 = true)
    let patch : I → EuclideanSpace ℂ (Fin 3) → ℂ := fun mσ =>
      if h : ∃ ω, wit mσ ω then sheetAt (Classical.choose h) else fun _ => 0
    have hball : ∀ (m : Fin 3 → Fin (2 * M + 1)) (ω₀ : Ω),
        ‖toEuc (u ω₀) - gridPt s M m‖ ≤ r →
        ball (emb (gridPt s M m)) (4 * r) ⊆ ball (emb (toEuc (u ω₀))) (A ^ (-(C₁ : ℝ))) := by
      intro m ω₀ hd z hz
      rw [mem_ball] at hz ⊢
      rw [hAr]
      calc dist z (emb (toEuc (u ω₀))) ≤ dist z (emb (gridPt s M m)) +
            dist (emb (gridPt s M m)) (emb (toEuc (u ω₀))) := dist_triangle _ _ _
        _ < 4 * r + r := by
            have h2 : dist (emb (gridPt s M m)) (emb (toEuc (u ω₀))) ≤ r := by
              rw [dist_emb, dist_comm, dist_eq_norm]; exact hd
            linarith only [hz, h2]
        _ ≤ 8 * r := by linarith only [hr]
    refine ⟨r, n, fun j => gridPt s M (eI.symm j).1, fun j => patch (eI.symm j), ?_, hr1, ?_, ?_, ?_⟩
    · rw [← hXdef]; exact hrX
    · rw [← hXdef, Real.rpow_natCast]; exact hcount
    · intro j
      show IsSheet 2 (fun z => patch (eI.symm j) (emb (gridPt s M (eI.symm j).1) + ((r : ℝ) : ℂ) • z))
      by_cases h : ∃ ω, wit (eI.symm j) ω
      · have hpatch : patch (eI.symm j) = sheetAt (Classical.choose h) := by
          simp only [patch, dif_pos h]
        rw [hpatch]
        obtain ⟨hω₀G, hω₀d, -⟩ := Classical.choose_spec h
        obtain ⟨hhol, hrel, hreal, -⟩ := hsheetAt _ hω₀G
        apply isSheet_of_local hFmap0 hFmapdeg hr
        · exact hhol.mono (hball _ _ hω₀d)
        · intro z hz; exact hrel z (hball _ _ hω₀d hz)
        · intro x hx
          have hx' : ‖toEuc (WithLp.ofLp x) - toEuc (u (Classical.choose h))‖ <
              A ^ (-(C₁ : ℝ)) := by
            rw [hAr]
            simp only [toEuc, WithLp.toLp_ofLp]
            calc ‖x - toEuc (u (Classical.choose h))‖ ≤
                ‖x - gridPt s M (eI.symm j).1‖ + ‖gridPt s M (eI.symm j).1 -
                  toEuc (u (Classical.choose h))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ r + r := by
                  rw [norm_sub_rev (gridPt s M _)]; linarith only [hx, hω₀d]
              _ < 8 * r := by linarith only [hr]
          have := hreal _ hx'
          simpa only [toEuc, WithLp.toLp_ofLp] using this
      · have hpatch : patch (eI.symm j) = fun _ => 0 := by
          simp only [patch, dif_neg h]
        rw [hpatch]
        exact isSheet_zero (by norm_num)
    · filter_upwards [haeG] with ω hω
      obtain ⟨m, hm⟩ := hnear ω hω
      set σ : Bool := decide (0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)) with hσ
      have hwit : ∃ ω', wit (m, σ) ω' :=
        ⟨ω, hω, hm.trans (by linarith only [hr]), by simp [hσ]⟩
      refine ⟨eI (m, σ), ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]; exact hm
      · simp only [Equiv.symm_apply_apply]
        have hpatch : patch (m, σ) = sheetAt (Classical.choose hwit) := by
          simp only [patch, dif_pos hwit]
        rw [hpatch]
        obtain ⟨hω₀G, hω₀d, hω₀s⟩ := Classical.choose_spec hwit
        obtain ⟨-, -, -, hclose⟩ := hsheetAt _ hω₀G
        have hd : ‖toEuc (u ω) - toEuc (u (Classical.choose hwit))‖ < A ^ (-(C₁ : ℝ)) := by
          rw [hAr]
          calc ‖toEuc (u ω) - toEuc (u (Classical.choose hwit))‖ ≤
              ‖toEuc (u ω) - gridPt s M m‖ + ‖gridPt s M m - toEuc (u (Classical.choose hwit))‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ r / 4 + r := by
                rw [norm_sub_rev (gridPt s M m)]; linarith only [hm, hω₀d]
            _ < 8 * r := by linarith only [hr]
        have hFw0 : eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) ≠ 0 := by
          intro h0
          have := hω.2.2.1
          rw [h0, abs_zero] at this
          have : (0 : ℝ) < K⁻¹ := by positivity
          linarith
        have hFw1 : eval (Fin.snoc (u (Classical.choose hwit)) (w (Classical.choose hwit)))
            (pderiv 3 F) ≠ 0 := by
          intro h0
          have := hω₀G.2.2.1
          rw [h0, abs_zero] at this
          have : (0 : ℝ) < K⁻¹ := by positivity
          linarith
        have hsign : 0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) *
            eval (Fin.snoc (u (Classical.choose hwit)) (w (Classical.choose hwit))) (pderiv 3 F) := by
          by_cases hp : 0 < eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)
          · have hσt : σ = true := by simp [hσ, hp]
            have hp' := hω₀s.mpr hσt
            exact mul_pos hp hp'
          · have hσf : σ = false := by simp [hσ, hp]
            have hp' : ¬ 0 < eval (Fin.snoc (u (Classical.choose hwit))
                (w (Classical.choose hwit))) (pderiv 3 F) := by
              intro hh; have := hω₀s.mp hh; rw [hσf] at this; exact Bool.false_ne_true this
            have hneg : eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F) < 0 :=
              lt_of_le_of_ne (not_lt.mp hp) hFw0
            have hneg' := lt_of_le_of_ne (not_lt.mp hp') hFw1
            exact mul_pos_of_neg_of_neg hneg hneg'
        have hcl := hclose (u ω) (w ω) hd
          (hω.2.1.trans (le_mul_of_one_le_right (by positivity) (by linarith only [hA2]))) hsign
        refine hcl.trans ?_
        have hAC : A ^ (C₁ : ℝ) = X ^ e := by
          rw [Real.rpow_natCast, hAdef, ← pow_mul]
        rw [hAC, ← hXdef, Real.rpow_natCast]
        have hle : K * X ^ e ≤ X ^ Cfin := by
          calc K * X ^ e ≤ X * X ^ e := mul_le_mul_of_nonneg_right hKX hXe.le
            _ = X ^ (e + 1) := by rw [pow_succ, mul_comm]
            _ ≤ X ^ Cfin := pow_le_pow_right₀ hX1 (by omega)
        calc K * a * X ^ e = (K * X ^ e) * a := by ring
          _ ≤ X ^ Cfin * a := mul_le_mul_of_nonneg_right hle ha.le
  · -- high curvature: the vertex sheet everywhere
    rw [not_le] at hlow
    have hA20 : A ^ (-20 : ℝ) = (X ^ (20 * cA))⁻¹ := by
      rw [Real.rpow_neg hApos.le, show ((20 : ℝ)) = ((20 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, hAdef, ← pow_mul, mul_comm]
    have hqa : 0 < |qa F| := by
      by_contra h0
      rw [not_lt] at h0
      have : |qa F| * (K * a) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)
      have : (0 : ℝ) < A ^ (-20 : ℝ) := Real.rpow_pos_of_pos hApos _
      linarith only [this, ‹|qa F| * (K * a) ≤ 0›, hlow]
    have hcurv0 : curvature F 3 ≠ 0 := by
      intro h0; rw [qa, h0, zero_div, abs_zero] at hqa; exact lt_irrefl _ hqa
    have hcurvabs : |curvature F 3| = 2 * |qa F| := by
      rw [qa, abs_div]; norm_num; ring
    refine ⟨r, n, fun j => gridPt s M (eI.symm j).1, fun _ => vertexSheet F, ?_, hr1, ?_, ?_, ?_⟩
    · rw [← hXdef]; exact hrX
    · rw [← hXdef, Real.rpow_natCast]; exact hcount
    · intro j
      apply isSheet_of_local (vertexRel_ne_zero F) (vertexRel_degree hF) hr
      · exact (differentiable_vertexSheet F).differentiableOn
      · intro z _; exact eval_vertexRel F z
      · intro x _
        have hx : x = toEuc (WithLp.ofLp x) := by simp [toEuc]
        rw [hx, vertexSheet_emb]
        simp
    · filter_upwards [haeG] with ω hω
      obtain ⟨m, hm⟩ := hnear ω hω
      refine ⟨eI (m, true), by simp only [Equiv.symm_apply_apply]; exact hm, ?_⟩
      rw [vertexSheet_emb, Complex.ofReal_re, abs_sub_vertex_le hF hcurv0, hcurvabs]
      have hFw := hω.2.2.2.1
      -- `|∂_w F| / (2 |qa F|) ≤ K * (K * a) * A ^ 20 / 2`
      have hinv : (2 * |qa F|)⁻¹ ≤ K * a * X ^ (20 * cA) / 2 := by
        have h1 : (X ^ (20 * cA))⁻¹ < |qa F| * (K * a) := by rw [← hA20]; exact hlow
        have hKa : 0 < K * a := by positivity
        have hpos20 : 0 < X ^ (20 * cA) := by positivity
        have h2 : 1 < |qa F| * (K * a) * X ^ (20 * cA) := by
          rw [inv_lt_iff_one_lt_mul₀ hpos20] at h1
          linarith only [h1]
        have hq0 : |qa F| ≠ 0 := hqa.ne'
        calc (2 * |qa F|)⁻¹ = (2 * |qa F|)⁻¹ * 1 := (mul_one _).symm
          _ ≤ (2 * |qa F|)⁻¹ * (|qa F| * (K * a) * X ^ (20 * cA)) := by
              gcongr
          _ = K * a * X ^ (20 * cA) / 2 := by field_simp
      have hfin : K * (K * a * X ^ (20 * cA) / 2) ≤ X ^ Cfin * a := by
        have hK2 : K * K ≤ X ^ 2 := by
          rw [sq]; exact mul_le_mul hKX hKX (by linarith only [hK]) hXpos.le
        have hle : X ^ 2 * X ^ (20 * cA) ≤ X ^ Cfin := by
          rw [← pow_add]; exact pow_le_pow_right₀ hX1 (by omega)
        calc K * (K * a * X ^ (20 * cA) / 2) = (K * K) * X ^ (20 * cA) * a / 2 := by ring
          _ ≤ X ^ 2 * X ^ (20 * cA) * a / 2 := by gcongr
          _ ≤ X ^ Cfin * a / 2 := by gcongr
          _ ≤ X ^ Cfin * a := by
              have : 0 ≤ X ^ Cfin * a := by positivity
              linarith only [this]
      rw [← hXdef, Real.rpow_natCast]
      calc |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| / (2 * |qa F|)
          = |eval (Fin.snoc (u ω) (w ω)) (pderiv 3 F)| * (2 * |qa F|)⁻¹ := div_eq_mul_inv _ _
        _ ≤ K * (K * a * X ^ (20 * cA) / 2) :=
            mul_le_mul hFw hinv (by positivity) (by linarith only [hK])
        _ ≤ X ^ Cfin * a := hfin

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
