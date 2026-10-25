-- Lane B: the cleared cubic numerator at one event, from seven tubes of its fine state.
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EventTubes
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.PotCubic
import Submission.Obl.k4_physical_parent_potential_candidates.GraphPointwiseConic
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniImplicit

/-!
# The cleared numerator at one event (lane B, step 3)

At a point `u` of the zoomed base, seven tubes of group points through nearby events of the same
fine state (directions `p i` in `A`-general position, anchors within `hδ` of `u`) give:

* the seven Hessian tests of the normalized graph `g = (f - c₀ - L) / s0` at `u`;
* (potential route) the cleared numerator `cleared (D²g u) (D³P0 u) / s0`, with the cubic tests
  of the potential `P0` from its quadratic fits along the tubes, transferred to `u`;
* (graph route) the same numerator, through the implicit identity
  `cleared (D²g) (D³P0) = s0 * Fw * cleared (D²g) (D³g)` with `Fw = 2 a f + Bδ`, and the raw
  third-order graph tests.

The first route is linear in the tube width when `s0` is at least the potential's scale, the
second when it is at most; the caller chooses.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial
open FubiniHessian
open scoped ContDiff

/-! ### Helpers: polynomial jets and the normalized graph -/

/-- A third formal partial derivative of a polynomial of total degree at most two vanishes. -/
private lemma pderiv_three_eq_zero {σ : Type*} (Q : MvPolynomial σ ℝ) (hQ : Q.totalDegree ≤ 2)
    (i j k : σ) : pderiv i (pderiv j (pderiv k Q)) = 0 := by
  ext m
  have hz : Q.coeff (m + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1) = 0 := by
    by_contra hne
    have hdeg := le_totalDegree (mem_support_iff.mpr hne)
    have h3 : Finsupp.degree (m + Finsupp.single i 1 + Finsupp.single j 1 +
        Finsupp.single k 1) = Finsupp.degree m + 3 := by
      simp only [map_add, Finsupp.degree_single]
    have h3' : (m + Finsupp.single i 1 + Finsupp.single j 1 +
        Finsupp.single k 1).sum (fun _ e => e) = Finsupp.degree m + 3 := h3
    omega
  simp [coeff_pderiv, hz]

/-- A polynomial curve: derivative of the evaluation of a polynomial along a differentiable
curve, by the chain rule over the monomials. -/
private lemma hasDerivAt_eval_curve {ι : Type*} [Fintype ι] (F : MvPolynomial ι ℝ) (z : ℝ → ι → ℝ)
    (z' : ι → ℝ) (t : ℝ) (hz : ∀ l, HasDerivAt (fun s => z s l) (z' l) t) :
    HasDerivAt (fun s => eval (z s) F) (∑ l, eval (z t) (pderiv l F) * z' l) t := by
  classical
  induction F using MvPolynomial.induction_on with
  | C r =>
      simp only [eval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      exact hasDerivAt_const t r
  | add p r hp hr =>
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      exact hp.add hr
  | mul_X p j hp =>
      simp only [map_mul, eval_X, pderiv_mul, map_add, pderiv_X, add_mul]
      have h := hp.mul (hz j)
      convert h using 1
      rw [Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro l _
        ring
      · rw [Finset.sum_eq_single j]
        · simp
        · intro l _ hl
          simp [Ne.symm hl]
        · intro h
          exact absurd (Finset.mem_univ j) h

/-- A polynomial in the four coordinates, evaluated on the base at hidden coordinate zero. -/
private def zeroSlice (Q : MvPolynomial (Fin 4) ℝ) : Base → ℝ := fun z => eval ![z 0, z 1, z 2, 0] Q

private lemma contDiff_zeroSlice (Q : MvPolynomial (Fin 4) ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (zeroSlice Q) := by
  have hcoord : ∀ l : Fin 4,
      ContDiff ℝ n (fun z : Base => (![z 0, z 1, z 2, 0] : Fin 4 → ℝ) l) := by
    intro l
    fin_cases l
    · exact contDiff_piLp_apply (𝕜 := ℝ) 2
    · exact contDiff_piLp_apply (𝕜 := ℝ) 2
    · exact contDiff_piLp_apply (𝕜 := ℝ) 2
    · exact contDiff_const
  induction Q using MvPolynomial.induction_on with
  | C r =>
      have h : zeroSlice (C r) = fun _ => r := by funext z; simp [zeroSlice]
      rw [h]; exact contDiff_const
  | add p r hp hr =>
      have h : zeroSlice (p + r) = fun z => zeroSlice p z + zeroSlice r z := by
        funext z; simp [zeroSlice]
      rw [h]; exact hp.add hr
  | mul_X p j hp =>
      have h : zeroSlice (p * X j) =
          fun z => zeroSlice p z * (![z 0, z 1, z 2, 0] : Fin 4 → ℝ) j := by
        funext z; simp [zeroSlice]
      rw [h]; exact hp.mul (hcoord j)

private lemma hasDerivAt_zeroSlice (Q : MvPolynomial (Fin 4) ℝ) (x : Base) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => zeroSlice Q (x + s • FubiniJets.basis i))
      (zeroSlice (pderiv (Fin.castSucc i) Q) x) 0 := by
  have hline : ∀ l : Fin 3, HasDerivAt (fun s : ℝ => (x + s • FubiniJets.basis i) l)
      (FubiniJets.basis i l) 0 := by
    intro l
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (FubiniJets.basis i l)).const_add (x l)
  have hz : ∀ l : Fin 4, HasDerivAt (fun s : ℝ => (![(x + s • FubiniJets.basis i) 0,
      (x + s • FubiniJets.basis i) 1, (x + s • FubiniJets.basis i) 2, 0] : Fin 4 → ℝ) l)
      ((![FubiniJets.basis i 0, FubiniJets.basis i 1, FubiniJets.basis i 2, 0] : Fin 4 → ℝ) l)
      0 := by
    intro l
    fin_cases l
    · exact hline 0
    · exact hline 1
    · exact hline 2
    · exact hasDerivAt_const _ _
  have h : HasDerivAt (fun s : ℝ => zeroSlice Q (x + s • FubiniJets.basis i)) _ 0 :=
    hasDerivAt_eval_curve Q (fun s => ![(x + s • FubiniJets.basis i) 0,
      (x + s • FubiniJets.basis i) 1, (x + s • FubiniJets.basis i) 2, 0]) _ 0 hz
  convert h using 1
  rw [Fin.sum_univ_four]
  simp only [zero_smul, add_zero, zeroSlice]
  fin_cases i <;> simp [FubiniJets.basis]

private lemma jet_zeroSlice_succ {n : ℕ} (α : Fin n → Fin 3) {Q R : MvPolynomial (Fin 4) ℝ}
    (h : ∀ y, FubiniJets.jet (zeroSlice Q) n α y = zeroSlice R y) (i : Fin 3) (x : Base) :
    FubiniJets.jet (zeroSlice Q) (n + 1) (Fin.cons i α) x =
      zeroSlice (pderiv (Fin.castSucc i) R) x := by
  have h1 := FubiniJets.hasDerivAt_coordinate_jet isOpen_univ
    ((contDiff_zeroSlice Q (n := ((n + 1 : ℕ) : WithTop ℕ∞))).contDiffOn) le_rfl α x
    (mem_univ x) i
  have hfun : (fun s : ℝ => FubiniJets.jet (zeroSlice Q) n α (x + s • FubiniJets.basis i)) =
      fun s => zeroSlice R (x + s • FubiniJets.basis i) := funext fun s => h _
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_zeroSlice R x i)

private lemma jet_zeroSlice_one (Q : MvPolynomial (Fin 4) ℝ) (k : Fin 3) (y : Base) :
    FubiniJets.jet (zeroSlice Q) 1 ![k] y = zeroSlice (pderiv (Fin.castSucc k) Q) y :=
  jet_zeroSlice_succ ![] (fun y => by simp [FubiniJets.jet]) k y

private lemma jet_zeroSlice_two (Q : MvPolynomial (Fin 4) ℝ) (j k : Fin 3) (y : Base) :
    FubiniJets.jet (zeroSlice Q) 2 ![j, k] y =
      zeroSlice (pderiv (Fin.castSucc j) (pderiv (Fin.castSucc k) Q)) y :=
  jet_zeroSlice_succ ![k] (jet_zeroSlice_one Q k) j y

private lemma jet_zeroSlice_three (Q : MvPolynomial (Fin 4) ℝ) (i j k : Fin 3) (y : Base) :
    FubiniJets.jet (zeroSlice Q) 3 ![i, j, k] y =
      zeroSlice (pderiv (Fin.castSucc i) (pderiv (Fin.castSucc j) (pderiv (Fin.castSucc k) Q))) y :=
  jet_zeroSlice_succ ![j, k] (jet_zeroSlice_two Q j k) i y

/-- Jets of order at least two of the normalized graph `(f - c₀ - L) / s0` are those of `f`
divided by `s0`. -/
private lemma iteratedFDeriv_normalized_graph {f : Base → ℝ} (c₀ s0 : ℝ) (L : Base →L[ℝ] ℝ)
    {x : Base} {n : ℕ} (hn : 2 ≤ n) (hf : ContDiffAt ℝ n f x) :
    iteratedFDeriv ℝ n (fun y => (f y - c₀ - L y) / s0) x = s0⁻¹ • iteratedFDeriv ℝ n f x := by
  have hL : iteratedFDeriv ℝ n (⇑L) x = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv]
    have hfd : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
    rw [hfd, iteratedFDeriv_const_of_ne (by omega)]
    simp
  have hc : iteratedFDeriv ℝ n (fun _ : Base => c₀) x = 0 := by
    rw [iteratedFDeriv_const_of_ne (by omega)]; rfl
  have heq : (fun y => (f y - c₀ - L y) / s0) = s0⁻¹ • ((f - fun _ => c₀) - ⇑L) := by
    funext y; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hcd : ContDiffAt ℝ n (fun _ : Base => c₀) x := contDiffAt_const
  have hLd : ContDiffAt ℝ n (⇑L) x := L.contDiff.contDiffAt
  have h1 : ContDiffAt ℝ n (f - fun _ => c₀) x := hf.sub hcd
  have h2 : ContDiffAt ℝ n ((f - fun _ => c₀) - ⇑L) x := h1.sub hLd
  rw [heq, iteratedFDeriv_const_smul_apply h2, iteratedFDeriv_sub_apply h1 hLd,
    iteratedFDeriv_sub_apply hf hcd, hL, hc, sub_zero, sub_zero]

/-- **The cleared numerator at one event.** -/
theorem event_numerator_bound (hR : DenseJet.SheetRemezAssertion) (d : ℕ) :
    ∃ (Kt Ct Cq : ℝ) (Jc : ℕ), 0 < Kt ∧ 1 ≤ Ct ∧ 0 < Cq ∧ 1 ≤ Jc ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ 2 * (d + 1) →
      U.totalDegree ≤ 2 * (d + 1) → V.totalDegree ≤ 2 * (d + 1) → W.totalDegree ≤ 2 * (d + 1) →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr Jr : ℕ}, DenseJetBound Dr Jr → HasRealExtension Dr f →
      ∀ (A b hδ s0 εown Mz : ℝ), 2 ≤ A → 0 ≤ b → 0 ≤ hδ → 0 < s0 → 0 ≤ εown → 0 ≤ Mz →
      (∀ ε : ℝ, s0 < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ (c₀ : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ Vc a : ℝ}
        {Bδ Cδ : MvPolynomial (Fin 3) ℝ},
      S0.totalDegree ≤ 2 → P0.totalDegree ≤ d → (∀ m, |P0.coeff m| ≤ Mz) →
      2 ≤ A₁ → 0 < εfit → 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹ → εfit * A₁ ^ 19 ≤ A * b →
      (∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
        eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
        a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
        2 * a * w + eval (fun i => z i) Bδ) →
      ∀ (u : Base) (p y : Fin 7 → Base) (α β γ : Fin 7 → ℝ),
      u ∈ closedBall (0 : Base) 1 →
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      (∀ i, CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc A 1 hδ u (p i)) →
      (∀ i, ‖y i‖ ≤ 1 ∧ ‖u - y i‖ ≤ hδ ∧
        ∀ t ∈ Icc (-1 : ℝ) 1,
          |Pf P0 (y i + t • ((8 * A)⁻¹ • p i)) - (α i + β i * t + γ i * t ^ 2)| ≤ εown) →
      -- the seven Hessian tests of the normalized graph
      (∀ i, |iteratedFDeriv ℝ 2 (fun x => (f x - c₀ - L x) / s0) u (fun _ => p i)| ≤
        (Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0) ∧
      -- the numerator, potential route
      (∀ i j k, |ConicTensor.cleared (hessian (fun x => (f x - c₀ - L x) / s0) u)
          (cubic (Pf P0) u) i j k| / s0 ≤
        A ^ Jc * ((A ^ Jr) ^ 3 * (Cq * A ^ 3 * εown + Cq * Mz * A ^ 3 * hδ) +
          Cq * Mz * (A ^ Jr) ^ 2 * ((Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0)) / s0) ∧
      -- the numerator, graph route
      (∀ i j k, |ConicTensor.cleared (hessian (fun x => (f x - c₀ - L x) / s0) u)
          (cubic (Pf P0) u) i j k| / s0 ≤
        |2 * a * f u + eval (fun i => u i) Bδ| * A ^ Jc *
          (2 * (A ^ Jr) ^ 3 * ((Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0))) := by
  obtain ⟨K, C, hK, hC, htests⟩ := graph_tests_at_point hR (2 * (d + 1))
  obtain ⟨Jc, hJc, hcleared⟩ := pointwise_potential_cleared_bound
  obtain ⟨C₁, hC₁, hnorm⟩ := cubic_norm_le d
  obtain ⟨C₂, hC₂, hfit⟩ := cubic_test_of_quadratic_fit d
  obtain ⟨C₃, hC₃, htransfer⟩ := cubic_test_transfer d
  refine ⟨K, C, C₁ + 512 * C₂ + C₃, Jc, hK, hC, by positivity, hJc, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr Jr hjet hext A b hδ s0 εown Mz
    hA hb hhδ hs0 hεown hMz happrox c₀ L S0 P0 Sc εfit A₁ σ Vc a Bδ Cδ hS0 hP0 hP0c hA₁ hεfit
    hsmall hband hroot hSeq hSd u p y α β γ hu hp hdet hwit hfits
  -- the point and the smoothness of the branch
  have hA0 : 0 ≤ A := by linarith
  have hu1 : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hu4 : u ∈ ball (0 : Base) 4 := by
    rw [mem_ball, dist_zero_right]; linarith
  have hu2 : u ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hsmooth : ContDiffOn ℝ ∞ f (ball 0 4) := hext.contDiffOn
  have hfAt : ∀ n : ℕ, ContDiffAt ℝ n f u := fun n =>
    (hsmooth.contDiffAt (isOpen_ball.mem_nhds hu4)).of_le (by exact_mod_cast le_top)
  -- the normalized graph
  set g : Base → ℝ := fun x => (f x - c₀ - L x) / s0 with hg
  set ηq : ℝ := (K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0 with hηq
  have hgD : ∀ n : ℕ, 2 ≤ n → iteratedFDeriv ℝ n g u = s0⁻¹ • iteratedFDeriv ℝ n f u :=
    fun n hn => iteratedFDeriv_normalized_graph c₀ s0 L hn (hfAt n)
  have hg6 : ContDiffOn ℝ 6 g (ball 0 4) :=
    (((hsmooth.sub contDiffOn_const).sub L.contDiff.contDiffOn).div_const s0).of_le (by simp)
  -- the graph tests of the branch along the seven directions
  have htest : ∀ i, |iteratedFDeriv ℝ 2 f u (fun _ => p i)| ≤
        K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ ∧
      |iteratedFDeriv ℝ 3 f u (fun _ => p i)| ≤ K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ := by
    intro i
    have h := htests Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hext A b 1 hδ s0
      hA hb one_pos le_rfl hhδ hs0.le happrox hA₁ hεfit hsmall hband hroot hSeq hSd u (p i) hu
      (hp i).2 (hwit i)
    simpa only [Real.one_rpow, mul_one] using h
  have hgtest : ∀ n, 2 ≤ n → ∀ i, |iteratedFDeriv ℝ n g u (fun _ => p i)| =
      s0⁻¹ * |iteratedFDeriv ℝ n f u (fun _ => p i)| := by
    intro n hn i
    rw [hgD n hn, smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hs0)]
  have hq2 : ∀ i, |iteratedFDeriv ℝ 2 g u (fun _ => p i)| ≤ ηq := by
    intro i
    rw [hgtest 2 le_rfl i, hηq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (htest i).1 (inv_nonneg.mpr hs0.le)
  have hq3 : ∀ i, |iteratedFDeriv ℝ 3 g u (fun _ => p i)| ≤ ηq := by
    intro i
    rw [hgtest 3 (by norm_num) i, hηq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (htest i).2 (inv_nonneg.mpr hs0.le)
  -- the jet norms of the normalized graph
  have hgnorm : ∀ n, 2 ≤ n → n ≤ 6 → ‖iteratedFDeriv ℝ n g u‖ ≤ A ^ Jr := by
    intro n hn2 hn6
    rw [hgD n hn2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have h := jet_le_of_affine_scale hjet hA hext hs0.le happrox hn2 hn6 hu2
    calc s0⁻¹ * ‖iteratedFDeriv ℝ n f u‖ ≤ s0⁻¹ * (A ^ Jr * s0) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs0.le)
      _ = A ^ Jr := by field_simp
  have hηq0 : 0 ≤ ηq := by positivity
  have hMH : 0 ≤ A ^ Jr := pow_nonneg hA0 _
  refine ⟨hq2, ?_, ?_⟩
  · -- the potential route: cubic tests of the potential from its fits, moved to `u`
    have hCq1 : C₁ ≤ C₁ + 512 * C₂ + C₃ := by linarith
    have hCq2 : 512 * C₂ ≤ C₁ + 512 * C₂ + C₃ := by linarith
    have hCq3 : C₃ ≤ C₁ + 512 * C₂ + C₃ := by linarith
    have hP3norm : ‖iteratedFDeriv ℝ 3 (Pf P0) u‖ ≤ (C₁ + 512 * C₂ + C₃) * Mz := by
      have h := hnorm P0 Mz 1 u hP0 hMz le_rfl hP0c hu1 3 (by norm_num)
      rw [one_pow, mul_one] at h
      exact h.trans (mul_le_mul_of_nonneg_right hCq1 hMz)
    have hP3test : ∀ i, |iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i)| ≤
        (C₁ + 512 * C₂ + C₃) * A ^ 3 * εown + (C₁ + 512 * C₂ + C₃) * Mz * A ^ 3 * hδ := by
      intro i
      obtain ⟨hyi, huyi, hfiti⟩ := hfits i
      have h1 := hfit P0 (y i) ((8 * A)⁻¹ • p i) (α i) (β i) (γ i) εown hP0 hεown hfiti
      have h8 : (8 * A) ≠ 0 := by positivity
      have hhom : iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i) = (8 * A) ^ 3 *
          iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => (8 * A)⁻¹ • p i) := by
        have hp' : (fun _ : Fin 3 => p i) =
            fun j : Fin 3 => (fun _ => 8 * A) j • (fun _ => (8 * A)⁻¹ • p i) j := by
          funext j
          simp only [smul_smul, mul_inv_cancel₀ h8, one_smul]
        rw [hp', ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      have h2 : |iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i)| ≤
          512 * C₂ * A ^ 3 * εown := by
        rw [hhom, abs_mul, abs_of_pos (by positivity)]
        calc (8 * A) ^ 3 * |iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => (8 * A)⁻¹ • p i)|
            ≤ (8 * A) ^ 3 * (C₂ * εown) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 512 * C₂ * A ^ 3 * εown := by ring
      have h3 := htransfer P0 Mz 1 u (y i) (p i) hP0 hMz le_rfl hP0c hu1 hyi
      rw [one_pow, mul_one] at h3
      have h4 : C₃ * Mz * ‖u - y i‖ * ‖p i‖ ^ 3 ≤ C₃ * Mz * hδ * A ^ 3 := by
        have hpi : ‖p i‖ ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hp i).2 3
        have hCM : 0 ≤ C₃ * Mz := by positivity
        calc C₃ * Mz * ‖u - y i‖ * ‖p i‖ ^ 3 ≤ C₃ * Mz * hδ * ‖p i‖ ^ 3 := by
              gcongr
          _ ≤ C₃ * Mz * hδ * A ^ 3 := by gcongr
      have h5 : |iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i)| ≤
          512 * C₂ * A ^ 3 * εown + C₃ * Mz * hδ * A ^ 3 := by
        have h6 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i))
          (iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i))
        linarith
      have hA3 : 0 ≤ A ^ 3 := by positivity
      have e1 : 512 * C₂ * A ^ 3 * εown ≤ (C₁ + 512 * C₂ + C₃) * A ^ 3 * εown :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCq2 hA3) hεown
      have e2 : C₃ * Mz * hδ * A ^ 3 ≤ (C₁ + 512 * C₂ + C₃) * Mz * A ^ 3 * hδ := by
        have hMAh : 0 ≤ Mz * A ^ 3 * hδ := by positivity
        calc C₃ * Mz * hδ * A ^ 3 = C₃ * (Mz * A ^ 3 * hδ) := by ring
          _ ≤ (C₁ + 512 * C₂ + C₃) * (Mz * A ^ 3 * hδ) := mul_le_mul_of_nonneg_right hCq3 hMAh
          _ = (C₁ + 512 * C₂ + C₃) * Mz * A ^ 3 * hδ := by ring
      linarith
    have hηc : 0 ≤ (C₁ + 512 * C₂ + C₃) * A ^ 3 * εown +
        (C₁ + 512 * C₂ + C₃) * Mz * A ^ 3 * hδ := by positivity
    have hMF : 0 ≤ (C₁ + 512 * C₂ + C₃) * Mz := by positivity
    have hP6 : ContDiffOn ℝ 6 (Pf P0) (ball 0 4) := (contDiff_Pf P0).contDiffOn
    intro i j k
    have h := hcleared A (A ^ Jr) ((C₁ + 512 * C₂ + C₃) * Mz) ηq
      ((C₁ + 512 * C₂ + C₃) * A ^ 3 * εown + (C₁ + 512 * C₂ + C₃) * Mz * A ^ 3 * hδ) hA hMH
      hMF hηq0 hηc p g (Pf P0) (ball 0 4) isOpen_ball hg6 hP6 u hu4 hp hdet
      (hgnorm 2 le_rfl (by norm_num)) hP3norm hq2 hP3test i j k
    exact div_le_div_of_nonneg_right h hs0.le
  · -- the graph route: the implicit identity `Pf P0 = a f² + Bδ f + S0(·, 0)`
    have hbz : (fun z : Base => eval (fun i => z i) Bδ) = zeroSlice (pderiv 3 S0) := by
      funext z
      have h := hSd z 0
      simp only [mul_zero, zero_add] at h
      exact h.symm
    have heq : ∀ z ∈ ball (0 : Base) 4, Pf P0 z =
        a * (f z * f z) + (fun z : Base => eval (fun i => z i) Bδ) z * f z + zeroSlice S0 z := by
      intro z hz
      have h0 := hSeq z 0
      have hr := (hroot z hz).1
      show eval (fun i => z i) P0 =
        a * (f z * f z) + eval (fun i => z i) Bδ * f z + eval ![z 0, z 1, z 2, 0] S0
      linear_combination -h0 - hr
    have hf3 : ContDiffOn ℝ 3 f (ball 0 4) := hsmooth.of_le (by simp)
    have hb3 : ContDiffOn ℝ 3 (fun z : Base => eval (fun i => z i) Bδ) (ball 0 4) := by
      rw [hbz]; exact (contDiff_zeroSlice _).contDiffOn
    have hc3 : ContDiffOn ℝ 3 (zeroSlice S0) (ball 0 4) := (contDiff_zeroSlice _).contDiffOn
    have hB2 : ∀ i j, FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 2 ![i, j] u = 0 := by
      intro i j
      rw [hbz, jet_zeroSlice_two, pderiv_three_eq_zero S0 hS0]
      simp [zeroSlice]
    have hB3 : ∀ i j k,
        FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 3 ![i, j, k] u = 0 := by
      intro i j k
      rw [hbz, jet_zeroSlice_three, pderiv_three_eq_zero S0 hS0, map_zero]
      simp [zeroSlice]
    have hC3 : ∀ i j k, FubiniJets.jet (zeroSlice S0) 3 ![i, j, k] u = 0 := by
      intro i j k
      rw [jet_zeroSlice_three, pderiv_three_eq_zero S0 hS0]
      simp [zeroSlice]
    have himpl := implicit_cubic_identity isOpen_ball hf3 hb3 hc3 a heq hu4 hB2 hB3 hC3
    -- the Hessian and the cubic of `f` are `s0` times those of `g`
    have hHf : hessian f u = s0 • hessian g u := by
      ext i j
      simp only [hessian, FubiniJets.jet, Matrix.smul_apply, smul_eq_mul, hgD 2 le_rfl,
        smul_apply]
      field_simp
    have hcubf : ∀ i j k, cubic f u i j k = s0 * cubic g u i j k := by
      intro i j k
      simp only [cubic, FubiniJets.jet, hgD 3 (by norm_num), smul_apply, smul_eq_mul]
      field_simp
    set Fw : ℝ := 2 * a * f u + eval (fun i => u i) Bδ with hFw
    have himp : ∀ i j k, cubic (Pf P0) u i j k = (Fw * s0) * cubic g u i j k +
        fubiniCubic (hessian g u) (fun l => s0 * (2 * a * FubiniJets.jet f 1 ![l] u +
          FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 1 ![l] u)) i j k := by
      intro i j k
      have h := himpl i j k
      simp only at h
      rw [show cubic (Pf P0) u i j k = FubiniJets.jet (Pf P0) 3 ![i, j, k] u from rfl, h,
        hcubf, hHf]
      simp only [fubiniCubic, Matrix.smul_apply, smul_eq_mul, hFw]
      ring
    have hcl : ∀ i j k, ConicTensor.cleared (hessian g u) (cubic (Pf P0) u) i j k =
        (Fw * s0) * ConicTensor.cleared (hessian g u) (cubic g u) i j k :=
      ConicTensor.cleared_of_implicit_identity (hessian g u)
        (hessian_symmetric isOpen_ball hg6 hu4) (cubic g u) (cubic (Pf P0) u) _ (Fw * s0) himp
    intro i j k
    have hX := hcleared A (A ^ Jr) (A ^ Jr) ηq ηq hA hMH hMH hηq0 hηq0 p g g (ball 0 4)
      isOpen_ball hg6 hg6 u hu4 hp hdet (hgnorm 2 le_rfl (by norm_num))
      (hgnorm 3 (by norm_num) (by norm_num)) hq2 hq3 i j k
    have hX' : |ConicTensor.cleared (hessian g u) (cubic g u) i j k| ≤
        A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq) := by
      calc _ ≤ A ^ Jc * ((A ^ Jr) ^ 3 * ηq + A ^ Jr * (A ^ Jr) ^ 2 * ηq) := hX
        _ = A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq) := by ring
    rw [hcl i j k, abs_mul, abs_mul, abs_of_pos hs0]
    calc |Fw| * s0 * |ConicTensor.cleared (hessian g u) (cubic g u) i j k| / s0
        = |Fw| * |ConicTensor.cleared (hessian g u) (cubic g u) i j k| := by
          field_simp
      _ ≤ |Fw| * (A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq)) :=
          mul_le_mul_of_nonneg_left hX' (abs_nonneg _)
      _ = |Fw| * A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq) := by ring



/-- **The graph cubic error at one event.** As `event_numerator_bound`, with the potential's
cubic tests given directly at the seven anchors (instead of fits along the tubes) and a lower
bound `m` on the hidden derivative `Fw = 2 a f + Bδ` at `u`; the conclusions bound the graph's
own cleared cubic error `clearedCubicError g u = cleared (D²g u) (D³g u)`, through the potential
(first) or directly (second). -/
theorem event_cleared_bound (hR : DenseJet.SheetRemezAssertion) (d : ℕ) :
    ∃ (Kt Cq : ℝ) (Jc : ℕ), 0 < Kt ∧ 0 < Cq ∧ 1 ≤ Jc ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ 2 * (d + 1) →
      U.totalDegree ≤ 2 * (d + 1) → V.totalDegree ≤ 2 * (d + 1) → W.totalDegree ≤ 2 * (d + 1) →
      ∀ (sq F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (sq z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * sq z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      (∀ y ∈ closedBall (0 : Base) 1, eval (fun i => (DenseJet.realSlice y) i) W ≠ 0) →
      ∀ {Dr Jr : ℕ}, DenseJetBound Dr Jr → HasRealExtension Dr f →
      ∀ (A b hδ s0 εc Mz m : ℝ), 2 ≤ A → 0 ≤ b → 0 ≤ hδ → 0 < s0 → 0 ≤ εc → 0 ≤ Mz → 0 < m →
      (∀ ε : ℝ, s0 < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ (c₀ : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {Sc : Poly} {εfit A₁ σ Vc a : ℝ}
        {Bδ Cδ : MvPolynomial (Fin 3) ℝ},
      S0.totalDegree ≤ 2 → P0.totalDegree ≤ d → (∀ m, |P0.coeff m| ≤ Mz) →
      2 ≤ A₁ → 0 < εfit → 4 * |a| * εfit ≤ (2 * A₁ ^ 2)⁻¹ → εfit * A₁ ^ 19 ≤ A * b →
      (∀ z ∈ ball (0 : Base) 4, a * (f z) ^ 2 + eval (fun i => z i) Bδ * f z +
        eval (fun i => z i) Cδ = 0 ∧ 0 < (2 * a * f z + eval (fun i => z i) Bδ) * σ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] S0 - eval (fun i => z i) P0 =
        a * w ^ 2 + eval (fun i => z i) Bδ * w + eval (fun i => z i) Cδ) →
      (∀ (z : Base) (w : ℝ), eval ![z 0, z 1, z 2, w] (pderiv 3 S0) =
        2 * a * w + eval (fun i => z i) Bδ) →
      ∀ (u : Base) (p y : Fin 7 → Base),
      u ∈ closedBall (0 : Base) 1 →
      m ≤ |2 * a * f u + eval (fun i => u i) Bδ| →
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      (∀ i, CertifiedTubeWitness S0 P0 Sc εfit A₁ σ Vc A 1 hδ u (p i)) →
      (∀ i, ‖y i‖ ≤ 1 ∧ ‖u - y i‖ ≤ hδ ∧
        |iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i)| ≤ εc) →
      -- the seven Hessian tests of the normalized graph
      (∀ i, |iteratedFDeriv ℝ 2 (fun x => (f x - c₀ - L x) / s0) u (fun _ => p i)| ≤
        (Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0) ∧
      -- the graph's cleared cubic error, through the potential
      (∀ i j k, |FubiniHessian.clearedCubicError (fun x => (f x - c₀ - L x) / s0) u i j k| ≤
        A ^ Jc * ((A ^ Jr) ^ 3 * (εc + Cq * Mz * A ^ 3 * hδ) +
          Cq * Mz * (A ^ Jr) ^ 2 * ((Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0)) /
          (s0 * m)) ∧
      -- the graph's cleared cubic error, directly
      (∀ i j k, |FubiniHessian.clearedCubicError (fun x => (f x - c₀ - L x) / s0) u i j k| ≤
        A ^ Jc * (2 * (A ^ Jr) ^ 3 * ((Kt * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0))) := by
  obtain ⟨K, C, hK, hC, htests⟩ := graph_tests_at_point hR (2 * (d + 1))
  obtain ⟨Jc, hJc, hcleared⟩ := pointwise_potential_cleared_bound
  obtain ⟨C₁, hC₁, hnorm⟩ := cubic_norm_le d
  obtain ⟨C₃, hC₃, htransfer⟩ := cubic_test_transfer d
  refine ⟨K, C₁ + C₃, Jc, hK, by positivity, hJc, ?_⟩
  intro Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne Dr Jr hjet hext A b hδ s0 εc Mz m
    hA hb hhδ hs0 hεc hMz hm happrox c₀ L S0 P0 Sc εfit A₁ σ Vc a Bδ Cδ hS0 hP0 hP0c hA₁ hεfit
    hsmall hband hroot hSeq hSd u p y hu hFwm hp hdet hwit hanch
  -- the point and the smoothness of the branch
  have hA0 : 0 ≤ A := by linarith
  have hu1 : ‖u‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hu4 : u ∈ ball (0 : Base) 4 := by
    rw [mem_ball, dist_zero_right]; linarith
  have hu2 : u ∈ closedBall (0 : Base) 2 := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hsmooth : ContDiffOn ℝ ∞ f (ball 0 4) := hext.contDiffOn
  have hfAt : ∀ n : ℕ, ContDiffAt ℝ n f u := fun n =>
    (hsmooth.contDiffAt (isOpen_ball.mem_nhds hu4)).of_le (by exact_mod_cast le_top)
  -- the normalized graph
  set g : Base → ℝ := fun x => (f x - c₀ - L x) / s0 with hg
  set ηq : ℝ := (K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ) / s0 with hηq
  have hgD : ∀ n : ℕ, 2 ≤ n → iteratedFDeriv ℝ n g u = s0⁻¹ • iteratedFDeriv ℝ n f u :=
    fun n hn => iteratedFDeriv_normalized_graph c₀ s0 L hn (hfAt n)
  have hg6 : ContDiffOn ℝ 6 g (ball 0 4) :=
    (((hsmooth.sub contDiffOn_const).sub L.contDiff.contDiffOn).div_const s0).of_le (by simp)
  -- the graph tests of the branch along the seven directions
  have htest : ∀ i, |iteratedFDeriv ℝ 2 f u (fun _ => p i)| ≤
        K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ ∧
      |iteratedFDeriv ℝ 3 f u (fun _ => p i)| ≤ K * A ^ 25 * b + A ^ Jr * s0 * A ^ 9 * hδ := by
    intro i
    have h := htests Δ U V W hΔ hU hV hW sq F f hsq hpres hF hmatch hWne hjet hext A b 1 hδ s0
      hA hb one_pos le_rfl hhδ hs0.le happrox hA₁ hεfit hsmall hband hroot hSeq hSd u (p i) hu
      (hp i).2 (hwit i)
    simpa only [Real.one_rpow, mul_one] using h
  have hgtest : ∀ n, 2 ≤ n → ∀ i, |iteratedFDeriv ℝ n g u (fun _ => p i)| =
      s0⁻¹ * |iteratedFDeriv ℝ n f u (fun _ => p i)| := by
    intro n hn i
    rw [hgD n hn, smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hs0)]
  have hq2 : ∀ i, |iteratedFDeriv ℝ 2 g u (fun _ => p i)| ≤ ηq := by
    intro i
    rw [hgtest 2 le_rfl i, hηq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (htest i).1 (inv_nonneg.mpr hs0.le)
  have hq3 : ∀ i, |iteratedFDeriv ℝ 3 g u (fun _ => p i)| ≤ ηq := by
    intro i
    rw [hgtest 3 (by norm_num) i, hηq, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (htest i).2 (inv_nonneg.mpr hs0.le)
  -- the jet norms of the normalized graph
  have hgnorm : ∀ n, 2 ≤ n → n ≤ 6 → ‖iteratedFDeriv ℝ n g u‖ ≤ A ^ Jr := by
    intro n hn2 hn6
    rw [hgD n hn2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
    have h := jet_le_of_affine_scale hjet hA hext hs0.le happrox hn2 hn6 hu2
    calc s0⁻¹ * ‖iteratedFDeriv ℝ n f u‖ ≤ s0⁻¹ * (A ^ Jr * s0) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs0.le)
      _ = A ^ Jr := by field_simp
  have hηq0 : 0 ≤ ηq := by positivity
  have hMH : 0 ≤ A ^ Jr := pow_nonneg hA0 _
  -- the graph's own cleared cubic error, directly from its tests
  have hdirect : ∀ i j k, |FubiniHessian.clearedCubicError g u i j k| ≤
      A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq) := by
    intro i j k
    have hX := hcleared A (A ^ Jr) (A ^ Jr) ηq ηq hA hMH hMH hηq0 hηq0 p g g (ball 0 4)
      isOpen_ball hg6 hg6 u hu4 hp hdet (hgnorm 2 le_rfl (by norm_num))
      (hgnorm 3 (by norm_num) (by norm_num)) hq2 hq3 i j k
    calc |FubiniHessian.clearedCubicError g u i j k|
        ≤ A ^ Jc * ((A ^ Jr) ^ 3 * ηq + A ^ Jr * (A ^ Jr) ^ 2 * ηq) := hX
      _ = A ^ Jc * (2 * (A ^ Jr) ^ 3 * ηq) := by ring
  refine ⟨hq2, ?_, hdirect⟩
  -- the potential route: the implicit identity `Pf P0 = a f² + Bδ f + S0(·, 0)`
  have hbz : (fun z : Base => eval (fun i => z i) Bδ) = zeroSlice (pderiv 3 S0) := by
    funext z
    have h := hSd z 0
    simp only [mul_zero, zero_add] at h
    exact h.symm
  have heq : ∀ z ∈ ball (0 : Base) 4, Pf P0 z =
      a * (f z * f z) + (fun z : Base => eval (fun i => z i) Bδ) z * f z + zeroSlice S0 z := by
    intro z hz
    have h0 := hSeq z 0
    have hr := (hroot z hz).1
    show eval (fun i => z i) P0 =
      a * (f z * f z) + eval (fun i => z i) Bδ * f z + eval ![z 0, z 1, z 2, 0] S0
    linear_combination -h0 - hr
  have hf3 : ContDiffOn ℝ 3 f (ball 0 4) := hsmooth.of_le (by simp)
  have hb3 : ContDiffOn ℝ 3 (fun z : Base => eval (fun i => z i) Bδ) (ball 0 4) := by
    rw [hbz]; exact (contDiff_zeroSlice _).contDiffOn
  have hc3 : ContDiffOn ℝ 3 (zeroSlice S0) (ball 0 4) := (contDiff_zeroSlice _).contDiffOn
  have hB2 : ∀ i j, FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 2 ![i, j] u = 0 := by
    intro i j
    rw [hbz, jet_zeroSlice_two, pderiv_three_eq_zero S0 hS0]
    simp [zeroSlice]
  have hB3 : ∀ i j k,
      FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 3 ![i, j, k] u = 0 := by
    intro i j k
    rw [hbz, jet_zeroSlice_three, pderiv_three_eq_zero S0 hS0, map_zero]
    simp [zeroSlice]
  have hC3 : ∀ i j k, FubiniJets.jet (zeroSlice S0) 3 ![i, j, k] u = 0 := by
    intro i j k
    rw [jet_zeroSlice_three, pderiv_three_eq_zero S0 hS0]
    simp [zeroSlice]
  have himpl := implicit_cubic_identity isOpen_ball hf3 hb3 hc3 a heq hu4 hB2 hB3 hC3
  -- the Hessian and the cubic of `f` are `s0` times those of `g`
  have hHf : hessian f u = s0 • hessian g u := by
    ext i j
    simp only [hessian, FubiniJets.jet, Matrix.smul_apply, smul_eq_mul, hgD 2 le_rfl,
      smul_apply]
    field_simp
  have hcubf : ∀ i j k, cubic f u i j k = s0 * cubic g u i j k := by
    intro i j k
    simp only [cubic, FubiniJets.jet, hgD 3 (by norm_num), smul_apply, smul_eq_mul]
    field_simp
  set Fw : ℝ := 2 * a * f u + eval (fun i => u i) Bδ with hFw
  have himp : ∀ i j k, cubic (Pf P0) u i j k = (Fw * s0) * cubic g u i j k +
      fubiniCubic (hessian g u) (fun l => s0 * (2 * a * FubiniJets.jet f 1 ![l] u +
        FubiniJets.jet (fun z : Base => eval (fun i => z i) Bδ) 1 ![l] u)) i j k := by
    intro i j k
    have h := himpl i j k
    simp only at h
    rw [show cubic (Pf P0) u i j k = FubiniJets.jet (Pf P0) 3 ![i, j, k] u from rfl, h,
      hcubf, hHf]
    simp only [fubiniCubic, Matrix.smul_apply, smul_eq_mul, hFw]
    ring
  have hcl : ∀ i j k, ConicTensor.cleared (hessian g u) (cubic (Pf P0) u) i j k =
      (Fw * s0) * FubiniHessian.clearedCubicError g u i j k :=
    ConicTensor.cleared_of_implicit_identity (hessian g u)
      (hessian_symmetric isOpen_ball hg6 hu4) (cubic g u) (cubic (Pf P0) u) _ (Fw * s0) himp
  -- the potential's third derivative at `u`, and its cubic tests moved from the anchors
  have hCq1 : C₁ ≤ C₁ + C₃ := by linarith
  have hCq3 : C₃ ≤ C₁ + C₃ := by linarith
  have hP3norm : ‖iteratedFDeriv ℝ 3 (Pf P0) u‖ ≤ (C₁ + C₃) * Mz := by
    have h := hnorm P0 Mz 1 u hP0 hMz le_rfl hP0c hu1 3 (by norm_num)
    rw [one_pow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hCq1 hMz)
  have hP3test : ∀ i, |iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i)| ≤
      εc + (C₁ + C₃) * Mz * A ^ 3 * hδ := by
    intro i
    obtain ⟨hyi, huyi, hεi⟩ := hanch i
    have h3 := htransfer P0 Mz 1 u (y i) (p i) hP0 hMz le_rfl hP0c hu1 hyi
    rw [one_pow, mul_one] at h3
    have h4 : C₃ * Mz * ‖u - y i‖ * ‖p i‖ ^ 3 ≤ C₃ * Mz * hδ * A ^ 3 := by
      have hpi : ‖p i‖ ^ 3 ≤ A ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hp i).2 3
      have hCM : 0 ≤ C₃ * Mz := by positivity
      calc C₃ * Mz * ‖u - y i‖ * ‖p i‖ ^ 3 ≤ C₃ * Mz * hδ * ‖p i‖ ^ 3 := by
            gcongr
        _ ≤ C₃ * Mz * hδ * A ^ 3 := by gcongr
    have h5 : |iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i)| ≤ εc + C₃ * Mz * hδ * A ^ 3 := by
      have h6 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ 3 (Pf P0) u (fun _ => p i))
        (iteratedFDeriv ℝ 3 (Pf P0) (y i) (fun _ => p i))
      linarith
    have e2 : C₃ * Mz * hδ * A ^ 3 ≤ (C₁ + C₃) * Mz * A ^ 3 * hδ := by
      have hMAh : 0 ≤ Mz * A ^ 3 * hδ := by positivity
      calc C₃ * Mz * hδ * A ^ 3 = C₃ * (Mz * A ^ 3 * hδ) := by ring
        _ ≤ (C₁ + C₃) * (Mz * A ^ 3 * hδ) := mul_le_mul_of_nonneg_right hCq3 hMAh
        _ = (C₁ + C₃) * Mz * A ^ 3 * hδ := by ring
    linarith
  have hηc : 0 ≤ εc + (C₁ + C₃) * Mz * A ^ 3 * hδ := by positivity
  have hMF : 0 ≤ (C₁ + C₃) * Mz := by positivity
  have hP6 : ContDiffOn ℝ 6 (Pf P0) (ball 0 4) := (contDiff_Pf P0).contDiffOn
  intro i j k
  have hB := hcleared A (A ^ Jr) ((C₁ + C₃) * Mz) ηq (εc + (C₁ + C₃) * Mz * A ^ 3 * hδ) hA hMH
    hMF hηq0 hηc p g (Pf P0) (ball 0 4) isOpen_ball hg6 hP6 u hu4 hp hdet
    (hgnorm 2 le_rfl (by norm_num)) hP3norm hq2 hP3test i j k
  -- divide by `s0 * |Fw| ≥ s0 * m`
  rw [hcl i j k, abs_mul, abs_mul, abs_of_pos hs0] at hB
  rw [le_div_iff₀ (mul_pos hs0 hm)]
  calc |FubiniHessian.clearedCubicError g u i j k| * (s0 * m)
      ≤ |FubiniHessian.clearedCubicError g u i j k| * (s0 * |Fw|) := by
        gcongr
    _ = |Fw| * s0 * |FubiniHessian.clearedCubicError g u i j k| := by ring
    _ ≤ _ := hB

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
