-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/NativeMeshAlgebra.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit 5ad87c691b3258ec246a7cd5750f11134f9c4fab,
   Submission/Obl/k4_finite_projected_horizontal_candidates/NativeMeshAlgebra.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.MeshCalibration
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SharpRootCover
import Submission.Obl.k4_stable_native_signal_oscillation.ExactRoot

/-!
# Algebra of the native sheets

The native signal `S` on the root branches of a quadratic hidden test `F` (accepted o176,
`ExactRoot`): with `β = ∂_w F` on the base, `κ = ∂²_w F`, `Δ = β² - 2 κ γ`,

* `κ ≠ 0`: on the branch with `∂_w F = ± √Δ`, `S = M ± B √Δ`, and the product of the two branch
  values is the base polynomial `N = M² - B² Δ` (`low_branch_value`);
* `κ = 0`: `S = N₀ / β²` (`zero_branch_value`);
* at the critical center `-β/κ`, `S` is the base polynomial `centerSignal F S`.

This file has the pointwise identities, the complex relations satisfied by the corresponding
holomorphic sheets, and `small_branch_bound`: two holomorphic branches with a known product
and a large difference cannot exchange their sizes on a ball.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

/-- The chart bounds of a point `(u, w)` for the hidden test `F` at width `a` and the native
signal `S`. -/
def NChart (K a : ℝ) (F S : MvPolynomial (Fin 4) ℝ) (u : Fin 3 → ℝ) (w : ℝ) : Prop :=
  (∀ i, |u i| ≤ K) ∧ |eval (Fin.snoc u w) F| ≤ K * a ∧
  K⁻¹ ≤ |eval (Fin.snoc u w) (pderiv 3 F)| ∧ |eval (Fin.snoc u w) (pderiv 3 F)| ≤ K ∧
  |curvature F 3| ≤ K / a ∧
  |eval (Fin.snoc u w) S| ≤ K ∧ |eval (Fin.snoc u w) (pderiv 3 S)| ≤ K ∧ |curvature S 3| ≤ K

/-- A native sheet on the complex ball of radius `r` around the real point `c`: holomorphic,
a root of the relation `R`, bounded by `V`, and real on the real points. -/
def SheetOn (R : MvPolynomial (Fin 4) ℂ) (g : EuclideanSpace ℂ (Fin 3) → ℂ)
    (c : EuclideanSpace ℝ (Fin 3)) (r V : ℝ) : Prop :=
  DifferentiableOn ℂ g (ball (emb c) r) ∧
  (∀ z ∈ ball (emb c) r, eval (Fin.snoc (fun i : Fin 3 => z i) (g z)) R = 0) ∧
  (∀ z ∈ ball (emb c) r, ‖g z‖ ≤ V) ∧
  (∀ x : EuclideanSpace ℝ (Fin 3), ‖x - c‖ < r → (g (emb x)).im = 0)

theorem SheetOn.mono {R : MvPolynomial (Fin 4) ℂ} {g : EuclideanSpace ℂ (Fin 3) → ℂ}
    {c : EuclideanSpace ℝ (Fin 3)} {r V V' : ℝ} (h : SheetOn R g c r V) (hV : V ≤ V') :
    SheetOn R g c r V' :=
  ⟨h.1, h.2.1, fun z hz => (h.2.2.1 z hz).trans hV, h.2.2.2⟩

/-- The sign of the hidden derivative selects the branch. -/
def branch (F : MvPolynomial (Fin 4) ℝ) (u : Fin 3 → ℝ) (w : ℝ) : Bool :=
  decide (0 < eval (Fin.snoc u w) (pderiv 3 F))

/-- `±1` from a branch. -/
def bsign (s : Bool) : ℝ := if s then 1 else -1

theorem bsign_sq (s : Bool) : bsign s ^ 2 = 1 := by cases s <;> simp [bsign]

theorem abs_bsign (s : Bool) : |bsign s| = 1 := by cases s <;> simp [bsign]

theorem bsign_branch_pos {F : MvPolynomial (Fin 4) ℝ} {u : Fin 3 → ℝ} {w : ℝ}
    (h : eval (Fin.snoc u w) (pderiv 3 F) ≠ 0) :
    0 < bsign (branch F u w) * eval (Fin.snoc u w) (pderiv 3 F) := by
  unfold bsign branch
  by_cases hp : 0 < eval (Fin.snoc u w) (pderiv 3 F)
  · simp [hp]
  · have hn : eval (Fin.snoc u w) (pderiv 3 F) < 0 := lt_of_le_of_ne (not_lt.mp hp) h
    simp [hp]; linarith

/-! ### Relations -/

theorem eval_snoc_renameMap (P : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3)) (v : ℂ) :
    eval (Fin.snoc (fun i : Fin 3 => z i) v)
      (rename Fin.castSucc (P.map (algebraMap ℝ ℂ)) : MvPolynomial (Fin 4) ℂ) = cev P z := by
  rw [eval_rename]
  have hc : (Fin.snoc (fun i : Fin 3 => z i) v : Fin 4 → ℂ) ∘ Fin.castSucc =
      fun i : Fin 3 => z i := by
    funext i; simp
  rw [hc, eval_map]

theorem eval_snoc_X3 (z : EuclideanSpace ℂ (Fin 3)) (v : ℂ) :
    eval (Fin.snoc (fun i : Fin 3 => z i) v) (X 3 : MvPolynomial (Fin 4) ℂ) = v := by
  rw [eval_X, last_three, Fin.snoc_last]

theorem totalDegree_renameMap_le (P : MvPolynomial (Fin 3) ℝ) :
    (rename Fin.castSucc (P.map (algebraMap ℝ ℂ)) : MvPolynomial (Fin 4) ℂ).totalDegree ≤
      P.totalDegree :=
  (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ P))

/-- `X₃ - G`. -/
def relLin (G : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 - rename Fin.castSucc (G.map (algebraMap ℝ ℂ))

/-- `β² X₃ - N₀`. -/
def relZero (β N₀ : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℂ :=
  rename Fin.castSucc (β.map (algebraMap ℝ ℂ)) ^ 2 * X 3 -
    rename Fin.castSucc (N₀.map (algebraMap ℝ ℂ))

/-- `X₃² - 2 M X₃ + N`. -/
def relQuad (M N : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 ^ 2 - 2 * rename Fin.castSucc (M.map (algebraMap ℝ ℂ)) * X 3 +
    rename Fin.castSucc (N.map (algebraMap ℝ ℂ))

theorem eval_relLin (G : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3)) (v : ℂ) :
    eval (Fin.snoc (fun i : Fin 3 => z i) v) (relLin G) = v - cev G z := by
  simp only [relLin, eval_sub, eval_snoc_renameMap]
  rw [eval_X, last_three, Fin.snoc_last]

theorem eval_relZero (β N₀ : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3)) (v : ℂ) :
    eval (Fin.snoc (fun i : Fin 3 => z i) v) (relZero β N₀) = cev β z ^ 2 * v - cev N₀ z := by
  simp only [relZero, eval_sub, eval_mul, eval_pow, eval_snoc_renameMap]
  rw [eval_X, last_three, Fin.snoc_last]

theorem eval_relQuad (M N : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3)) (v : ℂ) :
    eval (Fin.snoc (fun i : Fin 3 => z i) v) (relQuad M N) = v ^ 2 - 2 * cev M z * v + cev N z := by
  simp only [relQuad, eval_sub, eval_add, eval_mul, eval_pow, eval_snoc_renameMap, eval_ofNat]
  rw [eval_X, last_three, Fin.snoc_last]

theorem relLin_ne_zero (G : MvPolynomial (Fin 3) ℝ) : relLin G ≠ 0 := by
  intro h
  have h1 := eval_relLin G 0 1
  have h0 := eval_relLin G 0 0
  rw [h, map_zero] at h1 h0
  have : (1 : ℂ) = 0 := by linear_combination h0 - h1
  exact one_ne_zero this

theorem relQuad_ne_zero (M N : MvPolynomial (Fin 3) ℝ) : relQuad M N ≠ 0 := by
  intro h
  have h1 := eval_relQuad M N 0 1
  have h0 := eval_relQuad M N 0 0
  have h2 := eval_relQuad M N 0 (-1)
  rw [h, map_zero] at h1 h0 h2
  have : (2 : ℂ) = 0 := by linear_combination -h1 - h2 + 2 * h0
  exact two_ne_zero this

theorem relZero_ne_zero (β N₀ : MvPolynomial (Fin 3) ℝ) (z : EuclideanSpace ℂ (Fin 3))
    (hz : cev β z ≠ 0) : relZero β N₀ ≠ 0 := by
  intro h
  have h1 := eval_relZero β N₀ z 1
  have h0 := eval_relZero β N₀ z 0
  rw [h, map_zero] at h1 h0
  have : cev β z ^ 2 = 0 := by linear_combination h0 - h1
  exact hz (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem relLin_degree {G : MvPolynomial (Fin 3) ℝ} (hG : G.totalDegree ≤ 4) :
    (relLin G).totalDegree ≤ 4 := by
  unfold relLin
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]; norm_num
  · exact (totalDegree_renameMap_le G).trans hG

theorem relZero_degree {β N₀ : MvPolynomial (Fin 3) ℝ} (hβ : β.totalDegree ≤ 1)
    (hN : N₀.totalDegree ≤ 4) : (relZero β N₀).totalDegree ≤ 4 := by
  unfold relZero
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_pow (rename Fin.castSucc (β.map (algebraMap ℝ ℂ)) :
      MvPolynomial (Fin 4) ℂ) 2)
    have h2 := (totalDegree_renameMap_le β).trans hβ
    rw [totalDegree_X]
    nlinarith
  · exact (totalDegree_renameMap_le N₀).trans hN

theorem relQuad_degree {M N : MvPolynomial (Fin 3) ℝ} (hM : M.totalDegree ≤ 2)
    (hN : N.totalDegree ≤ 4) : (relQuad M N).totalDegree ≤ 4 := by
  unfold relQuad
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]; norm_num
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      have h2 : (2 * rename Fin.castSucc (M.map (algebraMap ℝ ℂ)) :
          MvPolynomial (Fin 4) ℂ).totalDegree ≤ 2 := by
        refine (totalDegree_mul _ _).trans ?_
        have : ((2 : MvPolynomial (Fin 4) ℂ)).totalDegree = 0 := by
          rw [show (2 : MvPolynomial (Fin 4) ℂ) = C 2 from rfl, totalDegree_C]
        rw [this, zero_add]
        exact (totalDegree_renameMap_le M).trans hM
      omega
  · exact (totalDegree_renameMap_le N).trans hN

/-! ### Real identities along the hidden direction -/

/-- The hidden quadratic in its base coefficients. -/
theorem quad_eval {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) (u : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc u w) F = eval u (restrictBase F) + eval u (restrictBase (pderiv 3 F)) * w +
      curvature F 3 * w ^ 2 / 2 := by
  have h := eval_snoc_quadratic F hF u w
  rw [← last_three] at h
  exact h

theorem quad_deriv {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2) (u : Fin 3 → ℝ)
    (w : ℝ) :
    eval (Fin.snoc u w) (pderiv 3 F) = eval u (restrictBase (pderiv 3 F)) + curvature F 3 * w := by
  rw [eval_snoc_qFw hF, qa, qb]; ring

/-- Variation of a quadratic signal along the hidden direction. -/
theorem signal_sub_bound {S : MvPolynomial (Fin 4) ℝ} (hS : S.totalDegree ≤ 2) {K : ℝ}
    (u : Fin 3 → ℝ) (w φ : ℝ) (hSw : |eval (Fin.snoc u w) (pderiv 3 S)| ≤ K)
    (hκ' : |curvature S 3| ≤ K) :
    |eval (Fin.snoc u w) S - eval (Fin.snoc u φ) S| ≤ |w - φ| * (K + K * |w - φ|) := by
  rw [quad_eval hS, quad_eval hS]
  rw [quad_deriv hS] at hSw
  set β' := eval u (restrictBase (pderiv 3 S))
  set κ' := curvature S 3
  have hid : (eval u (restrictBase S) + β' * w + κ' * w ^ 2 / 2) -
      (eval u (restrictBase S) + β' * φ + κ' * φ ^ 2 / 2) =
      (w - φ) * (β' + κ' * w) - κ' * (w - φ) ^ 2 / 2 := by ring
  rw [hid]
  calc |(w - φ) * (β' + κ' * w) - κ' * (w - φ) ^ 2 / 2|
      ≤ |(w - φ) * (β' + κ' * w)| + |κ' * (w - φ) ^ 2 / 2| := abs_sub _ _
    _ = |w - φ| * |β' + κ' * w| + |κ'| * |w - φ| ^ 2 / 2 := by
        rw [abs_mul, abs_div, abs_mul, abs_pow]; norm_num
    _ ≤ |w - φ| * K + K * |w - φ| ^ 2 / 2 := by
        gcongr
    _ ≤ |w - φ| * (K + K * |w - φ|) := by
        have h0 : 0 ≤ K := (abs_nonneg _).trans hκ'
        nlinarith [abs_nonneg (w - φ)]

/-- The discriminant at any point of the hidden line. -/
theorem erDisc_eval_point {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (u : Fin 3 → ℝ) (w : ℝ) :
    eval u (erDisc F) = eval (Fin.snoc u w) (pderiv 3 F) ^ 2 -
      2 * curvature F 3 * eval (Fin.snoc u w) F := by
  rw [quad_deriv hF, quad_eval hF]
  simp only [erDisc, eval_sub, eval_pow, eval_mul, eval_C]
  ring

/-- **Exact roots, nonzero curvature** (accepted o176 `er_root_identity`). -/
theorem low_branch_value {F S : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) (hκ : curvature F 3 ≠ 0) (u : Fin 3 → ℝ) (φ : ℝ)
    (hroot : eval (Fin.snoc u φ) F = 0) :
    eval (Fin.snoc u φ) (pderiv 3 F) ^ 2 = eval u (erDisc F) ∧
    eval (Fin.snoc u φ) S =
      eval u (erM F S) + eval u (erB F S) * eval (Fin.snoc u φ) (pderiv 3 F) := by
  rw [quad_eval hF] at hroot
  have hid := er_root_identity (κ' := curvature S 3) (γ' := eval u (restrictBase S))
    (β' := eval u (restrictBase (pderiv 3 S))) hκ hroot
  rw [quad_deriv hF, quad_eval hS]
  simp only [erDisc, erM, erB, eval_sub, eval_add, eval_mul, eval_pow, eval_C]
  refine ⟨hid.1, ?_⟩
  rw [hid.2]
  ring

/-- **Exact roots, zero curvature** (accepted o176 `er_linear_point`). -/
theorem zero_branch_value {F S : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) (hκ : curvature F 3 = 0) (u : Fin 3 → ℝ) (φ : ℝ)
    (hroot : eval (Fin.snoc u φ) F = 0) :
    eval u (erN0 F S) = eval u (restrictBase (pderiv 3 F)) ^ 2 * eval (Fin.snoc u φ) S := by
  rw [quad_eval hF, hκ] at hroot
  rw [quad_eval hS]
  simp only [erN0, eval_sub, eval_add, eval_mul, eval_pow, eval_C]
  set γ := eval u (restrictBase F)
  set β := eval u (restrictBase (pderiv 3 F))
  set β' := eval u (restrictBase (pderiv 3 S))
  linear_combination (-β * β' + curvature S 3 / 2 * (γ - β * φ)) * hroot

/-- The distance to the critical center. -/
theorem center_dist {F : MvPolynomial (Fin 4) ℝ} (hF : F.totalDegree ≤ 2)
    (hκ : curvature F 3 ≠ 0) (u : Fin 3 → ℝ) (w : ℝ) :
    w - eval u (centerPoly F) = eval (Fin.snoc u w) (pderiv 3 F) / curvature F 3 := by
  rw [quad_deriv hF]
  simp only [centerPoly, eval_mul, eval_C, ← last_three]
  field_simp
  ring

theorem eval_centerSignal' (F S : MvPolynomial (Fin 4) ℝ) (u : Fin 3 → ℝ) :
    eval u (centerSignal F S) = eval (Fin.snoc u (eval u (centerPoly F))) S :=
  eval_centerSignal F S u

/-! ### Two branches on a ball -/

/-- Two continuous branches on a ball whose difference is at least `L` and whose product has
size `< L² / 4`: if the first is small (`< L/2`) at one point, it is bounded by `2 V / L`
everywhere on the ball. -/
theorem small_branch_bound {g g' Nf : EuclideanSpace ℂ (Fin 3) → ℂ}
    {c : EuclideanSpace ℂ (Fin 3)} {r L V : ℝ} (hL : 0 < L)
    (hg : ContinuousOn g (ball c r)) (hg' : ContinuousOn g' (ball c r))
    (hprod : ∀ z ∈ ball c r, g z * g' z = Nf z) (hN : ∀ z ∈ ball c r, ‖Nf z‖ ≤ V)
    (hVL : V < L ^ 2 / 4) (hdiff : ∀ z ∈ ball c r, L ≤ ‖g z - g' z‖)
    (z₀ : EuclideanSpace ℂ (Fin 3)) (hz₀ : z₀ ∈ ball c r) (hsmall : ‖g z₀‖ < L / 2) :
    ∀ z ∈ ball c r, ‖g z‖ ≤ 2 * V / L := by
  set U := ball c r ∩ g ⁻¹' ball (0 : ℂ) (L / 2) with hU
  set U' := ball c r ∩ g' ⁻¹' ball (0 : ℂ) (L / 2) with hU'
  have hUo : IsOpen U := hg.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hUo' : IsOpen U' := hg'.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hdisj : Disjoint U U' := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 : ‖g z‖ < L / 2 := by simpa using hz.2
    have h2 : ‖g' z‖ < L / 2 := by simpa using hz'.2
    have h3 := hdiff z hz.1
    have h4 : ‖g z - g' z‖ ≤ ‖g z‖ + ‖g' z‖ := norm_sub_le _ _
    linarith
  have hcover : ball c r ⊆ U ∪ U' := by
    intro z hz
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have h1 : L / 2 ≤ ‖g z‖ := by
      by_contra h; exact hnot.1 ⟨hz, by simpa using (not_le.mp h)⟩
    have h2 : L / 2 ≤ ‖g' z‖ := by
      by_contra h; exact hnot.2 ⟨hz, by simpa using (not_le.mp h)⟩
    have h3 : ‖Nf z‖ = ‖g z‖ * ‖g' z‖ := by rw [← hprod z hz, norm_mul]
    have h4 : L / 2 * (L / 2) ≤ ‖g z‖ * ‖g' z‖ :=
      mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    have h5 := hN z hz
    nlinarith
  have hne : (ball c r ∩ U).Nonempty := ⟨z₀, hz₀, hz₀, by simpa using hsmall⟩
  have hsub : ball c r ⊆ U :=
    (convex_ball c r).isPreconnected.subset_left_of_subset_union hUo hUo' hdisj hcover hne
  intro z hz
  have hzU := hsub hz
  have hzU' : z ∉ U' := fun h => Set.disjoint_left.mp hdisj hzU h
  have hbig : L / 2 ≤ ‖g' z‖ := by
    by_contra h; exact hzU' ⟨hz, by simpa using (not_le.mp h)⟩
  have hpos : 0 < ‖g' z‖ := by linarith
  have h3 : ‖g z‖ * ‖g' z‖ = ‖Nf z‖ := by rw [← hprod z hz, norm_mul]
  have h5 := hN z hz
  rw [le_div_iff₀ hL]
  have : ‖g z‖ * (L / 2) ≤ ‖g z‖ * ‖g' z‖ := mul_le_mul_of_nonneg_left hbig (norm_nonneg _)
  nlinarith

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
