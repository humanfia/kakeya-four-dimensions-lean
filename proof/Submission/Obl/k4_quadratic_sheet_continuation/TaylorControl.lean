import Mathlib

/-!
# Finite Taylor data and a uniform tail estimate
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Metric Filter
open scoped Topology ContDiff

/-- On the half-unit disk a finite jet and an outer circle bound give a
quantitative norm estimate with a geometric error. -/
theorem norm_le_finite_jet_add_geometric_tail
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 2))
    {M V : ℝ} (_hM : 0 ≤ M) (_hV : 0 ≤ V)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 1, ‖g z‖ ≤ M)
    (q : ℕ) (hjet : ∀ j < q, ‖iteratedDeriv j g 0‖ ≤ V)
    {t : ℂ} (ht : ‖t‖ ≤ (1 : ℝ) / 2) :
    ‖g t‖ ≤ (q : ℝ) * V + 2 * M * ((1 : ℝ) / 2) ^ q := by
  let a : ℕ → ℂ := fun j => (j.factorial : ℂ)⁻¹ • t ^ j • iteratedDeriv j g 0
  have hdisc : DiffContOnCl ℂ g (ball 0 1) :=
    (hg.mono (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)))).diffContOnCl
  have hder (j : ℕ) : ‖iteratedDeriv j g 0‖ ≤ (j.factorial : ℝ) * M := by
    simpa using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      j (by norm_num : (0 : ℝ) < 1) hdisc hbound
  have hgeom (j : ℕ) : ‖a j‖ ≤ M * ((1 : ℝ) / 2) ^ j := by
    have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
    dsimp [a]
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    calc
      (j.factorial : ℝ)⁻¹ * (‖t‖ ^ j * ‖iteratedDeriv j g 0‖) ≤
          (j.factorial : ℝ)⁻¹ * (((1 : ℝ) / 2) ^ j * ((j.factorial : ℝ) * M)) := by
        gcongr
        exact hder j
      _ = M * ((1 : ℝ) / 2) ^ j := by field_simp
  have hs : HasSum a (g t) := by
    have htball : t ∈ ball (0 : ℂ) 2 := by
      simp only [mem_ball, dist_zero_right]
      linarith
    simpa only [a, sub_zero] using Complex.hasSum_taylorSeries_on_ball hg htball
  have htail := norm_sub_le_of_geometric_bound_of_hasSum (by norm_num : (1 : ℝ) / 2 < 1)
    hgeom hs q
  have hhead : ‖∑ j ∈ Finset.range q, a j‖ ≤ (q : ℝ) * V := by
    apply (norm_sum_le _ _).trans
    calc
      ∑ j ∈ Finset.range q, ‖a j‖ ≤ ∑ _j ∈ Finset.range q, V := by
        apply Finset.sum_le_sum
        intro j hj
        have hfac : 1 ≤ (j.factorial : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr j.factorial_pos)
        have hfacInv : (j.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hfac
        have htPow : ‖t‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
        dsimp [a]
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
        calc
          (j.factorial : ℝ)⁻¹ * (‖t‖ ^ j * ‖iteratedDeriv j g 0‖) ≤ 1 * (1 * V) := by
            gcongr
            exact hjet j (Finset.mem_range.mp hj)
          _ = V := by ring
      _ = (q : ℝ) * V := by simp
  have htriangle : ‖g t‖ ≤ ‖∑ j ∈ Finset.range q, a j‖ +
      ‖(∑ j ∈ Finset.range q, a j) - g t‖ := by
    have h := norm_add_le (g t - ∑ j ∈ Finset.range q, a j) (∑ j ∈ Finset.range q, a j)
    rw [sub_add_cancel] at h
    simpa only [norm_sub_rev, add_comm] using h
  calc
    ‖g t‖ ≤ ‖∑ j ∈ Finset.range q, a j‖ + ‖(∑ j ∈ Finset.range q, a j) - g t‖ := htriangle
    _ ≤ (q : ℝ) * V + M * ((1 : ℝ) / 2) ^ q / (1 - (1 : ℝ) / 2) := add_le_add hhead htail
    _ = (q : ℝ) * V + 2 * M * ((1 : ℝ) / 2) ^ q := by ring

/-- An affine complex slice has the diagonal Fréchet jet of the original
function. Only smoothness on an open neighborhood is needed. -/
theorem iteratedDeriv_affine_slice
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℂ ∞ f U)
    {a : E} (ha : a ∈ U) (v : E) (j : ℕ) :
    iteratedDeriv j (fun t : ℂ => f (a + t • v)) 0 =
      iteratedFDeriv ℂ j f a (fun _ => v) := by
  let f₀ : E → F := fun z => f (a + z)
  let U₀ : Set E := (fun z : E => a + z) ⁻¹' U
  let L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ v
  have hU₀ : IsOpen U₀ := hU.preimage (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ U₀ := by simpa [U₀] using ha
  have hf₀ : ContDiffOn ℂ ∞ f₀ U₀ :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have hUL : IsOpen (L ⁻¹' U₀) := hU₀.preimage L.continuous
  have h0L : (0 : ℂ) ∈ L ⁻¹' U₀ := by simpa using h0
  have hcomp := L.iteratedFDerivWithin_comp_right hf₀ hU₀.uniqueDiffOn hUL.uniqueDiffOn
    h0L (i := j) (by exact_mod_cast le_top (a := (j : ℕ∞)))
  rw [iteratedFDerivWithin_of_isOpen j hUL h0L,
    iteratedFDerivWithin_of_isOpen j hU₀ (by simpa using h0)] at hcomp
  have htrans : iteratedFDeriv ℂ j f₀ (L 0) = iteratedFDeriv ℂ j f a := by
    simpa only [L, map_zero, add_zero] using iteratedFDeriv_comp_add_left j a (0 : E)
  rw [htrans] at hcomp
  have hdiag := congrArg (fun T => T (fun _ : Fin j => (1 : ℂ))) hcomp
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa only [Function.comp_def, f₀, L,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hdiag

/-- A uniform local norm comparison implies control by a fixed finite jet.
The order and the constant depend only on the comparison constant and the
prescribed minimum order, uniformly for all small radii. -/
theorem finite_jet_control_of_local_norm_comparison
    (B : ℝ) (hB : 0 < B) (s : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, s ≤ q ∧ 0 < C ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
        (f : E → ℂ) (a : E) (r V : ℝ), 0 < r → r ≤ (1 : ℝ) / 2 → 0 ≤ V →
        ContDiffOn ℂ ∞ f (ball a (8 * r)) →
        (∀ K : ℝ, 0 ≤ K → (∀ z ∈ closedBall a r, ‖f z‖ ≤ K) →
          ∀ z ∈ closedBall a (2 * r), ‖f z‖ ≤ B * K) →
        (∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j f a‖ ≤ V) →
        ∀ z ∈ closedBall a r, ‖f z‖ ≤ C * V := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (le_max_left 1 (4 * B))
    (by norm_num : (1 : ℝ) < 2)
  let q := s + n + 1
  have hqpos : 0 < q := by dsimp [q]; omega
  have hBpow : 4 * B ≤ (2 : ℝ) ^ q := by
    calc
      4 * B ≤ max 1 (4 * B) := le_max_right _ _
      _ ≤ 2 ^ (n + 1) := hn'.le
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) (by dsimp [q]; omega)
  have hsmall : 2 * B * ((1 : ℝ) / 2) ^ q ≤ (1 : ℝ) / 2 := by
    have hprod : (2 : ℝ) ^ q * ((1 : ℝ) / 2) ^ q = 1 := by rw [← mul_pow]; norm_num
    have h := mul_le_mul_of_nonneg_right hBpow (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ q)
    nlinarith
  refine ⟨q, 2 * (q : ℝ), by dsimp [q]; omega, by positivity, ?_⟩
  intro E _ _ _ f a r V hr hrhalf hV hf hgrowth hjet
  have hsub : closedBall a r ⊆ ball a (8 * r) := closedBall_subset_ball (by linarith)
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall a r).exists_isMaxOn
    ⟨a, mem_closedBall_self hr.le⟩ (hf.continuousOn.mono hsub).norm
  let S := ‖f p‖
  have hS : 0 ≤ S := norm_nonneg _
  have hinner : ∀ z ∈ closedBall a r, ‖f z‖ ≤ S := by
    intro z hz
    exact hmax hz
  have houter := hgrowth S hS hinner
  have hpoint (z : E) (hz : z ∈ closedBall a r) :
      ‖f z‖ ≤ (q : ℝ) * V + 2 * (B * S) * ((1 : ℝ) / 2) ^ q := by
    let v : E := (2 : ℂ) • (z - a)
    let g : ℂ → ℂ := fun t => f (a + t • v)
    have hv : ‖v‖ ≤ 2 * r := by
      dsimp [v]
      rw [norm_smul]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hz)
        (by norm_num)
    have hv1 : ‖v‖ ≤ 1 := by linarith
    have hmap : MapsTo (fun t : ℂ => a + t • v) (ball 0 2) (ball a (8 * r)) := by
      intro t ht
      simp only [mem_ball, dist_zero_right] at ht
      simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      calc
        ‖t‖ * ‖v‖ ≤ ‖t‖ * (2 * r) := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
        _ < 8 * r := by nlinarith
    have hgd : DifferentiableOn ℂ g (ball 0 2) :=
      (hf.differentiableOn (by simp)).comp (by fun_prop) hmap
    have hgb : ∀ t ∈ sphere (0 : ℂ) 1, ‖g t‖ ≤ B * S := by
      intro t ht
      apply houter
      simp only [mem_sphere, dist_zero_right] at ht
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, ht, one_mul]
      exact hv
    have hgj : ∀ j < q, ‖iteratedDeriv j g 0‖ ≤ V := by
      intro j hj
      rw [iteratedDeriv_affine_slice isOpen_ball hf (mem_ball_self (by positivity)) v j]
      calc
        ‖iteratedFDeriv ℂ j f a (fun _ => v)‖ ≤ ‖iteratedFDeriv ℂ j f a‖ * ‖v‖ ^ j := by
          simpa only [Finset.prod_const, Finset.card_fin] using
            (iteratedFDeriv ℂ j f a).le_opNorm (fun _ => v)
        _ ≤ V * 1 := by
          gcongr
          · exact hjet j (Nat.le_of_lt hj)
          · exact pow_le_one₀ (norm_nonneg _) hv1
        _ = V := mul_one _
    have ht : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) / 2 := by norm_num
    have h := norm_le_finite_jet_add_geometric_tail hgd (mul_nonneg hB.le hS) hV hgb q hgj ht
    simpa [g, v, smul_smul] using h
  have hpbound := hpoint p hp
  have htail : 2 * (B * S) * ((1 : ℝ) / 2) ^ q ≤ S / 2 := by
    have h := mul_le_mul_of_nonneg_right hsmall hS
    nlinarith
  have hSV : S ≤ 2 * (q : ℝ) * V := by
    change S ≤ (q : ℝ) * V + 2 * (B * S) * ((1 : ℝ) / 2) ^ q at hpbound
    linarith
  intro z hz
  exact (hinner z hz).trans hSV

end Submission.Obl.k4_quadratic_sheet_continuation
