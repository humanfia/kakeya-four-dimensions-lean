/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.PathSimulation
import Mathlib.Tactic.Positivity

open Set MeasureTheory
open scoped Interval

namespace Submission.Lib.K4PolynomialNorming

/-- A shared-state base error and a velocity-bin error give the actual
one-leg base error, for a signed time increment of magnitude at most one. -/
theorem affine_switch_base_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b c u v : E) (δ η τ : ℝ) (hδ : |δ| ≤ 1)
    (hshared : ‖b-c‖ ≤ η) (hvelocity : ‖u-v‖ ≤ τ) :
    ‖(b+δ • u)-(c+δ • v)‖ ≤ η+τ := by
  have hτ : 0 ≤ τ := (norm_nonneg _).trans hvelocity
  calc
    _ = ‖(b-c)+δ • (u-v)‖ := by congr 1; module
    _ ≤ ‖b-c‖+‖δ • (u-v)‖ := norm_add_le _ _
    _ = ‖b-c‖+|δ| * ‖u-v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ η+τ := add_le_add hshared
      ((mul_le_mul_of_nonneg_left hvelocity (abs_nonneg _)).trans
        (mul_le_of_le_one_left hτ hδ))

/-- A whole-leg field fit on the actual new line survives the shared-state
and velocity-bin errors. Signed increments need no orientation choice. -/
theorem affine_switch_height_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E → ℝ) (b c u v : E) (hF : Continuous (F v)) (znew zold speed δ ε η τ ζ M L : ℝ)
    (hδ : |δ| ≤ 1) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hshared : ‖b-c‖ ≤ η) (hvelocity : ‖u-v‖ ≤ τ)
    (hheight : |znew-zold| ≤ ζ)
    (hfit : ∀ s ∈ uIcc (0:ℝ) δ, |speed-F u (b+s • u)| ≤ ε)
    (hvel : ∀ s ∈ uIcc (0:ℝ) δ,
      |F u (b+s • u)-F v (b+s • u)| ≤ M*‖u-v‖)
    (hLip : ∀ s ∈ uIcc (0:ℝ) δ,
      |F v (b+s • u)-F v (c+s • v)| ≤ L*‖(b+s • u)-(c+s • v)‖) :
    |(znew+δ*speed)-zold-∫ s in (0:ℝ)..δ, F v (c+s • v)| ≤
      ζ+ε+M*τ+L*(η+τ) := by
  have hbound : ∀ s ∈ uIcc (0:ℝ) δ,
      |speed-F v (c+s • v)| ≤ ε+M*τ+L*(η+τ) := by
    intro s hs
    have hsδ : |s| ≤ 1 :=
      (show |s| ≤ |δ| by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs).trans hδ
    have hb := affine_switch_base_error b c u v s η τ hsδ hshared hvelocity
    calc
      _ = |(speed-F u (b+s • u)) +
          (F u (b+s • u)-F v (b+s • u)) +
          (F v (b+s • u)-F v (c+s • v))| := by congr 1; ring
      _ ≤ |speed-F u (b+s • u)| + |F u (b+s • u)-F v (b+s • u)| +
          |F v (b+s • u)-F v (c+s • v)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ ε+M*τ+L*(η+τ) := add_le_add
        (add_le_add (hfit s hs) ((hvel s hs).trans
          (mul_le_mul_of_nonneg_left hvelocity hM)))
        ((hLip s hs).trans (mul_le_mul_of_nonneg_left hb hL))
  have hi : IntervalIntegrable (fun s : ℝ => F v (c+s • v)) volume 0 δ :=
    (hF.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  have hdiff : |δ*speed-∫ s in (0:ℝ)..δ, F v (c+s • v)| ≤
      ε+M*τ+L*(η+τ) := by
    have heq : δ*speed-∫ s in (0:ℝ)..δ, F v (c+s • v) =
        ∫ s in (0:ℝ)..δ, (speed-F v (c+s • v)) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) hi]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    rw [heq]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := δ) (C := ε+M*τ+L*(η+τ))
      (f := fun s => speed-F v (c+s • v))
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s (uIoc_subset_uIcc hs))
    simp only [Real.norm_eq_abs, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hδ)
  calc
    _ = |(znew-zold)+(δ*speed-∫ s in (0:ℝ)..δ, F v (c+s • v))| := by congr 1; ring
    _ ≤ |znew-zold|+|δ*speed-∫ s in (0:ℝ)..δ, F v (c+s • v)| := abs_add_le _ _
    _ ≤ ζ+(ε+M*τ+L*(η+τ)) := add_le_add hheight hdiff
    _ = _ := by ring

/-- Whole-leg fits for the actual refreshed lines supply both the base
and height simulation bounds for the full signed path. -/
theorem affine_switched_path_simulation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (F : E → E → ℝ) (b c u v : ℕ → E)
    (z znew speed δ : ℕ → ℝ) (U : Set E) (ε η τ ζ M L : ℝ)
    (hF : ∀ k, Continuous (F (v k)))
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : ∀ k < N, |δ k| ≤ 1)
    (hbaseeq : ∀ k < N, c (k+1) = b k + δ k • u k)
    (hheighteq : ∀ k < N, z (k+1) = znew k + δ k * speed k)
    (hshared : ∀ k < N, ‖b k-c k‖ ≤ η)
    (hvelocity : ∀ k < N, ‖u k-v k‖ ≤ τ)
    (hheight : ∀ k < N, |znew k-z k| ≤ ζ)
    (hfit : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      |speed k-F (u k) (b k+s • u k)| ≤ ε)
    (hvel : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      |F (u k) (b k+s • u k)-F (v k) (b k+s • u k)| ≤ M*‖u k-v k‖)
    (hU : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      b k+s • u k ∈ U ∧ c k+s • v k ∈ U ∧
        pathBasePrefix (c 0) δ v k+s • v k ∈ U)
    (hLip : ∀ k < N, ∀ x ∈ U, ∀ y ∈ U,
      |F (v k) x-F (v k) y| ≤ L*‖x-y‖) :
    (∀ k ≤ N, ‖c k-pathBasePrefix (c 0) δ v k‖ ≤ (k:ℝ)*(η+τ)) ∧
      |z N-z 0-∑ k ∈ Finset.range N,
        ∫ s in (0:ℝ)..δ k, F (v k) (pathBasePrefix (c 0) δ v k+s • v k)| ≤
        (N:ℝ)*(ζ+ε+M*τ+L*(η+τ)+L*((N:ℝ)*(η+τ))) := by
  have hb : ∀ k < N, ‖c (k+1)-(c k+δ k • v k)‖ ≤ η+τ := by
    intro k hk
    rw [hbaseeq k hk]
    exact affine_switch_base_error (b k) (c k) (u k) (v k) (δ k) η τ
      (hδ k hk) (hshared k hk) (hvelocity k hk)
  refine ⟨pathBasePrefix_error N c δ v (η+τ) hb, ?_⟩
  apply noisy_path_height_error N c δ v z (fun k => F (v k)) hF U
    (ζ+ε+M*τ+L*(η+τ)) (η+τ) L (add_nonneg hη hτ) hL hδ hb
  · intro k hk
    rw [hheighteq k hk]
    exact affine_switch_height_error F (b k) (c k) (u k) (v k) (hF k)
      (znew k) (z k) (speed k) (δ k) ε η τ ζ M L (hδ k hk) hε hη hτ hM hL
      (hshared k hk) (hvelocity k hk) (hheight k hk) (hfit k hk) (hvel k hk)
      (fun s hs => hLip k hk _ (hU k hk s hs).1 _ (hU k hk s hs).2.1)
  · exact fun k hk s hs => (hU k hk s hs).2
  · exact hLip

/-- Coordinate field bounds control the error from replacing the actual
velocity by its observed code, in the product norm. -/
theorem finite_field_velocity_difference_le {ι : Type*} [Fintype ι]
    (u v f : ι → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |(∑ i, u i*f i)-(∑ i, v i*f i)| ≤
      (Fintype.card ι:ℝ)*B*‖u-v‖ := by
  have heq : (∑ i, u i*f i)-(∑ i, v i*f i) = ∑ i, (u i-v i)*f i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |(u i-v i)*f i| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i => (u i-v i)*f i)
    _ ≤ ∑ _i : ι, ‖u-v‖*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hi : |u i-v i| ≤ ‖u-v‖ := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (u-v) i
      exact mul_le_mul hi (hf i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Coordinate Lipschitz bounds control the field contraction along each
bounded observed direction. -/
theorem finite_field_spatial_difference_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E]
    (f : ι → E → ℝ) (v : ι → ℝ) (x y : E) (U A : ℝ)
    (hU : 0 ≤ U) (hv : ∀ i, |v i| ≤ U)
    (hf : ∀ i, |f i x-f i y| ≤ A*‖x-y‖) :
    |(∑ i, v i*f i x)-(∑ i, v i*f i y)| ≤
      ((Fintype.card ι:ℝ)*U*A)*‖x-y‖ := by
  have heq : (∑ i, v i*f i x)-(∑ i, v i*f i y) = ∑ i, v i*(f i x-f i y) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |v i*(f i x-f i y)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le Finset.univ (fun i => v i*(f i x-f i y))
    _ ≤ ∑ _i : ι, U*(A*‖x-y‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hv i) (hf i) (abs_nonneg _) hU
    _ = _ := by simp; ring

/-- Whole-line confinement also controls the actual coarse paths and
ideal paths on the slightly enlarged region needed by the Lipschitz bound. -/
theorem affine_switched_path_region {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (b c u v : ℕ → E) (δ : ℕ → ℝ) (η τ R : ℝ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hδ : ∀ k < N, |δ k| ≤ 1)
    (hbaseeq : ∀ k < N, c (k+1) = b k+δ k • u k)
    (hshared : ∀ k < N, ‖b k-c k‖ ≤ η)
    (hvelocity : ∀ k < N, ‖u k-v k‖ ≤ τ)
    (hactual : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k), ‖b k+s • u k‖ ≤ R) :
    ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      b k+s • u k ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)) ∧
      c k+s • v k ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)) ∧
      pathBasePrefix (c 0) δ v k+s • v k ∈
        Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)) := by
  have hE : 0 ≤ η+τ := add_nonneg hη hτ
  have hb : ∀ k < N, ‖c (k+1)-(c k+δ k • v k)‖ ≤ η+τ := by
    intro k hk
    rw [hbaseeq k hk]
    exact affine_switch_base_error (b k) (c k) (u k) (v k) (δ k) η τ
      (hδ k hk) (hshared k hk) (hvelocity k hk)
  intro k hk s hs
  have hsδ : |s| ≤ 1 :=
    (show |s| ≤ |δ k| by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs).trans
      (hδ k hk)
  have hbs := affine_switch_base_error (b k) (c k) (u k) (v k) s η τ hsδ
    (hshared k hk) (hvelocity k hk)
  have hc : ‖c k+s • v k‖ ≤ R+(η+τ) := by
    calc
      _ = ‖(b k+s • u k)+((c k+s • v k)-(b k+s • u k))‖ := by congr 1; abel
      _ ≤ ‖b k+s • u k‖+‖(c k+s • v k)-(b k+s • u k)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hactual k hk s hs) (by simpa only [norm_sub_rev] using hbs)
  have hkN : (k:ℝ) ≤ N := by exact_mod_cast hk.le
  have hprefix := pathBasePrefix_error N c δ v (η+τ) hb k hk.le
  have hideal : ‖pathBasePrefix (c 0) δ v k+s • v k‖ ≤ R+((N:ℝ)+1)*(η+τ) := by
    have hsmall : ‖pathBasePrefix (c 0) δ v k+s • v k‖ ≤ R+(η+τ)+(k:ℝ)*(η+τ) := by
      calc
        _ = ‖(c k+s • v k)+(pathBasePrefix (c 0) δ v k-c k)‖ := by congr 1; abel
        _ ≤ ‖c k+s • v k‖+‖pathBasePrefix (c 0) δ v k-c k‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hc (by simpa only [norm_sub_rev] using hprefix)
    nlinarith
  have hR : R ≤ R+((N:ℝ)+1)*(η+τ) :=
    le_add_of_nonneg_right (mul_nonneg (by positivity) hE)
  have hc' : ‖c k+s • v k‖ ≤ R+((N:ℝ)+1)*(η+τ) := by
    have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    And.intro ((hactual k hk s hs).trans hR) (And.intro hc' hideal)

/-- A fitted variable height derivative gives the same signed-leg error
as a constant derivative, using its exact height integral. -/
theorem fitted_switched_height_increment_error {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E → ℝ) (b c u v : E) (hF : Continuous (F v))
    (g : ℝ → ℝ) (hg : Continuous g)
    (znext znew zold δ ε η τ ζ M L : ℝ)
    (hδ : |δ| ≤ 1) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hshared : ‖b-c‖ ≤ η) (hvelocity : ‖u-v‖ ≤ τ)
    (hheight : |znew-zold| ≤ ζ)
    (hincrement : znext-znew = ∫ s in (0:ℝ)..δ, g s)
    (hfit : ∀ s ∈ uIcc (0:ℝ) δ, |g s-F u (b+s • u)| ≤ ε)
    (hvel : ∀ s ∈ uIcc (0:ℝ) δ,
      |F u (b+s • u)-F v (b+s • u)| ≤ M*‖u-v‖)
    (hLip : ∀ s ∈ uIcc (0:ℝ) δ,
      |F v (b+s • u)-F v (c+s • v)| ≤ L*‖(b+s • u)-(c+s • v)‖) :
    |znext-zold-∫ s in (0:ℝ)..δ, F v (c+s • v)| ≤ ζ+ε+M*τ+L*(η+τ) := by
  have hbound : ∀ s ∈ uIcc (0:ℝ) δ,
      |g s-F v (c+s • v)| ≤ ε+M*τ+L*(η+τ) := by
    intro s hs
    have hsδ : |s| ≤ 1 :=
      (show |s| ≤ |δ| by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs).trans hδ
    have hb := affine_switch_base_error b c u v s η τ hsδ hshared hvelocity
    calc
      _ = |(g s-F u (b+s • u))+(F u (b+s • u)-F v (b+s • u))+
          (F v (b+s • u)-F v (c+s • v))| := by congr 1; ring
      _ ≤ |g s-F u (b+s • u)|+|F u (b+s • u)-F v (b+s • u)|+
          |F v (b+s • u)-F v (c+s • v)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add
        (add_le_add (hfit s hs) ((hvel s hs).trans (mul_le_mul_of_nonneg_left hvelocity hM)))
        ((hLip s hs).trans (mul_le_mul_of_nonneg_left hb hL))
  have hi : IntervalIntegrable (fun s : ℝ => F v (c+s • v)) volume 0 δ :=
    (hF.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  have hdiff : |(znext-znew)-∫ s in (0:ℝ)..δ, F v (c+s • v)| ≤ ε+M*τ+L*(η+τ) := by
    rw [hincrement,← intervalIntegral.integral_sub (hg.intervalIntegrable _ _) hi]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := δ) (C := ε+M*τ+L*(η+τ))
      (f := fun s => g s-F v (c+s • v))
      (fun s hs => by simpa only [Real.norm_eq_abs] using hbound s (uIoc_subset_uIcc hs))
    simp only [Real.norm_eq_abs,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hδ)
  calc
    _ = |(znew-zold)+((znext-znew)-∫ s in (0:ℝ)..δ, F v (c+s • v))| := by congr 1; ring
    _ ≤ |znew-zold|+|(znext-znew)-∫ s in (0:ℝ)..δ, F v (c+s • v)| := abs_add_le _ _
    _ ≤ ζ+(ε+M*τ+L*(η+τ)) := add_le_add hheight hdiff
    _ = _ := by ring

/-- Signed path simulation with the actual variable derivatives of the
assigned height trajectories, before identifying the endpoint polynomial. -/
theorem switched_path_simulation_of_fitted_height_integrals {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (F : E → E → ℝ) (b c u v : ℕ → E)
    (z znew δ : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (U : Set E) (ε η τ ζ M L : ℝ)
    (hF : ∀ k, Continuous (F (v k))) (hg : ∀ k, Continuous (g k))
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : ∀ k < N, |δ k| ≤ 1)
    (hbaseeq : ∀ k < N, c (k+1) = b k+δ k • u k)
    (hheighteq : ∀ k < N, z (k+1)-znew k = ∫ s in (0:ℝ)..δ k, g k s)
    (hshared : ∀ k < N, ‖b k-c k‖ ≤ η)
    (hvelocity : ∀ k < N, ‖u k-v k‖ ≤ τ)
    (hheight : ∀ k < N, |znew k-z k| ≤ ζ)
    (hfit : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k), |g k s-F (u k) (b k+s • u k)| ≤ ε)
    (hvel : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      |F (u k) (b k+s • u k)-F (v k) (b k+s • u k)| ≤ M*‖u k-v k‖)
    (hU : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k),
      b k+s • u k ∈ U ∧ c k+s • v k ∈ U ∧ pathBasePrefix (c 0) δ v k+s • v k ∈ U)
    (hLip : ∀ k < N, ∀ x ∈ U, ∀ y ∈ U, |F (v k) x-F (v k) y| ≤ L*‖x-y‖) :
    (∀ k ≤ N, ‖c k-pathBasePrefix (c 0) δ v k‖ ≤ (k:ℝ)*(η+τ)) ∧
      |z N-z 0-∑ k ∈ Finset.range N,
        ∫ s in (0:ℝ)..δ k, F (v k) (pathBasePrefix (c 0) δ v k+s • v k)| ≤
        (N:ℝ)*(ζ+ε+M*τ+L*(η+τ)+L*((N:ℝ)*(η+τ))) := by
  have hb : ∀ k < N, ‖c (k+1)-(c k+δ k • v k)‖ ≤ η+τ := by
    intro k hk
    rw [hbaseeq k hk]
    exact affine_switch_base_error (b k) (c k) (u k) (v k) (δ k) η τ
      (hδ k hk) (hshared k hk) (hvelocity k hk)
  refine ⟨pathBasePrefix_error N c δ v (η+τ) hb,?_⟩
  apply noisy_path_height_error N c δ v z (fun k => F (v k)) hF U
    (ζ+ε+M*τ+L*(η+τ)) (η+τ) L (add_nonneg hη hτ) hL hδ hb
  · intro k hk
    exact fitted_switched_height_increment_error F (b k) (c k) (u k) (v k) (hF k)
      (g k) (hg k) (z (k+1)) (znew k) (z k) (δ k) ε η τ ζ M L (hδ k hk)
      hε hη hτ hM hL (hshared k hk) (hvelocity k hk) (hheight k hk) (hheighteq k hk)
      (hfit k hk) (hvel k hk)
      (fun s hs => hLip k hk _ (hU k hk s hs).1 _ (hU k hk s hs).2.1)
  · exact fun k hk s hs => (hU k hk s hs).2
  · exact hLip

end Submission.Lib.K4PolynomialNorming
