/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/RootPartition.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Obl.k4_stable_native_signal_oscillation.ExactRoot

/-!
Adapted from this LOT tree o176,
Submission/Obl/k4_stable_native_signal_oscillation/ExactRoot.lean (accepted).
The accepted algebraic lemmas and partition packaging are imported.
This generalizes the partition assembly to supplied original-law polynomial
control and slab bounds, so continuous base density is not a hypothesis.
-/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh


open MvPolynomial MeasureTheory Set Metric
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

set_option maxHeartbeats 2000000

noncomputable section

def RootPolynomialControl (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    (K : ℝ) (N : ℕ) : Prop :=
  ∀ G : Set (EuclideanSpace ℝ (Fin 4)), (∀ᵐ p ∂μ, p ∈ G) →
    (∀ p ∈ G, ‖erBase p‖ ≤ K) →
    ∀ f : MvPolynomial (Fin 3) ℝ, f.totalDegree ≤ 4 →
    ∀ V : ℝ, 0 ≤ V → (∀ p ∈ G, |eval (fun i => erBase p i) f| ≤ V) →
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K →
      |eval (fun i => x i) f| ≤ K ^ N * V) ∧
    ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
      |eval (fun i => x i) f - eval (fun i => y i) f| ≤ K ^ N * V * ‖x - y‖

def RootSlabControl (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    (K : ℝ) (A c : ℕ) : Prop :=
  ∀ B : MvPolynomial (Fin 3) ℝ, B.totalDegree ≤ 4 →
    ∀ x₀ : EuclideanSpace ℝ (Fin 3), ‖x₀‖ ≤ K →
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ K →
      |eval (fun i => x i) B| ≤ |eval (fun i => x₀ i) B|) →
    0 < |eval (fun i => x₀ i) B| →
    μ (erBase ⁻¹' {x | ‖x‖ ≤ K ∧
        |eval (fun i => x i) B| ≤ |eval (fun i => x₀ i) B| / K ^ c}) ≤
      ENNReal.ofReal ((K ^ A)⁻¹)

/-- Exactly two root groups suffice once the original law supplies the
polynomial bounds and the small-slab bound. -/
theorem exact_root_partition_of_controls (N c A : ℕ) (K : ℝ)
    (P S : MvPolynomial (Fin 4) ℝ) (μ : Measure (EuclideanSpace ℝ (Fin 4)))
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hP : P.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) (hctl : RootPolynomialControl μ K N)
    (hslab : RootSlabControl μ K A c)
    (hae : ∀ᵐ p ∂μ, ‖erBase p‖ ≤ K ∧ eval (fun i => p i) P = 0 ∧
      K⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧
      |eval (fun i => p i) (pderiv 3 P)| ≤ K ∧ |eval (fun i => p i) S| ≤ K) :
    ∃ E : Fin 2 → Set (EuclideanSpace ℝ (Fin 4)),
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
      μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧
      ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
        |eval (fun j => p j) S - eval (fun j => q j) S| ≤
          K ^ (N + c + 10) * ‖erBase p - erBase q‖ := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → K ^ a ≤ K ^ b := fun a b h => pow_le_pow_right₀ hK1 h
  have hcv : ∀ Q : MvPolynomial (Fin 4) ℝ,
      Continuous (fun p : EuclideanSpace ℝ (Fin 4) => eval (fun i => p i) Q) :=
    fun Q => (MvPolynomial.continuous_eval Q).comp (by fun_prop)
  let G : Set (EuclideanSpace ℝ (Fin 4)) := {p | ‖erBase p‖ ≤ K ∧ eval (fun i => p i) P = 0 ∧
    K⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧ |eval (fun i => p i) (pderiv 3 P)| ≤ K ∧
    |eval (fun i => p i) S| ≤ K}
  have hGm : MeasurableSet G := by
    refine (measurableSet_le measurable_erBase.norm measurable_const).inter ?_
    refine (measurableSet_eq_fun (hcv P).measurable measurable_const).inter ?_
    refine (measurableSet_le measurable_const (hcv _).abs.measurable).inter ?_
    exact (measurableSet_le (hcv _).abs.measurable measurable_const).inter
      (measurableSet_le (hcv S).abs.measurable measurable_const)
  have hG : ∀ᵐ p ∂μ, p ∈ G := hae
  have hGball : ∀ p ∈ G, ‖erBase p‖ ≤ K := fun p hp => hp.1
  let u : EuclideanSpace ℝ (Fin 4) → ℝ := fun p => eval (fun i => p i) (pderiv 3 P)
  have hu : Measurable u := (hcv _).measurable
  have hu0 : ∀ p ∈ G, u p ≠ 0 := by
    intro p hp h
    have h1 : K⁻¹ ≤ |u p| := hp.2.2.1
    rw [h, abs_zero] at h1
    exact absurd h1 (not_le.mpr (inv_pos.mpr hK0))
  have hbase3 : ∀ p ∈ G, ‖erBase p‖ ≤ 3 * K := fun p hp => by linarith [hp.1]
  suffices hmain : ∃ (g : EuclideanSpace ℝ (Fin 4) → ℝ) (b L : ℝ), Measurable g ∧
      μ (G ∩ {p | |g p| ≤ b}) ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧ L ≤ K ^ (N + c + 10) ∧
      ∀ p ∈ G, ∀ q ∈ G, b < |g p| → b < |g q| → 0 < u p * u q →
        |eval (fun j => p j) S - eval (fun j => q j) S| ≤ L * ‖erBase p - erBase q‖ by
    obtain ⟨g, b, L, hg, hmass, hL, hlip⟩ := hmain
    obtain ⟨E, hEm, hEd, hEmass, hElip⟩ := er_package μ G hGm hG u hu hu0 g hg b
      (fun p => eval (fun j => p j) S) L _ hmass hlip
    refine ⟨E, hEm, hEd, hEmass, ?_⟩
    intro i p hp q hq
    exact (hElip i p hp q hq).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have htriv : μ (G ∩ {p | |(fun _ : EuclideanSpace ℝ (Fin 4) => (0 : ℝ)) p| ≤ -1}) ≤
      ENNReal.ofReal ((K ^ A)⁻¹) := by
    have h : G ∩ {p | |(fun _ : EuclideanSpace ℝ (Fin 4) => (0 : ℝ)) p| ≤ -1} = ∅ := by
      ext p
      simp only [abs_zero, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro _
      norm_num
    rw [h, measure_empty]
    exact bot_le
  have hKN : 0 ≤ K ^ N := by positivity
  by_cases hκ : curvature P 3 = 0
  · -- a linear hidden test
    have hlin : ∀ p ∈ G, u p = eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ∧
        eval (fun j => erBase p j) (erN0 P S) =
          eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ^ 2 * eval (fun i => p i) S :=
      fun p hp => er_linear_point P S hP hS hκ p hp.2.1
    have hβ := hctl G hG hGball (restrictBase (pderiv 3 P))
      ((er_totalDegree_restrict_deriv P hP).trans (by norm_num)) K hK0.le
      (fun p hp => by rw [← (hlin p hp).1]; exact hp.2.2.2.1)
    have hN0 := hctl G hG hGball (erN0 P S) (erN0_degree P S hP hS) (K ^ 3)
      (by positivity) (fun p hp => by
        rw [(hlin p hp).2, abs_mul, abs_pow, ← (hlin p hp).1]
        calc |u p| ^ 2 * |eval (fun i => p i) S| ≤ K ^ 2 * K :=
              mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hp.2.2.2.1 2) hp.2.2.2.2
                (abs_nonneg _) (by positivity)
          _ = K ^ 3 := by ring)
    refine ⟨fun _ => 0, -1, K ^ 2 * (K ^ N * K ^ 3) + 2 * K ^ 4 * (K ^ N * K),
      measurable_const, htriv, ?_, ?_⟩
    · have h1 : K ^ 2 * (K ^ N * K ^ 3) + 2 * K ^ 4 * (K ^ N * K) = 3 * K ^ (N + 5) := by ring
      rw [h1]
      calc 3 * K ^ (N + 5) ≤ K ^ 2 * K ^ (N + 5) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ = K ^ (N + 7) := by ring
        _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
    · intro p hp q hq _ _ _
      have hβp : K⁻¹ ≤ |eval (fun j => erBase p j) (restrictBase (pderiv 3 P))| := by
        rw [← (hlin p hp).1]; exact hp.2.2.1
      have hβp' : |eval (fun j => erBase p j) (restrictBase (pderiv 3 P))| ≤ K := by
        rw [← (hlin p hp).1]; exact hp.2.2.2.1
      have hβq' : |eval (fun j => erBase q j) (restrictBase (pderiv 3 P))| ≤ K := by
        rw [← (hlin q hq).1]; exact hq.2.2.2.1
      exact er_linear_case_bound hK0 hβp hβp' hβq' (hlin p hp).2 (hlin q hq).2 hq.2.2.2.2
        (hN0.2 _ _ (hbase3 p hp) (hbase3 q hq)) (hβ.2 _ _ (hbase3 p hp) (hbase3 q hq))
        (norm_nonneg _) (by positivity) (by positivity)
  · -- a genuinely quadratic hidden test: two root sheets
    have hpt : ∀ p ∈ G, u p ^ 2 = eval (fun j => erBase p j) (erDisc P) ∧
        eval (fun i => p i) S = eval (fun j => erBase p j) (erM P S) +
          eval (fun j => erBase p j) (erB P S) * u p :=
      fun p hp => er_root_point P S hP hS hκ p hp.2.1
    obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) K).exists_isMaxOn
      (nonempty_closedBall.mpr hK0.le) (er_continuous_eval3 (erB P S)).abs.continuousOn
    set LB := |eval (fun i => x₀ i) (erB P S)| with hLB
    have hx₀K : ‖x₀‖ ≤ K := by simpa [mem_closedBall, dist_zero_right] using hx₀
    have hBle : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ K →
        |eval (fun i => x i) (erB P S)| ≤ LB := fun x hx =>
      hmax (by simpa [mem_closedBall, dist_zero_right] using hx)
    have hLB0 : 0 ≤ LB := abs_nonneg _
    have hMbound : ∀ p ∈ G, |eval (fun j => erBase p j) (erM P S)| ≤ K + LB * K := by
      intro p hp
      have h1 : eval (fun j => erBase p j) (erM P S) =
          eval (fun i => p i) S - eval (fun j => erBase p j) (erB P S) * u p := by
        rw [(hpt p hp).2]; ring
      rw [h1]
      calc _ ≤ |eval (fun i => p i) S| + |eval (fun j => erBase p j) (erB P S) * u p| :=
            abs_sub _ _
        _ ≤ K + LB * K := by
          rw [abs_mul]
          exact add_le_add hp.2.2.2.2
            (mul_le_mul (hBle _ hp.1) hp.2.2.2.1 (abs_nonneg _) hLB0)
    by_cases hsmall : LB ≤ 2 * K ^ (c + 2)
    · -- close branches
      set L₀ := 2 * K ^ (c + 2) with hL₀
      have hL₀0 : 0 ≤ L₀ := by positivity
      have hΔ := hctl G hG hGball (erDisc P) ((erDisc_degree2 P hP).trans (by norm_num))
        (K ^ 2) (by positivity) (fun p hp => by
          rw [← (hpt p hp).1, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hp.2.2.2.1 2)
      have hB := hctl G hG hGball (erB P S)
        ((erB_degree1 P S hP hS).trans (by norm_num)) L₀ hL₀0
        (fun p hp => (hBle _ hp.1).trans hsmall)
      have hM := hctl G hG hGball (erM P S)
        ((erM_degree2 P S hP hS).trans (by norm_num)) (K + L₀ * K) (by positivity)
        (fun p hp => (hMbound p hp).trans (by gcongr))
      refine ⟨fun _ => 0, -1, K ^ N * (K + L₀ * K) + K ^ N * L₀ * K + L₀ * K * (K ^ N * K ^ 2) / 2,
        measurable_const, htriv, ?_, ?_⟩
      · have h1 : K ^ N * (K + L₀ * K) + K ^ N * L₀ * K + L₀ * K * (K ^ N * K ^ 2) / 2 =
            K ^ (N + 1) + 4 * K ^ (N + c + 3) + K ^ (N + c + 5) := by
          rw [hL₀]; ring
        rw [h1]
        have h2 : K ^ (N + 1) ≤ K ^ (N + c + 5) := hpow _ _ (by omega)
        have h3 : 4 * K ^ (N + c + 3) ≤ K ^ (N + c + 5) := by
          have : K ^ (N + c + 5) = K ^ 2 * K ^ (N + c + 3) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        calc K ^ (N + 1) + 4 * K ^ (N + c + 3) + K ^ (N + c + 5) ≤ 3 * K ^ (N + c + 5) := by
              linarith
          _ ≤ K ^ 2 * K ^ (N + c + 5) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
          _ = K ^ (N + c + 7) := by ring
          _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
      · intro p hp q hq _ _ hsign
        have hSp := (hpt p hp).2
        have hSq := (hpt q hq).2
        rw [hSp, hSq]
        have hLD : |u p ^ 2 - u q ^ 2| ≤ K ^ N * K ^ 2 * ‖erBase p - erBase q‖ := by
          rw [(hpt p hp).1, (hpt q hq).1]
          exact hΔ.2 _ _ (hbase3 p hp) (hbase3 q hq)
        have h := er_small_branch_bound hK0 hp.2.2.1 hq.2.2.1 hp.2.2.2.1 hsign
          ((hBle _ hq.1).trans hsmall) (hM.2 _ _ (hbase3 p hp) (hbase3 q hq))
          (hB.2 _ _ (hbase3 p hp) (hbase3 q hq)) hLD (norm_nonneg _) hL₀0 (by positivity)
        convert h using 2
    · -- separated branches: trim a thin slab of the branch coefficient
      push Not at hsmall
      have hLBpos : 0 < LB := lt_of_le_of_lt (by positivity) hsmall
      have hcKpos : 0 < K ^ c := by positivity
      have hN := hctl G hG hGball (erN P S) (erN_degree P S hP hS)
        ((K + 2 * LB * K) * K) (by positivity) (fun p hp => by
          have h1 : eval (fun j => erBase p j) (erN P S) =
              (eval (fun i => p i) S - 2 * (eval (fun j => erBase p j) (erB P S) * u p)) *
                eval (fun i => p i) S := by
            simp only [erN, eval_sub, eval_mul, eval_pow]
            rw [← (hpt p hp).1, (hpt p hp).2]
            ring
          rw [h1, abs_mul]
          apply mul_le_mul _ hp.2.2.2.2 (abs_nonneg _) (by positivity)
          calc _ ≤ |eval (fun i => p i) S| + |2 * (eval (fun j => erBase p j) (erB P S) * u p)| :=
                abs_sub _ _
            _ ≤ K + 2 * LB * K := by
              rw [abs_mul, abs_mul, abs_two]
              have := mul_le_mul (hBle _ hp.1) hp.2.2.2.1 (abs_nonneg _) hLB0
              linarith [hp.2.2.2.2])
      have hM := hctl G hG hGball (erM P S)
        ((erM_degree2 P S hP hS).trans (by norm_num)) (K + LB * K) (by positivity) hMbound
      set ℓ := LB / K ^ (c + 1) with hℓ
      have hℓpos : 0 < ℓ := by positivity
      refine ⟨fun p => eval (fun j => erBase p j) (erB P S), LB / K ^ c,
        (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) / ℓ,
        (er_continuous_eval3 (erB P S)).measurable.comp measurable_erBase, ?_, ?_, ?_⟩
      · calc μ (G ∩ {p | |eval (fun j => erBase p j) (erB P S)| ≤ LB / K ^ c}) ≤
            μ (erBase ⁻¹' {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) (erB P S)| ≤ LB / K ^ c}) := by
              apply measure_mono
              intro p hp
              exact ⟨hp.1.1, hp.2⟩
          _ ≤ ENNReal.ofReal ((K ^ A)⁻¹) :=
              hslab (erB P S) ((erB_degree1 P S hP hS).trans (by norm_num)) x₀ hx₀K
                hBle hLBpos
      · have h1 : (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) / ℓ =
            K ^ (N + c + 1) * (3 * K ^ 2 / LB + 4 * K ^ 2) := by
          rw [hℓ]
          field_simp
          ring
        rw [h1]
        have h2 : 3 * K ^ 2 / LB ≤ K ^ 2 := by
          rw [div_le_iff₀ hLBpos]
          have : 3 ≤ LB := by
            have h4 : (4 : ℝ) ≤ K ^ (c + 2) := by
              calc (4 : ℝ) = 2 ^ 2 := by norm_num
                _ ≤ K ^ 2 := pow_le_pow_left₀ (by norm_num) hK 2
                _ ≤ K ^ (c + 2) := hpow _ _ (by omega)
            linarith
          nlinarith [sq_nonneg K]
        calc K ^ (N + c + 1) * (3 * K ^ 2 / LB + 4 * K ^ 2) ≤ K ^ (N + c + 1) * (5 * K ^ 2) := by
              gcongr; linarith
          _ ≤ K ^ (N + c + 1) * (K ^ 3 * K ^ 2) := by
              gcongr
              nlinarith
          _ = K ^ (N + c + 6) := by ring
          _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
      · intro p hp q hq hbp _ _
        have hSp := (hpt p hp).2
        have hSq := (hpt q hq).2
        have hSpK : |eval (fun j => erBase p j) (erM P S) +
            eval (fun j => erBase p j) (erB P S) * u p| ≤ K := by rw [← hSp]; exact hp.2.2.2.2
        have hSqK : |eval (fun j => erBase q j) (erM P S) +
            eval (fun j => erBase q j) (erB P S) * u q| ≤ K := by rw [← hSq]; exact hq.2.2.2.2
        have hsep : ℓ ≤ 2 * |eval (fun j => erBase p j) (erB P S)| * |u p| - 2 * K := by
          have h1 : LB / K ^ c * K⁻¹ ≤ |eval (fun j => erBase p j) (erB P S)| * |u p| :=
            mul_le_mul hbp.le hp.2.2.1 (by positivity) (abs_nonneg _)
          have h2 : LB / K ^ c * K⁻¹ = ℓ * 1 := by rw [hℓ]; field_simp; ring
          have h3 : 2 * K ≤ ℓ := by
            rw [hℓ, le_div_iff₀ (by positivity)]
            have : 2 * K * K ^ (c + 1) = 2 * K ^ (c + 2) := by ring
            linarith
          nlinarith
        have hLN : |(eval (fun j => erBase p j) (erM P S) ^ 2 -
              eval (fun j => erBase p j) (erB P S) ^ 2 * u p ^ 2) -
            (eval (fun j => erBase q j) (erM P S) ^ 2 -
              eval (fun j => erBase q j) (erB P S) ^ 2 * u q ^ 2)| ≤
            K ^ N * ((K + 2 * LB * K) * K) * ‖erBase p - erBase q‖ := by
          have h := hN.2 _ _ (hbase3 p hp) (hbase3 q hq)
          simp only [erN, eval_sub, eval_mul, eval_pow] at h
          rw [(hpt p hp).1, (hpt q hq).1]
          exact h
        have h := er_separated_branch_bound hK0 hSpK hSqK hsep hℓpos
          (hM.2 _ _ (hbase3 p hp) (hbase3 q hq)) hLN
        rw [hSp, hSq]
        calc _ ≤ (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) *
              ‖erBase p - erBase q‖ / ℓ := h
          _ = _ := by ring

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
