/-
Adapted from: here:o106
Original proofs by session x0352, commit e08f59f4.
Owned source: Submission/Obl/k4_isotropic_path_improvement/LocalListPacking.lean.
-/

import Submission.Lib.K4VelocityStrips.StripPacking

/-!
Second-moment packing when each point has only a short list of colors.
The colors may depend on the point and may range over an infinite type.
-/

namespace Submission.Lib.K4PolynomialFiberLists

open MeasureTheory Set

noncomputable section

theorem finite_color_collision_bound {ι β : Type*} [DecidableEq β] (S : Finset ι) (code : ι → β)
    (K : ℝ) (hK : ((S.image code).card : ℝ) ≤ K) :
    (S.card : ℝ) ^ 2 ≤ K * ∑ i ∈ S, ∑ j ∈ S,
      (if code i = code j then (1 : ℝ) else 0) := by
  classical
  let B := S.image code
  let a : β → ℝ := fun b => ((S.filter fun i => code i = b).card : ℝ)
  have hfirst : (S.card : ℝ) = ∑ b ∈ B, a b := by
    dsimp only [B, a]
    exact_mod_cast Finset.card_eq_sum_card_image code S
  have ha (b : β) : a b = ∑ i ∈ S, (if code i = b then (1 : ℝ) else 0) := by
    simp [a]
  have hsquares : (∑ b ∈ B, a b ^ 2) = ∑ i ∈ S, ∑ j ∈ S,
      (if code i = code j then (1 : ℝ) else 0) := by
    calc
      _ = ∑ b ∈ B, ∑ i ∈ S, if code i = b then a b else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        rw [pow_two, ha b, Finset.sum_mul]
        simp only [ite_mul, one_mul, zero_mul]
      _ = ∑ i ∈ S, a (code i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        have hiB : code i ∈ B := Finset.mem_image_of_mem code hi
        simp [hiB]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ha]
        apply Finset.sum_congr rfl
        intro j _
        simp only [eq_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [← hfirst, hsquares] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hK (by positivity))

private theorem integral_double_indicator {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (μ : Measure X) [IsFiniteMeasure μ]
    (E : ι → κ → Set X) (hE : ∀ i j, MeasurableSet (E i j)) :
    (∫ x, ∑ i, ∑ j, (E i j).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      ∑ i, ∑ j, μ.real (E i j) := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_const (1 : ℝ)).indicator (hE i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_const (1 : ℝ)).indicator (hE i j))]
  exact Finset.sum_congr rfl (fun j _ => integral_indicator_one (hE i j))

open Classical in
/-- At most K occurring colors at each point replace the ordinary
second moment by K times the same-color collision moment. -/
theorem local_list_second_moment {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq β]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : ι → Set X)
    (hE : ∀ i, MeasurableSet (E i)) (code : ι → X → β)
    (heq : ∀ i j, MeasurableSet {x | code i x = code j x})
    (K : ℝ) (hlocal : ∀ x,
      (((Finset.univ.filter fun i => x ∈ E i).image (fun i => code i x)).card : ℝ) ≤ K) :
    (∑ i, μ.real (E i)) ^ 2 ≤
      K * ∑ i, ∑ j, μ.real {x | x ∈ E i ∧ x ∈ E j ∧ code i x = code j x} := by
  classical
  let C : ι → ι → Set X := fun i j =>
    {x | x ∈ E i ∧ x ∈ E j ∧ code i x = code j x}
  have hC (i j : ι) : MeasurableSet (C i j) := (hE i).inter ((hE j).inter (heq i j))
  have hpoint (x : X) :
      (∑ i, ∑ j, (E i ∩ E j).indicator (fun _ => (1 : ℝ)) x) ≤
        K * ∑ i, ∑ j, (C i j).indicator (fun _ => (1 : ℝ)) x := by
    let S := Finset.univ.filter fun i => x ∈ E i
    have hcard : (S.card : ℝ) = ∑ i, (E i).indicator (fun _ => (1 : ℝ)) x := by
      simp [S, Set.indicator_apply]
    have hleft : (S.card : ℝ) ^ 2 =
        ∑ i, ∑ j, (E i ∩ E j).indicator (fun _ => (1 : ℝ)) x := by
      rw [hcard, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : x ∈ E i <;> by_cases hj : x ∈ E j <;> simp [hi, hj]
    have hright : (∑ i ∈ S, ∑ j ∈ S,
        if code i x = code j x then (1 : ℝ) else 0) =
        ∑ i, ∑ j, (C i j).indicator (fun _ => (1 : ℝ)) x := by
      simp only [S, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x ∈ E i
      · simp only [hi, ite_true]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : x ∈ E j <;> simp [C, hi, hj, Set.indicator_apply]
      · simp [C, hi]
    have h := finite_color_collision_bound S (fun i => code i x) K (hlocal x)
    rwa [hleft, hright] at h
  have hu : Integrable (fun x => ∑ i, ∑ j,
      (E i ∩ E j).indicator (fun _ => (1 : ℝ)) x) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_const (1 : ℝ)).indicator ((hE i).inter (hE j))
  have hc : Integrable (fun x => ∑ i, ∑ j,
      (C i j).indicator (fun _ => (1 : ℝ)) x) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_const (1 : ℝ)).indicator (hC i j)
  have hcomp := integral_mono hu (hc.const_mul K) hpoint
  rw [integral_const_mul, integral_double_indicator μ _ (fun i j => (hE i).inter (hE j)),
    integral_double_indicator μ C hC] at hcomp
  exact (Submission.Lib.K4VelocityStrips.event_mass_second_moment μ E hE).trans hcomp

open Classical in
/-- Heavy witnesses whose same-color pair collisions are rare form a
short family. The bound has no factor for the full color range. -/
theorem local_list_heavy_family_card {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq β]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : ι → Set X)
    (hE : ∀ i, MeasurableSet (E i)) (code : ι → X → β)
    (heq : ∀ i j, MeasurableSet {x | code i x = code j x})
    (K η ε : ℝ) (hK : 0 < K) (hη : 0 < η) (hε : 0 ≤ ε)
    (hlocal : ∀ x,
      (((Finset.univ.filter fun i => x ∈ E i).image (fun i => code i x)).card : ℝ) ≤ K)
    (hmass : ∀ i, η ≤ μ.real (E i))
    (hinter : ∀ i j, i ≠ j →
      μ.real {x | x ∈ E i ∧ x ∈ E j ∧ code i x = code j x} ≤ ε)
    (hsmall : 2 * K * ε ≤ η ^ 2) :
    (Fintype.card ι : ℝ) ≤ 2 * K / η ^ 2 := by
  classical
  let M : ℝ := Fintype.card ι
  have hM : 0 ≤ M := by positivity
  have hfloor : M * η ≤ ∑ i, μ.real (E i) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, M] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmass i)
  have hupper : (∑ i, ∑ j,
      μ.real {x | x ∈ E i ∧ x ∈ E j ∧ code i x = code j x}) ≤ M + ε * M ^ 2 := by
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, ((if i = j then (1 : ℝ) else 0) + ε) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          have hevent : {x | x ∈ E i ∧ x ∈ E i ∧ code i x = code i x} = E i := by
            ext x; simp
          rw [hevent, ite_eq_left rfl]
          have hprob : μ.real (E i) ≤ 1 := by simp
          linarith
        · simpa only [ite_eq_right hij, zero_add] using hinter i j hij
      _ = _ := by simp [Finset.sum_add_distrib, M]; ring
  have hmoment := local_list_second_moment μ E hE code heq K hlocal
  have hsq : (M * η) ^ 2 ≤ K * (M + ε * M ^ 2) :=
    ((sq_le_sq₀ (by positivity) (by positivity)).mpr hfloor).trans
      (hmoment.trans (mul_le_mul_of_nonneg_left hupper hK.le))
  by_cases hzero : M = 0
  · change M ≤ _
    rw [hzero]
    positivity
  · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
    apply (mul_le_mul_iff_left₀ hMp).mp
    have hmargin := mul_le_mul_of_nonneg_right hsmall (sq_nonneg M)
    nlinarith

end

end Submission.Lib.K4PolynomialFiberLists
