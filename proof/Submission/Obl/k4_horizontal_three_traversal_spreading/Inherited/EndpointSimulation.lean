-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/EndpointSimulation.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/EndpointSimulation.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.CriticalEndpoint

/-! Deterministic error propagation for the three critical horizontal traversals. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

/-- Errors in a spatial starting point grow by at most two over a unit-time
traversal. No bound on the velocity or the affine part is required. -/
theorem horizontalTraverse_start_error (c t s E : ℝ) (hE : 0 ≤ E)
    (hts : |s - t| ≤ 1) (z z' : Fin 2 → ℝ) (hz : ∀ i, |z i - z' i| ≤ E) :
    ∀ i, |horizontalTraverse c t s z i - horizontalTraverse c t s z' i| ≤ 2 * E := by
  intro i
  fin_cases i
  · change |z 0 + c * (s - t) - (z' 0 + c * (s - t))| ≤ _
    rw [show z 0 + c * (s - t) - (z' 0 + c * (s - t)) = z 0 - z' 0 by ring]
    linarith [hz 0]
  · change |z 1 + (-z 0 + t * c) * (s - t) -
      (z' 1 + (-z' 0 + t * c) * (s - t))| ≤ _
    calc
      _ = |(z 1 - z' 1) - (z 0 - z' 0) * (s - t)| := by congr 1; ring
      _ ≤ |z 1 - z' 1| + |(z 0 - z' 0) * (s - t)| := abs_sub _ _
      _ ≤ E + E * 1 := add_le_add (hz 1) (by
        rw [abs_mul]
        exact mul_le_mul (hz 0) hts (abs_nonneg _) hE)
      _ = _ := by ring

/-- A fine-state refresh perturbs one exact traversal by an explicit amount.
Only the horizontal starting position is bounded; the transverse one is free. -/
theorem horizontalTraverse_refresh_error
    (c t t' s K δ : ℝ) (z z' : Fin 2 → ℝ)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hc : |c| ≤ K) (hz0 : |z' 0| ≤ K)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (htt : |t - t'| ≤ δ)
    (hzz : ∀ i, |z i - z' i| ≤ δ) :
    ∀ i, |horizontalTraverse c t s z i - horizontalTraverse c t' s z' i| ≤ 6 * K * δ := by
  have hK0 : 0 ≤ K := by linarith
  have hKD : δ ≤ K * δ := by nlinarith
  have hst : |s - t| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have ht1 : |t'| ≤ 1 := abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
  have hprod : |t * (s - t) - t' * (s - t')| ≤ 2 * δ := by
    calc
      _ = |(t - t') * (s - t) - t' * (t - t')| := by congr 1; ring
      _ ≤ |(t - t') * (s - t)| + |t' * (t - t')| := abs_sub _ _
      _ ≤ δ * 1 + 1 * δ := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul htt hst (abs_nonneg _) hδ)
          (mul_le_mul ht1 htt (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  intro i
  fin_cases i
  · change |z 0 + c * (s - t) - (z' 0 + c * (s - t'))| ≤ _
    calc
      _ = |(z 0 - z' 0) - c * (t - t')| := by congr 1; ring
      _ ≤ |z 0 - z' 0| + |c * (t - t')| := abs_sub _ _
      _ ≤ δ + K * δ := add_le_add (hzz 0) (by
        rw [abs_mul]
        exact mul_le_mul hc htt (abs_nonneg _) hK0)
      _ ≤ _ := by nlinarith
  · change |z 1 + (-z 0 + t * c) * (s - t) -
      (z' 1 + (-z' 0 + t' * c) * (s - t'))| ≤ _
    calc
      _ = |((z 1 - z' 1) - (z 0 - z' 0) * (s - t)) +
          z' 0 * (t - t') + c * (t * (s - t) - t' * (s - t'))| := by congr 1; ring
      _ ≤ |(z 1 - z' 1) - (z 0 - z' 0) * (s - t)| +
          |z' 0 * (t - t')| + |c * (t * (s - t) - t' * (s - t'))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (δ + δ * 1) + K * δ + K * (2 * δ) := by
        apply add_le_add
        · apply add_le_add
          · exact (abs_sub _ _).trans (add_le_add (hzz 1) (by
              rw [abs_mul]
              exact mul_le_mul (hzz 0) hst (abs_nonneg _) hδ))
          · rw [abs_mul]
            exact mul_le_mul hz0 htt (abs_nonneg _) hK0
        · rw [abs_mul]
          exact mul_le_mul hc hprod (abs_nonneg _) hK0
      _ ≤ _ := by nlinarith

/-- Velocity rounding has no coefficient-size loss over a unit-time traversal. -/
theorem horizontalTraverse_velocity_error
    (c c' t s δ : ℝ) (z : Fin 2 → ℝ) (hδ : 0 ≤ δ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hcc : |c - c'| ≤ δ) :
    ∀ i, |horizontalTraverse c t s z i - horizontalTraverse c' t s z i| ≤ δ := by
  have hst : |s - t| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hmul : |(c - c') * (s - t)| ≤ δ := by
    rw [abs_mul]
    exact (mul_le_mul hcc hst (abs_nonneg _) hδ).trans_eq (mul_one δ)
  intro i
  fin_cases i
  · change |z 0 + c * (s - t) - (z 0 + c' * (s - t))| ≤ _
    convert hmul using 1 <;> congr 1 <;> ring
  · change |z 1 + (-z 0 + t * c) * (s - t) -
      (z 1 + (-z 0 + t * c') * (s - t))| ≤ _
    calc
      _ = |t * ((c - c') * (s - t))| := by congr 1; ring
      _ ≤ 1 * δ := by
        rw [abs_mul]
        exact mul_le_mul ht1 hmul (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- Three approximate horizontal traversals stay within seven times their
individual error of the exact critical endpoint. Signed increments are allowed. -/
theorem critical_endpoint_simulation
    (c : Fin 3 → ℝ) (t : Fin 4 → ℝ) (z : Fin 4 → Fin 2 → ℝ) (E : ℝ)
    (hE : 0 ≤ E) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hstep : ∀ i : Fin 3, ∀ j : Fin 2,
      |z i.succ j - horizontalTraverse (c i) (t i.castSucc) (t i.succ) (z i.castSucc) j| ≤ E) :
    ∀ j, |z 3 j - criticalSpatialEndpoint c ![t 0, z 0 0, z 0 1] (t 3) ![t 1, t 2] j| ≤
      7 * E := by
  let A := horizontalTraverse (c 0) (t 0) (t 1) (z 0)
  let B := horizontalTraverse (c 1) (t 1) (t 2) A
  let D := horizontalTraverse (c 2) (t 2) (t 3) B
  have hg (i j : Fin 4) : |t i - t j| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(ht i).1, (ht j).2], by linarith [(ht i).2, (ht j).1]⟩
  have h1 : ∀ j, |z 1 j - A j| ≤ E := by
    simpa [A] using hstep 0
  have h2a := horizontalTraverse_start_error (c 1) (t 1) (t 2) E hE (hg 2 1) (z 1) A h1
  have h2 : ∀ j, |z 2 j - B j| ≤ 3 * E := by
    intro j
    have hstep1 : |z 2 j - horizontalTraverse (c 1) (t 1) (t 2) (z 1) j| ≤ E := by
      simpa using hstep 1 j
    have hclose : |horizontalTraverse (c 1) (t 1) (t 2) (z 1) j - B j| ≤ 2 * E := h2a j
    exact (abs_sub_le (z 2 j) (horizontalTraverse (c 1) (t 1) (t 2) (z 1) j) (B j)).trans
      (by linarith only [hstep1, hclose])
  have h3a := horizontalTraverse_start_error (c 2) (t 2) (t 3) (3 * E)
    (by positivity) (hg 3 2) (z 2) B h2
  intro j
  rw [criticalSpatialEndpoint_eq_traversals]
  change |z 3 j - D j| ≤ _
  have hstep2 : |z 3 j - horizontalTraverse (c 2) (t 2) (t 3) (z 2) j| ≤ E := by
    simpa using hstep 2 j
  have hclose : |horizontalTraverse (c 2) (t 2) (t 3) (z 2) j - D j| ≤ 2 * (3 * E) := h3a j
  exact (abs_sub_le (z 3 j) (horizontalTraverse (c 2) (t 2) (t 3) (z 2) j) (D j)).trans
    (by linarith only [hstep2, hclose])

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
