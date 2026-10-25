-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/BaseCubes.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ObservationGrid

/-!
# Base cubes of the observation grid

The base cube `cubeSet p n` is the half-open cube `∏ₑ [nₑ p, (nₑ+1) p)` in the base space.  A
base point lies in it exactly when its cube index is `n`.  It has volume `p³`, diameter less
than `2p`, time extent `p`, and lies in an explicit ball; distinct cubes are disjoint.  These
are the cell hypotheses of the broad completion.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set

noncomputable section

/-- The base cube of index `n` at mesh `p`. -/
def cubeSet (p : ℝ) (n : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {z | ∀ e, ⌊z e / p⌋ = n e}

lemma basePoint_mem_cubeSet_iff (p : ℝ) (n : Fin 3 → ℤ) (q : Ev) :
    basePoint q ∈ cubeSet p n ↔ cubeIdx p q = n := by
  simp only [cubeSet, Set.mem_ofPred_eq, cubeIdx, funext_iff]

lemma mem_cubeSet_iff {p : ℝ} (hp : 0 < p) (n : Fin 3 → ℤ) (z : EuclideanSpace ℝ (Fin 3)) :
    z ∈ cubeSet p n ↔ ∀ e, (n e : ℝ) * p ≤ z e ∧ z e < ((n e : ℝ) + 1) * p := by
  simp only [cubeSet, Set.mem_ofPred_eq, Int.floor_eq_iff, le_div_iff₀ hp, div_lt_iff₀ hp]

lemma measurable_euclid_apply (e : Fin 3) :
    Measurable fun z : EuclideanSpace ℝ (Fin 3) => z e :=
  (measurable_pi_apply e).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable

lemma measurableSet_cubeSet (p : ℝ) (n : Fin 3 → ℤ) : MeasurableSet (cubeSet p n) := by
  have : cubeSet p n = ⋂ e, (fun z : EuclideanSpace ℝ (Fin 3) => ⌊z e / p⌋) ⁻¹' {n e} := by
    ext z; simp [cubeSet]
  rw [this]
  exact MeasurableSet.iInter fun e =>
    (Int.measurable_floor.comp ((measurable_euclid_apply e).div_const p))
      (measurableSet_singleton _)

lemma disjoint_cubeSet {p : ℝ} {n n' : Fin 3 → ℤ} (h : n ≠ n') :
    Disjoint (cubeSet p n) (cubeSet p n') := by
  refine Set.disjoint_left.mpr fun z hz hz' => h ?_
  funext e
  exact (hz e).symm.trans (hz' e)

lemma volume_cubeSet {p : ℝ} (hp : 0 < p) (n : Fin 3 → ℤ) :
    volume (cubeSet p n) = ENNReal.ofReal (p ^ 3) := by
  have hpre : cubeSet p n = (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → Fin 3 → ℝ) ⁻¹'
      (Set.pi Set.univ fun e => Set.Ico ((n e : ℝ) * p) (((n e : ℝ) + 1) * p)) := by
    ext z
    rw [mem_cubeSet_iff hp]
    simp [Set.mem_pi]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
  have : ∀ e : Fin 3, ENNReal.ofReal (((n e : ℝ) + 1) * p - (n e : ℝ) * p) = ENNReal.ofReal p :=
    fun e => by congr 1; ring
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hp.le]

lemma dist_lt_of_mem_cubeSet {p : ℝ} (hp : 0 < p) {n : Fin 3 → ℤ}
    {z z' : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ cubeSet p n) (hz' : z' ∈ cubeSet p n) :
    dist z z' < 2 * p := by
  rw [mem_cubeSet_iff hp] at hz hz'
  have hc : ∀ e, dist (z e) (z' e) ^ 2 ≤ p ^ 2 := by
    intro e
    rw [Real.dist_eq]
    have h1 := hz e
    have h2 := hz' e
    have : |z e - z' e| ≤ p := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg (z e - z' e), sq_abs (z e - z' e)]
  rw [EuclideanSpace.dist_eq, Real.sqrt_lt' (by positivity)]
  have hsum : ∑ e, dist (z e) (z' e) ^ 2 ≤ ∑ _e : Fin 3, p ^ 2 := Finset.sum_le_sum fun e _ => hc e
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  nlinarith

lemma time_mem_of_mem_cubeSet {p : ℝ} (hp : 0 < p) (n : Fin 3 → ℤ) :
    ∀ z ∈ cubeSet p n, z 0 ∈ Icc ((n 0 : ℝ) * p) ((n 0 : ℝ) * p + p) := by
  intro z hz
  rw [mem_cubeSet_iff hp] at hz
  obtain ⟨h1, h2⟩ := hz 0
  exact ⟨h1, by linarith⟩

/-- The Euclidean norm of a base point is at most the sum of its coordinates' moduli. -/
lemma norm_le_sum_abs_three (z : EuclideanSpace ℝ (Fin 3)) : ‖z‖ ≤ |z 0| + |z 1| + |z 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have hB : 0 ≤ |z 0| + |z 1| + |z 2| := by positivity
  rw [Real.sqrt_le_left hB]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg (z 0), abs_nonneg (z 1), abs_nonneg (z 2), sq_abs (z 0), sq_abs (z 1),
    sq_abs (z 2), mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1)),
    mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 2)),
    mul_nonneg (abs_nonneg (z 1)) (abs_nonneg (z 2))]

lemma norm_le_of_mem_cubeSet {p : ℝ} (hp : 0 < p) {n : Fin 3 → ℤ}
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ cubeSet p n) :
    ‖z‖ ≤ (|(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)| + 3) * p := by
  rw [mem_cubeSet_iff hp] at hz
  have hc : ∀ e, |z e| ≤ (|(n e : ℝ)| + 1) * p := by
    intro e
    obtain ⟨h1, h2⟩ := hz e
    rw [abs_le]
    have ha := abs_nonneg (n e : ℝ)
    have hle := le_abs_self (n e : ℝ)
    have hge := neg_abs_le (n e : ℝ)
    constructor <;> nlinarith
  refine (norm_le_sum_abs_three z).trans ?_
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  nlinarith

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
