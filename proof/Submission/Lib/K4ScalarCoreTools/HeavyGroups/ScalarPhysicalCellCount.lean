/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/ScalarPhysicalCellCount.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ccf90c32bd4af25c1ba009c960359aada67a01a5,
Submission/Obl/k4_scalar_mesh_projection/ScalarPhysicalCellCount.lean.
-/

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.HeavyCells
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.ScalarBaseLines
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.CellDuration

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory
open scoped NNReal ENNReal

/-- The actual scalar base-cell count for a heavy intercept group. The
incidence law and group prior are the original unnormalized laws; the
observed base may be the rounded state center. -/
theorem scalar_physical_cell_count {α ι : Type*} [MeasurableSpace α]
    (C : ℝ) (hC : 0 < C) (hMK : Submission.Lib.K4ContinuousKakeya.FiniteMK 2 C)
    (θ : Measure α) [IsFiniteMeasure θ] (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    (K h ξ error start R M : ℝ) (hK : 1 ≤ K) (hh : 0 < h) (hξ : 0 < ξ)
    (he : 0 ≤ error) (hfiner : 2 * error ≤ ξ) (hM : 0 < M)
    (hinc : inc ≤ ENNReal.ofReal K • θ.prod volume)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (Λ : Set α) (hΛ : MeasurableSet Λ)
    (hU : ∀ l ∈ Λ, |u l| ≤ K) (hV : ∀ l ∈ Λ, |v l| ≤ K)
    (hprior : θ Λ ≤ ENNReal.ofReal (K * M / h))
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    (F : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (center : ι → EuclideanSpace ℝ (Fin 2)) (m : ι → ℝ)
    (hEm : ∀ j ∈ F, MeasurableSet (E j)) (hEd : (F : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ F, E j ⊆ Metric.closedBall 0 R)
    (hbox : ∀ j ∈ F, ∀ x ∈ E j, ∀ i : Fin 2, center j i ≤ x i ∧ x i ≤ center j i + ξ)
    (hvol : ∀ j ∈ F, ENNReal.ofReal (ξ ^ 2) ≤ volume (E j))
    (hm : ∀ j ∈ F, 0 ≤ m j) (hsum : ∑ j ∈ F, m j = M)
    (hround : ∀ j ∈ F, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ i : Fin 2,
      |Φ ω i - baseLinePoint (u ω.1) (v ω.1) ((ω.2 - start) / h) i| ≤ error)
    (hsucc : ∀ j ∈ F, ENNReal.ofReal ((m j) ^ 2 / 2) ≤
      Measure.pi (fun _ : Fin 2 => inc)
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          1 / K ≤ |v (ω 0).1 - v (ω 1).1|}) :
    1 / (65536 * C * K ^ 8) ≤ ξ ^ 2 * (F.card : ℝ) := by
  classical
  have hKp : 0 < K := by linarith
  let K₀ : ℝ≥0 := ⟨K, hKp.le⟩
  let B₀ : ℝ≥0 := ⟨2 * h * ξ, by positivity⟩
  let c₀ : ℝ≥0 := K₀ * B₀
  have hKcast : ENNReal.ofReal K = (K₀ : ℝ≥0∞) := by
    exact ENNReal.ofReal_coe_nnreal (p := K₀)
  have hinc' : inc ≤ K₀ • θ.prod volume := by
    simpa only [hKcast, Measure.coe_nnreal_smul] using hinc
  let a : α → EuclideanSpace ℝ (Fin 2) :=
    fun l => if l ∈ Λ then baseLinePoint (u l) (v l) 0 else 0
  let e : α → EuclideanSpace ℝ (Fin 2) := fun l => unitBaseDirection (v l)
  have ha : Measurable a := by
    dsimp only [a]
    apply Measurable.ite hΛ
    · unfold baseLinePoint
      fun_prop
    · exact measurable_const
  have heM : Measurable e := continuous_unitBaseDirection.measurable.comp hv
  have he1 (l : α) : ‖e l‖ = 1 := norm_unitBaseDirection (v l)
  have hBa (l : α) : ‖a l‖ ≤ K := by
    by_cases hl : l ∈ Λ
    · have hnorm : ‖baseLinePoint (u l) (v l) 0‖ = |u l| := by
        simp [baseLinePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs]
      simpa only [a, hl, ↓reduceIte, hnorm] using hU l hl
    · simp only [a, hl, ↓reduceIte, norm_zero]
      linarith
  have hpush (j : ι) (hj : j ∈ F) :
      (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤ c₀ • θ.restrict Λ := by
    apply rounded_time_cell_prior_cap θ inc K₀ B₀ hinc'
      {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j} ((measurable_fst hΛ).inter (hΦ (hEm j hj)))
      Λ hΛ (fun ω hω => hω.1) (fun ω => Φ ω 0) start h (center j 0) ξ error
      hh hξ.le he
    · change h * (ξ + 2 * error) ≤ 2 * h * ξ
      nlinarith
    · intro ω hω
      simpa [baseLinePoint] using hround j hj ω hω.1 hω.2 0
    · intro ω hω
      exact hbox j hj (Φ ω) hω.2 0
  have htube (j : ι) (hj : j ∈ F) (ω : α × ℝ) (hl : ω.1 ∈ Λ) (hω : Φ ω ∈ E j)
      (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ E j) :
      x ∈ Submission.Lib.K4ContinuousKakeya.tube (4 * ξ) (a ω.1) (e ω.1) := by
    have hnear (i : Fin 2) : |x i - Φ ω i| ≤ ξ := by
      apply abs_le.mpr
      constructor <;> linarith [(hbox j hj x hx i).1, (hbox j hj x hx i).2,
        (hbox j hj (Φ ω) hω i).1, (hbox j hj (Φ ω) hω i).2]
    simpa only [a, hl, ↓reduceIte, e] using rounded_base_cell_mem_tube
      (u ω.1) (v ω.1) ((ω.2 - start) / h) ξ error hξ he hfiner (Φ ω) x hnear
        (hround j hj ω hl hω)
  have hsuccess (j : ι) (hj : j ∈ F) :
      ENNReal.ofReal ((1 / 2 : ℝ) * (m j) ^ 2) ≤
      Measure.pi (fun _ : Fin 2 => inc)
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          1 / (4 * K ^ 3) ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (ω i).1 k)|} := by
    have hsub : {ω : Fin 2 → α × ℝ | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          1 / K ≤ |v (ω 0).1 - v (ω 1).1|} ⊆
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          1 / (4 * K ^ 3) ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (ω i).1 k)|} := by
      intro ω hω
      refine ⟨hω.1, ?_⟩
      have hdet := normalized_velocity_pair_bound (v (ω 0).1) (v (ω 1).1) K hK
        (hV _ (hω.1 0).1) (hV _ (hω.1 1).1) hω.2
      have hid : (fun i k : Fin 2 => e (ω i).1 k) =
          (fun i k : Fin 2 => unitBaseDirection (![v (ω 0).1, v (ω 1).1] i) k) := by
        funext i k
        fin_cases i <;> rfl
      simpa only [hid] using hdet
    have hleft : ENNReal.ofReal ((1 / 2 : ℝ) * (m j) ^ 2) =
        ENNReal.ofReal ((m j) ^ 2 / 2) := by congr 1; ring
    exact hleft ▸ (hsucc j hj).trans (measure_mono hsub)
  have hcpos : 0 < c₀ := by change (0 : ℝ) < K * (2 * h * ξ); positivity
  have hprior' : θ Λ ≤ ENNReal.ofReal ((K / h) * M) := by
    have hid : K * M / h = (K / h) * M := by ring
    simpa only [hid] using hprior
  have hcount := pair_incidence_cell_count C hC.le hMK θ inc Φ hΦ a e ha heM he1 K hBa
    (4 * ξ) R (by positivity) Λ hΛ F E hEm hEd hER c₀ hcpos hpush htube m M (K / h)
      (ξ ^ 2) (1 / (4 * K ^ 3)) (1 / 2) hm hM (by positivity) (by positivity)
        (by positivity) (by norm_num) hsum hprior' hvol hsuccess
  have hscaled := scalar_pair_cell_count_scaled C (2 * K) h ξ (4 * ξ) (K / h) (c₀ : ℝ)
    (1 / (4 * K ^ 3)) (1 / 2) F.card hC (by linarith) hh hξ (by positivity)
      (by positivity) (by positivity) le_rfl (by gcongr; linarith) (by
        change K * (2 * h * ξ) ≤ 2 * K * h * ξ
        nlinarith) (by gcongr; linarith) (by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
        linarith) hcount
  have hid : 256 * C * (2 * K) ^ 8 = 65536 * C * K ^ 8 := by ring
  simpa only [hid] using hscaled

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
