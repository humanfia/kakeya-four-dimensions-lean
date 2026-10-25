/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/FullCrossingFormat.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/CrossingFormat.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.ChartCrossing
import Submission.Obl.k4_balanced_native_packet_transport.CPF.FiniteBooleanFormat
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

/-! The crossing tests and every finite crossing-count table have bounded
Boolean polynomial format, with degree independent of the number of labels.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MvPolynomial
open scoped Classical

noncomputable section

theorem fmt.polynomial_preimage {n m D d : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (hS : fmt n H D S) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ d) :
    fmt m H (d * D) ((fun x i => eval x (f i)) ⁻¹' S) := by
  obtain ⟨r, hr, p, hp, b, hb⟩ := hS
  refine ⟨r, hr, fun i => aeval f (p i), ?_, b, ?_⟩
  · intro i
    exact (Submission.Obl.k4_quadratic_atlas_normalization.degree_aeval_le_mul
      (p i) f d hf).trans (Nat.mul_le_mul_left d (hp i))
  · intro x
    simpa only [mem_preimage, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
      using hb (fun i => eval x (f i))

/-- The normalized horizontal coordinates as affine polynomials in the base. -/
def crossingCoordinate (c u : Spatial) (Q : Frame) (i : Fin 2) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ j : Fin 2, C (Q⁻¹ i j) * (X j.succ - C (c j) - X 0 * C (u j))

theorem crossingCoordinate_degree (c u : Spatial) (Q : Frame) (i : Fin 2) :
    (crossingCoordinate c u Q i).totalDegree ≤ 1 := by
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro j _
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_sub _ _).trans
    simp
  · apply (totalDegree_mul _ _).trans
    simp

theorem eval_crossingCoordinate (c u : Spatial) (Q : Frame) (i : Fin 2)
    (z : Fin 3 → ℝ) :
    eval z (crossingCoordinate c u Q i) =
      (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)) i := by
  fin_cases i <;> simp [crossingCoordinate, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail,
    Pi.smul_apply, smul_eq_mul]

def crossingNormTest (κ : ℝ) (c u : Spatial) (Q : Frame) : MvPolynomial (Fin 3) ℝ :=
  C (κ ^ 2) - ∑ i : Fin 2, (crossingCoordinate c u Q i) ^ 2

theorem crossingNormTest_degree (κ : ℝ) (c u : Spatial) (Q : Frame) :
    (crossingNormTest κ c u Q).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp only [totalDegree_C]
    omega
  · apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro i _
    exact (totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left 2 (crossingCoordinate_degree c u Q i))

theorem crossingNormTest_iff {κ : ℝ} (hκ : 0 ≤ κ) (c u : Spatial) (Q : Frame)
    (z : Fin 3 → ℝ) :
    0 ≤ eval z (crossingNormTest κ c u Q) ↔
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ κ := by
  simp only [crossingNormTest, map_sub, eval_C, map_sum, map_pow, eval_crossingCoordinate]
  rw [← EuclideanSpace.real_norm_sq_eq]
  exact sub_nonneg.trans (sq_le_sq₀ (norm_nonneg _) hκ)

def hiddenBaseTest (R : Test) (w : ℝ) : MvPolynomial (Fin 3) ℝ :=
  aeval ![X 0, X 1, X 2, C w] R

theorem hiddenBaseTest_degree (R : Test) (w : ℝ) :
    (hiddenBaseTest R w).totalDegree ≤ R.totalDegree := by
  apply Submission.Obl.k4_eligibility_sign_description.degree_aeval_le
  intro i
  fin_cases i <;> simp

theorem eval_hiddenBaseTest (R : Test) (w : ℝ) (z : Fin 3 → ℝ) :
    eval z (hiddenBaseTest R w) = eval ![z 0, z 1, z 2, w] R := by
  rw [hiddenBaseTest, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
  apply congrArg (fun v : Fin 4 → ℝ => eval v R)
  funext i
  fin_cases i <;> simp

theorem format_hidden_sample (R : Test) (hR : R.totalDegree ≤ 2) (w a B κ : ℝ) :
    fmt 3 4 2 {z : Fin 3 → ℝ |
      |(hiddenPolynomial R (WithLp.toLp 2 z)).eval w| ≤ 2 * κ * a ∧
      B / (2 * κ) ≤ |(hiddenPolynomial R (WithLp.toLp 2 z)).derivative.eval w|} := by
  have hd : (pderiv (3 : Fin 4) R).totalDegree ≤ 2 :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le R 3).trans (by omega)
  have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
    (Submission.Obl.k4_quadratic_atlas_normalization.format_abs_le (hiddenBaseTest R w)
      ((hiddenBaseTest_degree _ _).trans hR) (2 * κ * a))
    (Submission.Obl.k4_quadratic_atlas_normalization.format_abs_ge (hiddenBaseTest (pderiv 3 R) w)
      ((hiddenBaseTest_degree _ _).trans hd) (B / (2 * κ)))
  change fmt 3 _ _ _ at h
  convert h using 1 <;> try norm_num
  ext z
  simp only [mem_ofPred_eq, mem_inter_iff, eval_hiddenBaseTest,
    hiddenPolynomial_derivative, hiddenPolynomial_eval]

theorem format_quadraticCrosses (R : Test) (hR : R.totalDegree ≤ 2)
    (a B κ : ℝ) (m : ℕ) (n : ℤ) :
    fmt 3 (4 * m) 2 {z : Fin 3 → ℝ |
      QuadraticCrosses (hiddenPolynomial R (WithLp.toLp 2 z)) a B κ m n} := by
  have h := fmt.exists_finite (fun i : Fin m => {z : Fin 3 → ℝ |
      |(hiddenPolynomial R (WithLp.toLp 2 z)).eval (subBinPoint (a / B) m n i)| ≤ 2 * κ * a ∧
      B / (2 * κ) ≤ |(hiddenPolynomial R (WithLp.toLp 2 z)).derivative.eval
        (subBinPoint (a / B) m n i)|}) (fun _ => 4)
    (fun i => format_hidden_sample R hR _ a B κ)
  simpa [QuadraticCrosses, mul_comm] using h

theorem format_chartCrosses_base (R : Test) (hR : R.totalDegree ≤ 2)
    {κ : ℝ} (hκ : 0 ≤ κ) (T : ℕ) (j a B : ℝ) (c u : Spatial) (Q : Frame)
    (m : ℕ) (n : ℤ) :
    fmt 3 (3 + 4 * m) 2 {z : Fin 3 → ℝ |
      ChartCrosses κ T j a B c u Q R m (WithLp.toLp 2 z, n)} := by
  have ht : fmt 3 2 2 {z : Fin 3 → ℝ |
      z 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)} := by
    refine ⟨2, le_rfl, ![X 0 - C (j / (2 : ℝ) ^ T),
      C ((j + 1) / (2 : ℝ) ^ T) - X 0], ?_, fun b => b 0 && b 1, ?_⟩
    · intro i
      fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      all_goals exact (totalDegree_sub _ _).trans (by simp)
    · intro z
      simp [sub_nonneg]
  have hs : fmt 3 1 2 {z : Fin 3 → ℝ |
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - z 0 • u)‖ ≤ κ} := by
    have h := fmt.of_fintype_tests (fun _ : Fin 1 => crossingNormTest κ c u Q)
      (fun _ => crossingNormTest_degree κ c u Q) (fun v => v 0) (by simp : (Fintype.card (Fin 1) : ℝ) ≤ 1)
    simpa only [crossingNormTest_iff hκ, decide_eq_true_eq] using h
  have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter ht
    (Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter hs
      (format_quadraticCrosses R hR a B κ m n))
  change fmt 3 _ _ _ at h
  convert h using 1 <;> try norm_num
  · ring
  · ext z
    simp [ChartCrosses, and_assoc]

/-- Seven continuous coordinates of an original incidence, with its discrete tag fixed. -/
def rawIncidence (i : ℕ) (z : Fin 7 → ℝ) : Incidence :=
  ((i, fun j : Fin 6 => z j.castSucc), z 6)

def incidentBaseSub : Fin 3 → MvPolynomial (Fin 7) ℝ :=
  ![X 6, X 0 + X 6 * X 3, X 1 + X 6 * X 4]

theorem incidentBaseSub_degree (j : Fin 3) : (incidentBaseSub j).totalDegree ≤ 2 := by
  fin_cases j
  · simp [incidentBaseSub]
  all_goals
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply (totalDegree_mul _ _).trans
      simp

theorem eval_incidentBaseSub (i : ℕ) (z : Fin 7 → ℝ) (B a : ℝ) :
    (fun j => eval z (incidentBaseSub j)) = (obs B a (rawIncidence i z)).1.ofLp := by
  funext j
  fin_cases j <;> simp [incidentBaseSub, obs, rawIncidence, x]

theorem format_chartCrosses_incident_base (R : Test) (hR : R.totalDegree ≤ 2)
    {κ : ℝ} (hκ : 0 ≤ κ) (T : ℕ) (j a B : ℝ) (c u : Spatial) (Q : Frame)
    (m : ℕ) (n : ℤ) (i : ℕ) :
    fmt 7 (3 + 4 * m) 4 {z : Fin 7 → ℝ |
      ChartCrosses κ T j a B c u Q R m ((obs B a (rawIncidence i z)).1, n)} := by
  have h := (format_chartCrosses_base R hR hκ T j a B c u Q m n).polynomial_preimage
    incidentBaseSub incidentBaseSub_degree
  convert h using 1
  ext z
  simp only [mem_preimage, mem_ofPred_eq, eval_incidentBaseSub i z B a]

def hiddenSignal (B a : ℝ) : MvPolynomial (Fin 7) ℝ :=
  C (B / a) * (X 2 + X 6 * X 5)

theorem hiddenSignal_degree (B a : ℝ) : (hiddenSignal B a).totalDegree ≤ 2 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply (totalDegree_mul _ _).trans
    simp

theorem eval_hiddenSignal (B a : ℝ) (i : ℕ) (z : Fin 7 → ℝ) :
    eval z (hiddenSignal B a) = B * (x (rawIncidence i z).1 (rawIncidence i z).2) 3 / a := by
  simp [hiddenSignal, rawIncidence, x]
  ring

theorem format_hiddenBin (B a : ℝ) (n : ℤ) (i : ℕ) :
    fmt 7 2 2 {z : Fin 7 → ℝ | (obs B a (rawIncidence i z)).2 = n} := by
  refine ⟨2, le_rfl, ![hiddenSignal B a - C (n : ℝ),
    hiddenSignal B a - C ((n : ℝ) + 1)], ?_, fun b => b 0 && !(b 1), ?_⟩
  · intro j
    fin_cases j
    all_goals exact (totalDegree_sub _ _).trans (by simpa only [totalDegree_C, max_zero] using hiddenSignal_degree B a)
  · intro z
    simp [obs, Int.floor_eq_iff, eval_hiddenSignal B a i z, sub_nonneg]

/-- Only polynomially many hidden bins are relevant on the bounded original support. -/
def BoundedChartCrosses (κ : ℝ) (T : ℕ) (j a B : ℝ) (c u : Spatial) (Q : Frame)
    (R : Test) (m : ℕ) (bins : Finset ℤ) (o : Observation) : Prop :=
  o.2 ∈ bins ∧ ChartCrosses κ T j a B c u Q R m o

theorem format_boundedChartCrosses (R : Test) (hR : R.totalDegree ≤ 2)
    {κ : ℝ} (hκ : 0 ≤ κ) (T : ℕ) (j a B : ℝ) (c u : Spatial) (Q : Frame)
    (m : ℕ) (bins : Finset ℤ) (i : ℕ) :
    fmt 7 ((bins.card : ℝ) * (5 + 4 * m)) 4 {z : Fin 7 → ℝ |
      BoundedChartCrosses κ T j a B c u Q R m bins (obs B a (rawIncidence i z))} := by
  let S : (n : bins) → Set (Fin 7 → ℝ) := fun n => {z |
    (obs B a (rawIncidence i z)).2 = n ∧
      ChartCrosses κ T j a B c u Q R m ((obs B a (rawIncidence i z)).1, n)}
  have hS (n : bins) : fmt 7 (5 + 4 * m) 4 (S n) := by
    have h := Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter
      (format_hiddenBin B a n i)
      (format_chartCrosses_incident_base R hR hκ T j a B c u Q m n i)
    change fmt 7 _ _ _ at h
    convert h using 1 <;> try norm_num
    · ring
    · rfl
  have h := fmt.exists_finite S (fun _ => 5 + 4 * m) hS
  have hs : {z : Fin 7 → ℝ |
      BoundedChartCrosses κ T j a B c u Q R m bins (obs B a (rawIncidence i z))} =
      {z : Fin 7 → ℝ | ∃ n : bins, z ∈ S n} := by
    ext z
    simp only [mem_ofPred_eq, BoundedChartCrosses, S]
    constructor
    · rintro ⟨hn, hc⟩
      exact ⟨⟨_, hn⟩, rfl, hc⟩
    · rintro ⟨⟨n, hn⟩, heq, hc⟩
      dsimp at heq hc
      rw [← heq] at hn hc
      exact ⟨hn, hc⟩
  rw [hs]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using h

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
