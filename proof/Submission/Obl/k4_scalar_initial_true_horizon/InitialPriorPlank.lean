import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellDefs
import Submission.Obl.k4_scalar_initial_true_horizon.Basic

/-! Original coefficient-prior density bounds on scalar full-block planks. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial)

noncomputable def initialShearMatrix (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, t, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, t, t ^ 2;
    0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

noncomputable def initialShear (t : ℝ) : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) :=
  Matrix.toLin' (initialShearMatrix t)

theorem initialShear_apply (t : ℝ) (b : Fin 5 → ℝ) :
    initialShear t b = ![b 0 + t * b 1, b 1, b 2 + t * b 3 + t ^ 2 * b 4, b 3, b 4] := by
  ext i
  fin_cases i <;> simp [initialShear, Matrix.toLin'_apply, initialShearMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

theorem initialShear_det (t : ℝ) : LinearMap.det (initialShear t) = 1 := by
  rw [initialShear, LinearMap.det_toLin', Matrix.det_of_isUpperTriangular]
  · norm_num [initialShearMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [initialShearMatrix]

theorem volume_initialShear_preimage (t : ℝ) (S : Set (Fin 5 → ℝ)) :
    volume (initialShear t ⁻¹' S) = volume S := by
  rw [Measure.addHaar_preimage_linearMap volume (by rw [initialShear_det]; norm_num),
    initialShear_det]
  simp

/-- In sheared coordinates the plank is contained in a box with side lengths
`2w`, `4w/q`, `aL`, `2Kb`, `2Kb`. -/
def initialPlankBox (y₀ s₀ Kb aL q w : ℝ) (m : ℤ) : Set (Fin 5 → ℝ) :=
  Set.pi univ ![Icc (y₀ - w) (y₀ + w), Icc (s₀ - 2 * w / q) (s₀ + 2 * w / q),
    Icc ((m : ℝ) * aL) (((m : ℝ) + 1) * aL), Icc (-Kb) Kb, Icc (-Kb) Kb]

theorem volume_initialPlankBox (y₀ s₀ Kb aL q w : ℝ) (m : ℤ)
    (hK : 0 ≤ Kb) (ha : 0 ≤ aL) (hq : 0 < q) (hw : 0 ≤ w) :
    volume (initialPlankBox y₀ s₀ Kb aL q w m) =
      ENNReal.ofReal (8 * w ^ 2 / q * aL * (2 * Kb) ^ 2) := by
  unfold initialPlankBox
  rw [volume_pi_pi]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, Real.volume_Icc]
  have h1 : y₀ + w - (y₀ - w) = 2 * w := by ring
  have h2 : s₀ + 2 * w / q - (s₀ - 2 * w / q) = 4 * w / q := by ring
  have h3 : ((m : ℝ) + 1) * aL - (m : ℝ) * aL = aL := by ring
  have h4 : Kb - -Kb = 2 * Kb := by ring
  rw [h1, h2, h3, h4]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The original trajectories in one hidden bin and one scalar full-block
plank. The index cut only reduces its mass. -/
def initialPriorPlank (Nb Kb aL q t₀ w : ℝ) (m : ℤ) (l₀ : Coeff) : Set Coeff :=
  {l | bddTraj Nb Kb l ∧ xBin aL t₀ l = m ∧
    ∀ t ∈ Icc t₀ (t₀ + q), |spatial l₀ t - spatial l t| ≤ w}

theorem volume_initialPriorPlank_fiber (Nb Kb aL q t₀ w : ℝ) (m : ℤ) (l₀ : Coeff)
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hq : 0 < q) (hw : 0 ≤ w) (i : ℕ) :
    volume {b : Fin 5 → ℝ | (i, b) ∈ initialPriorPlank Nb Kb aL q t₀ w m l₀} ≤
      ENNReal.ofReal (8 * w ^ 2 / q * aL * (2 * Kb) ^ 2) := by
  let S := initialPlankBox (spatial l₀ t₀) (l₀.2 1) Kb aL q w m
  have hsub : {b : Fin 5 → ℝ | (i, b) ∈ initialPriorPlank Nb Kb aL q t₀ w m l₀} ⊆
      initialShear t₀ ⁻¹' S := by
    intro b hb
    have h0 := hb.2.2 t₀ ⟨le_rfl, by linarith⟩
    have h1 := hb.2.2 (t₀ + q) ⟨by linarith, le_rfl⟩
    have hs : |b 1 - l₀.2 1| ≤ 2 * w / q := by
      apply (le_div_iff₀ hq).mpr
      calc
        _ = |q * (l₀.2 1 - b 1)| := by
          rw [abs_mul, abs_of_pos hq, abs_sub_comm]
          ring
        _ = |(spatial l₀ (t₀ + q) - spatial (i, b) (t₀ + q)) -
            (spatial l₀ t₀ - spatial (i, b) t₀)| := by
          congr 1
          unfold spatial
          ring
        _ ≤ |spatial l₀ (t₀ + q) - spatial (i, b) (t₀ + q)| +
            |spatial l₀ t₀ - spatial (i, b) t₀| := abs_sub _ _
        _ ≤ _ := by linarith
    have hx := Int.floor_eq_iff.mp hb.2.1
    change (m : ℝ) ≤ (b 2 + t₀ * b 3 + t₀ ^ 2 * b 4) / aL ∧
      (b 2 + t₀ * b 3 + t₀ ^ 2 * b 4) / aL < (m : ℝ) + 1 at hx
    have hx0 := (le_div_iff₀ ha).mp hx.1
    have hx1 := (div_lt_iff₀ ha).mp hx.2
    change initialShear t₀ b ∈ S
    rw [initialShear_apply]
    change _ ∈ Set.pi univ _
    simp only [mem_pi, mem_univ, true_implies]
    intro e
    fin_cases e <;> dsimp only [S, initialPlankBox, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · change spatial l₀ t₀ - w ≤ b 0 + t₀ * b 1 ∧ b 0 + t₀ * b 1 ≤ spatial l₀ t₀ + w
      change |spatial l₀ t₀ - (b 0 + t₀ * b 1)| ≤ w at h0
      exact ⟨by linarith [(abs_le.mp h0).2], by linarith [(abs_le.mp h0).1]⟩
    · change l₀.2 1 - 2 * w / q ≤ b 1 ∧ b 1 ≤ l₀.2 1 + 2 * w / q
      exact ⟨by linarith [(abs_le.mp hs).1], by linarith [(abs_le.mp hs).2]⟩
    · exact ⟨hx0, hx1.le⟩
    · exact abs_le.mp (hb.1.2 3)
    · exact abs_le.mp (hb.1.2 4)
  calc
    _ ≤ volume (initialShear t₀ ⁻¹' S) := measure_mono hsub
    _ = volume S := volume_initialShear_preimage t₀ S
    _ = _ := volume_initialPlankBox _ _ _ _ _ _ _ hK ha.le hq hw

theorem initialPriorPlank_measurable (Nb Kb aL q t₀ w : ℝ) (m : ℤ) (l₀ : Coeff) :
    MeasurableSet (initialPriorPlank Nb Kb aL q t₀ w m l₀) := by
  have hB : MeasurableSet {l : Coeff | bddTraj Nb Kb l} := by
    have heq : {l : Coeff | bddTraj Nb Kb l} =
        {l : Coeff | (l.1 : ℝ) ≤ Nb} ∩ ⋂ e : Fin 5, {l : Coeff | |l.2 e| ≤ Kb} := by
      ext l
      simp only [bddTraj, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [heq]
    apply (measurableSet_le ((measurable_of_countable (fun z : ℕ => (z : ℝ))).comp measurable_fst) measurable_const).inter
    exact MeasurableSet.iInter (fun e =>
      measurableSet_le ((measurable_pi_apply e).comp measurable_snd).abs measurable_const)
  have hX : Measurable (xBin aL t₀) := by
    unfold xBin Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden
    fun_prop
  have hP : MeasurableSet {l : Coeff | ∀ t ∈ Icc t₀ (t₀ + q), |spatial l₀ t - spatial l t| ≤ w} := by
    have heq : {l : Coeff | ∀ t ∈ Icc t₀ (t₀ + q), |spatial l₀ t - spatial l t| ≤ w} =
        ⋂ t, ⋂ (_ : t ∈ Icc t₀ (t₀ + q)), {l : Coeff | |spatial l₀ t - spatial l t| ≤ w} := by
      ext l
      simp
    rw [heq]
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro ht
    apply isClosed_le _ continuous_const
    unfold spatial
    fun_prop
  exact hB.inter ((hX (measurableSet_singleton m)).inter hP)

/-- The frozen finite mixture prior obeys the plank-density bound under its
original weights. No regularity of the prior pieces beyond that representation
is needed, since the bounded coefficient cut is already inside the plank set. -/
theorem initialPriorPlank_mass_le {n : ℕ} (ν : Measure Coeff)
    (h : Fin n → ℝ) (idx : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ))
    (hν : ν = ∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (idx j, b)) (volume.restrict (B j)))
    (hh : ∀ j, 0 ≤ h j) {H Nb Kb aL q t₀ w : ℝ} (hH : ∑ j, h j ≤ H)
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hq : 0 < q) (hw : 0 ≤ w)
    (m : ℤ) (l₀ : Coeff) :
    ν (initialPriorPlank Nb Kb aL q t₀ w m l₀) ≤
      ENNReal.ofReal (H * 8 * w ^ 2 / q * aL * (2 * Kb) ^ 2) := by
  let S := initialPriorPlank Nb Kb aL q t₀ w m l₀
  let V := 8 * w ^ 2 / q * aL * (2 * Kb) ^ 2
  have hS : MeasurableSet S := initialPriorPlank_measurable _ _ _ _ _ _ _ _
  have hV : ∀ j : Fin n,
      Measure.map (fun b => (idx j, b)) (volume.restrict (B j)) S ≤ ENNReal.ofReal V := by
    intro j
    rw [Measure.map_apply (by fun_prop) hS]
    calc
      _ ≤ volume ((fun b => (idx j, b)) ⁻¹' S) := Measure.restrict_le_self _
      _ ≤ _ := volume_initialPriorPlank_fiber Nb Kb aL q t₀ w m l₀ hK ha hq hw (idx j)
  have hH0 : 0 ≤ H := (Finset.sum_nonneg (fun j _ => hh j)).trans hH
  have hweights : (∑ j, ENNReal.ofReal (h j)) ≤ ENNReal.ofReal H := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hh j)]
    exact ENNReal.ofReal_le_ofReal hH
  have heq : H * V = H * 8 * w ^ 2 / q * aL * (2 * Kb) ^ 2 := by dsimp [V]; ring
  calc
    ν S = ∑ j, ENNReal.ofReal (h j) *
        Measure.map (fun b => (idx j, b)) (volume.restrict (B j)) S := by
      rw [hν, Measure.finsetSum_apply]
      simp only [Measure.smul_apply, smul_eq_mul]
    _ ≤ ∑ j, ENNReal.ofReal (h j) * ENNReal.ofReal V :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hV j) zero_le)
    _ = (∑ j, ENNReal.ofReal (h j)) * ENNReal.ofReal V := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal H * ENNReal.ofReal V := mul_le_mul_of_nonneg_right hweights zero_le
    _ = ENNReal.ofReal (H * V) := (ENNReal.ofReal_mul hH0).symm
    _ = _ := by rw [heq]

/-- In an exact problem, the number and heights of prior pieces give the
fixed density factor `N^(2M)` in the finest-scale plank cap. -/
theorem Exact.prior_plank_mass_le {p : Data} (hp : Exact p) (k : ℕ)
    (a : Fin (worlds p k)) {Nb Kb aL q t₀ w : ℝ}
    (hK : 0 ≤ Kb) (ha : 0 < aL) (hq : 0 < q) (hw : 0 ≤ w)
    (m : ℤ) (l₀ : Coeff) :
    prior p k a (initialPriorPlank Nb Kb aL q t₀ w m l₀) ≤
      ENNReal.ofReal (N p k ^ (2 * (M p : ℝ)) * 8 * w ^ 2 / q * aL * (2 * Kb) ^ 2) := by
  obtain ⟨n, hn, h, idx, B, hpieces, hν⟩ := (((hp.2.1 k).2.2.2.1 a).2.1)
  have hN : 0 < N p k := lt_of_lt_of_le (by norm_num) (hp.resolution_ge k)
  have hsum : ∑ j, h j ≤ N p k ^ (2 * (M p : ℝ)) := by
    calc
      _ ≤ ∑ _j : Fin n, N p k ^ (M p : ℝ) :=
        Finset.sum_le_sum (fun j _ => (hpieces j).2.1)
      _ = (n : ℝ) * N p k ^ (M p : ℝ) := by simp
      _ ≤ N p k ^ (M p : ℝ) * N p k ^ (M p : ℝ) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hN.le _)
      _ = _ := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
  exact initialPriorPlank_mass_le (prior p k a) h idx B hν (fun j => (hpieces j).1)
    hsum hK ha hq hw m l₀

end Submission.Obl.k4_scalar_initial_true_horizon
