import Submission.Obl.k4_critical_intercept_concentration.TrueBoxes
import Submission.Obl.k4_critical_intercept_concentration.NormalizedBoxes
import Submission.Obl.k4_scalar_angular_pair_agreement.ChartGeometry

namespace Submission.Obl.k4_critical_intercept_concentration

open Set MeasureTheory Inherited

noncomputable section

/-- The contact frame based at the left endpoint of a true horizontal box
has a bounded image throughout the complete block. -/
theorem true_box_parent_frame_bounds (c : Fin 5 → ℝ) (t₀ H K : ℝ)
    (hH : 0 < H) (hK : 1 ≤ K) (hc : |c 1| ≤ K)
    (hcenter : |c 3 + c 0 + (t₀ + H / 2) * c 1| ≤ K * H)
    (htilt : |c 4 - (t₀ + H / 2)| ≤ K * H)
    (q : Fin 3 → ℝ) (hq : q ∈ horizontalTrueBox c (t₀ + H / 2) H K) :
    let z₀ := c 0 + t₀ * c 1
    let y₀ := c 2 + t₀ * c 3 + c 4 * z₀
    let q' := horizontalFrame H t₀ z₀ y₀ (c 1) q
    q' 0 ∈ Icc (0 : ℝ) 1 ∧ |q' 1| ≤ K ∧ |q' 2| ≤ 8 * K ^ 2 := by
  let z₀ := c 0 + t₀ * c 1
  let y₀ := c 2 + t₀ * c 3 + c 4 * z₀
  let q' := horizontalFrame H t₀ z₀ y₀ (c 1) q
  let c' := horizontalBoxCoefficients H t₀ z₀ y₀ (c 1) c
  have hmid : (t₀ + H / 2 - t₀) / H = 1 / 2 := by field_simp; ring
  have hc₀ : c' 0 = 0 := by simp [c', horizontalBoxCoefficients, z₀]
  have hc₁ : c' 1 = 0 := by simp [c', horizontalBoxCoefficients]
  have hc₂ : c' 2 = 0 := by simp [c', horizontalBoxCoefficients, y₀]
  have hq' := (horizontalFrame_mem_trueBox H t₀ z₀ y₀ (c 1)
    (t₀ + H / 2) H K hH c q).mpr hq
  change |q' 0 - (t₀ + H / 2 - t₀) / H| ≤ (H / H) / 2 ∧
    |q' 1 - c' 0 - q' 0 * c' 1| ≤ K * (H / H) ∧
    |q' 2 - c' 2 - q' 0 * c' 3 - c' 4 * q' 1| ≤ K * (H / H) ^ 2 at hq'
  simp only [hmid, div_self hH.ne', hc₀, hc₁, hc₂, mul_zero,
    sub_zero, mul_one, one_pow] at hq'
  have ht : q' 0 ∈ Icc (0 : ℝ) 1 := by
    have ht' := abs_le.mp hq'.1
    exact ⟨by linarith, by linarith⟩
  have hct := horizontalBoxCoefficients_center_bound H t₀ z₀ y₀ (c 1)
    (t₀ + H / 2) H K c hH hH.le hK hc hcenter htilt
  change |c' 3 + c' 0 + ((t₀ + H / 2 - t₀) / H) * c' 1| ≤
      2 * K ^ 2 * (H / H) ∧
    |c' 4 - (t₀ + H / 2 - t₀) / H| ≤ K * (H / H) at hct
  simp only [hmid, div_self hH.ne', hc₀, hc₁, mul_zero, add_zero, mul_one] at hct
  have hK0 : 0 ≤ K := by linarith
  have hqtime : |q' 0| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have htilt' : |c' 4| ≤ K + 1 / 2 := by
    calc
      _ ≤ |c' 4 - 1 / 2| + |(1 : ℝ) / 2| := by
        simpa only [sub_zero] using abs_sub_le (c' 4) (1 / 2) 0
      _ ≤ _ := by simpa using add_le_add_right hct.2 (1 / 2)
  refine ⟨ht, hq'.2.1, ?_⟩
  calc
    |q' 2| = |(q' 2 - q' 0 * c' 3 - c' 4 * q' 1) +
        q' 0 * c' 3 + c' 4 * q' 1| := by congr 1; ring
    _ ≤ |q' 2 - q' 0 * c' 3 - c' 4 * q' 1| +
        |q' 0 * c' 3| + |c' 4 * q' 1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K + 2 * K ^ 2 + (K + 1 / 2) * K := by
      apply add_le_add
      · apply add_le_add hq'.2.2
        rw [abs_mul]
        exact (mul_le_mul hqtime hct.1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · rw [abs_mul]
        exact mul_le_mul htilt' hq'.2.1 (abs_nonneg _) (by positivity)
    _ ≤ 8 * K ^ 2 := by nlinarith

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def blockLeft (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : ℝ :=
  (((cfg.j k s i : ℕ) : ℝ)) * cfg.timeLength k s

def blockOrigin (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Fin 3 → ℝ :=
  ![cfg.blockLeft k s i,
    cfg.c k s i 0 + cfg.blockLeft k s i * cfg.c k s i 1,
    cfg.c k s i 2 + cfg.blockLeft k s i * cfg.c k s i 3 + cfg.c k s i 4 *
      (cfg.c k s i 0 + cfg.blockLeft k s i * cfg.c k s i 1)]

def parentFrame (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  horizontalFrame (cfg.timeLength k s) (cfg.blockOrigin k s i 0)
    (cfg.blockOrigin k s i 1) (cfg.blockOrigin k s i 2) (cfg.c k s i 1) q

def framedPoint (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) : Fin 3 → ℝ :=
  cfg.parentFrame k s i (nativeHorizontalLine (cfg.b k p.1) p.2)

theorem block_interval (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    I (cfg.T k s) (cfg.j k s i) =
      Icc (cfg.blockLeft k s i) (cfg.blockLeft k s i + cfg.timeLength k s) := by
  simpa only [I, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I,
    blockLeft, timeLength, div_eq_mul_inv] using
    Submission.Obl.k4_scalar_angular_pair_agreement.I_eq_time_block (cfg.T k s) (cfg.j k s i)

theorem midpoint_eq_blockLeft (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    cfg.midpoint k s i = cfg.blockLeft k s i + cfg.timeLength k s / 2 := by
  dsimp [midpoint, blockLeft]
  ring

theorem blockLeft_mem_I (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    cfg.blockLeft k s i ∈ I (cfg.T k s) (cfg.j k s i) := by
  rw [cfg.block_interval]
  exact ⟨le_rfl, le_add_of_nonneg_right (cfg.timeLength_pos k s).le⟩

theorem midpoint_mem_I (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) :
    cfg.midpoint k s i ∈ I (cfg.T k s) (cfg.j k s i) := by
  rw [cfg.block_interval, cfg.midpoint_eq_blockLeft]
  have hh := cfg.timeLength_pos k s
  exact ⟨by linarith, by linarith⟩

theorem parentFrame_time_mem (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (q : Fin 3 → ℝ) (ht : q 0 ∈ I (cfg.T k s) (cfg.j k s i)) :
    cfg.parentFrame k s i q 0 ∈ Icc (0 : ℝ) 1 := by
  rw [cfg.block_interval] at ht
  change (q 0 - cfg.blockLeft k s i) / cfg.timeLength k s ∈ Icc (0 : ℝ) 1
  exact ⟨div_nonneg (by linarith [ht.1]) (cfg.timeLength_pos k s).le,
    (div_le_one (cfg.timeLength_pos k s)).mpr (by linarith [ht.2])⟩

theorem AssignmentLevel.blockOrigin_bounds {cfg : Data α} (h : cfg.Valid)
    {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    |cfg.blockOrigin k s i 0| ≤ 1 ∧ |cfg.blockOrigin k s i 1| ≤ 3 * cfg.K k ∧
      |cfg.c k s i 1| ≤ cfg.K k := by
  have ht := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) (cfg.blockLeft_mem_I k s i)
  have habs : |cfg.blockLeft k s i| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  refine ⟨habs, ?_, a.coefficient_bound i 1⟩
  change |cfg.c k s i 0 + cfg.blockLeft k s i * cfg.c k s i 1| ≤ 3 * cfg.K k
  have hm : |cfg.blockLeft k s i * cfg.c k s i 1| ≤ cfg.K k := by
    rw [abs_mul]
    exact (mul_le_mul habs (a.coefficient_bound i 1) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (abs_add_le _ _).trans (by linarith [a.coefficient_bound i 0, h.subpower.1 k])

/-- The true horizontal parent has a bounded image in its actual contact
frame, uniformly in its dyadic time length. -/
theorem AssignmentLevel.framedPoint_bounds {cfg : Data α} (h : cfg.Valid)
    {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s))
    {p : α × ℝ} (hl : p.1 ∈ cfg.A k s i)
    (ht : p.2 ∈ I (cfg.T k s) (cfg.j k s i)) :
    (cfg.framedPoint k s i p) 0 ∈ Icc (0 : ℝ) 1 ∧
    |cfg.framedPoint k s i p 1| ≤ cfg.K k ^ 2 ∧
    ∀ e : Fin 3, |cfg.framedPoint k s i p e| ≤ 8 * cfg.K k ^ 4 := by
  have hK := h.subpower.1 k
  have hKsq : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hgeo := a.native_point_in_true_box h i p.1 hl ht
  have hc := a.native_box_center_bounds h i
  rw [cfg.midpoint_eq_blockLeft] at hgeo hc
  have hbounds := true_box_parent_frame_bounds (cfg.c k s i)
    (cfg.blockLeft k s i) (cfg.timeLength k s) (cfg.K k ^ 2)
    (cfg.timeLength_pos k s) (by nlinarith) ((a.coefficient_bound i 1).trans hKsq)
    (hc.1.trans (mul_le_mul_of_nonneg_right hKsq (cfg.timeLength_pos k s).le))
    (hc.2.trans (mul_le_mul_of_nonneg_right hKsq (cfg.timeLength_pos k s).le))
    (nativeHorizontalLine (cfg.b k p.1) p.2) hgeo
  change (cfg.framedPoint k s i p) 0 ∈ Icc (0 : ℝ) 1 ∧
    |cfg.framedPoint k s i p 1| ≤ cfg.K k ^ 2 ∧
    |cfg.framedPoint k s i p 2| ≤ 8 * (cfg.K k ^ 2) ^ 2 at hbounds
  refine ⟨hbounds.1, hbounds.2.1, ?_⟩
  have hfour : 1 ≤ cfg.K k ^ 4 := one_le_pow₀ hK
  have htwofour : cfg.K k ^ 2 ≤ cfg.K k ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  intro e
  fin_cases e
  · have htime : |cfg.framedPoint k s i p 0| ≤ 1 := by
      simpa only [abs_of_nonneg hbounds.1.1] using hbounds.1.2
    exact htime.trans (by linarith)
  · exact hbounds.2.1.trans (by linarith)
  · change |cfg.framedPoint k s i p 2| ≤ 8 * cfg.K k ^ 4
    convert hbounds.2.2 using 1 <;> ring

/-- A true descendant meeting the parent is a horizontal box in the same
contact frame, with the fourth-power ratio of actual dyadic lengths. -/
theorem AssignmentLevel.normalized_true_box {cfg : Data α} (h : cfg.Valid)
    {k : ℕ} {s t : ℝ} (parent : cfg.AssignmentLevel k s)
    (child : cfg.AssignmentLevel k t) (ip : Fin (cfg.n k s)) (i : Fin (cfg.n k t))
    (hrel : cfg.timeLength k t / cfg.timeLength k s ≤ 1)
    {p : α × ℝ} (hp : p.1 ∈ cfg.A k s ip)
    (hpt : p.2 ∈ I (cfg.T k s) (cfg.j k s ip))
    (hi : p.1 ∈ cfg.A k t i) (hit : p.2 ∈ I (cfg.T k t) (cfg.j k t i)) :
    let H := cfg.timeLength k s
    let h' := cfg.timeLength k t / H
    let c' := horizontalBoxCoefficients H (cfg.blockOrigin k s ip 0)
      (cfg.blockOrigin k s ip 1) (cfg.blockOrigin k s ip 2) (cfg.c k s ip 1) (cfg.c k t i)
    let m' := (cfg.midpoint k t i - cfg.blockOrigin k s ip 0) / H
    |c' 1| ≤ 4 * cfg.K k ^ 4 ∧ |c' 0 + m' * c' 1| ≤ 4 * cfg.K k ^ 4 ∧
      |c' 3 + c' 0 + m' * c' 1| ≤ (4 * cfg.K k ^ 4) * h' ∧
      |c' 4 - m'| ≤ (4 * cfg.K k ^ 4) * h' ∧
      ∀ q ∈ horizontalTrueBox (cfg.c k t i) (cfg.midpoint k t i)
          (cfg.timeLength k t) (cfg.K k ^ 2),
        cfg.parentFrame k s ip q ∈ horizontalTrueBox c' m' h' (4 * cfg.K k ^ 4) := by
  have hK := h.subpower.1 k
  have hKsq : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  have hc := child.native_box_center_bounds h i
  have hbox := normalized_box_bounds (cfg.timeLength k s)
    (cfg.blockOrigin k s ip 0) (cfg.blockOrigin k s ip 1) (cfg.blockOrigin k s ip 2)
    (cfg.c k s ip 1) (cfg.midpoint k t i) (cfg.timeLength k t) (cfg.K k ^ 2)
    (cfg.c k t i) (nativeHorizontalLine (cfg.b k p.1) p.2)
    (cfg.timeLength_pos k s) (cfg.timeLength_pos k t).le hrel (by nlinarith)
    ((parent.coefficient_bound ip 1).trans hKsq) ((child.coefficient_bound i 1).trans hKsq)
    (hc.1.trans (mul_le_mul_of_nonneg_right hKsq (cfg.timeLength_pos k t).le))
    (hc.2.trans (mul_le_mul_of_nonneg_right hKsq (cfg.timeLength_pos k t).le))
    (child.native_point_in_true_box h i p.1 hi hit)
    (parent.framedPoint_bounds h ip hp hpt).2.1
  rw [show 4 * (cfg.K k ^ 2) ^ 2 = 4 * cfg.K k ^ 4 by ring] at hbox
  exact hbox

/-- The original prior's almost-everywhere coefficient bounds also hold
for the incidence law and for every dominated residual. -/
theorem Valid.ae_base_coefficients {cfg : Data α} (h : cfg.Valid) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k,
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
  have hprior := (h.basic k).2.2.2.2.2.2.2.2.1
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := cfg.ν k) (ν := (volume : Measure ℝ))).ae hprior
  exact ae_mono (h.basic k).2.2.2.1 (Measure.ae_smul_measure hprod (ENNReal.ofReal (cfg.K k)))

/-- All contact-coordinate signals used by the finite tables are measurable
on the original source. -/
theorem measurable_framedPoint {cfg : Data α} (h : cfg.Valid)
    (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) : Measurable (cfg.framedPoint k s i) := by
  have hb : Measurable (cfg.b k) := (h.basic k).1
  unfold framedPoint parentFrame horizontalFrame nativeHorizontalLine
  fun_prop

end Data

end

end Submission.Obl.k4_critical_intercept_concentration
