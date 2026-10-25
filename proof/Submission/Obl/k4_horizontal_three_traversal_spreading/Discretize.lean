-- Adapted from the same LOT tree, o201, session x0702, commit 8598cc6c87975aa470bd15a311478d45160361da
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/LowerCount/Discretize.lean
import Mathlib

/-! # Discretizing a continuous retained law

Trajectories carry normalized parameters `(Z0, Y0, v)`; an exact horizontal
line is `t ↦ (t, Z0 + v t, Y0 - Z0 t)` in normalized block coordinates.  An
event is a pair (arm code, time code): the arm code bins `Z0`, `Y0` at width
`δ` and records the palette bin of `v` and the intercept bin; the time code
bins normalized time at width `1 / T`.  Representative points lie on the exact
line of the bin centres, so horizontal traversals between them are exact. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Discretize

open Finset MeasureTheory

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The normalized position of an incidence on its exact horizontal line. -/
def idealPoint (Z0 Y0 v : α → ℝ) (tn : α × ℝ → ℝ) (p : α × ℝ) : Fin 3 → ℝ :=
  ![tn p, Z0 p.1 + v p.1 * tn p, Y0 p.1 - Z0 p.1 * tn p]

/-- The base cell of side `ω` containing a point. -/
def cellIdx (ω : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℤ := fun i => ⌊x i / ω⌋

/-- The centre of a base cell of side `ω`. -/
def cellCenter (ω : ℝ) (Q : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => ((Q i : ℝ) + 1 / 2) * ω

/-- The arm code of a trajectory. -/
def armCode (δ : ℝ) (Z0 Y0 : α → ℝ) (vb cb : α → ℤ) (l : α) : Fin 4 → ℤ :=
  ![⌊Z0 l / δ⌋, ⌊Y0 l / δ⌋, vb l, cb l]

/-- The time code of an incidence. -/
def timeCode (T : ℕ) (tn : α × ℝ → ℝ) (p : α × ℝ) : ℤ := ⌊(T : ℝ) * tn p⌋

/-- The centre of the time cell with code `t`. -/
def timeCenter (T : ℕ) (t : ℤ) : ℝ := ((t : ℝ) + 1 / 2) / T

/-- The representative point of an event: the exact line of the bin centres,
at the centre of the time cell. -/
def repPoint (δ wv : ℝ) (T : ℕ) (a : Fin 4 → ℤ) (t : ℤ) : Fin 3 → ℝ :=
  ![timeCenter T t, ((a 0 : ℝ) + 1 / 2) * δ + ((a 2 : ℝ) + 1 / 2) * wv * timeCenter T t,
    ((a 1 : ℝ) + 1 / 2) * δ - ((a 0 : ℝ) + 1 / 2) * δ * timeCenter T t]

theorem abs_sub_floor_center {x ω : ℝ} (hω : 0 < ω) :
    |x - ((⌊x / ω⌋ : ℝ) + 1 / 2) * ω| ≤ ω / 2 := by
  have h1 := Int.floor_le (x / ω)
  have h2 := Int.lt_floor_add_one (x / ω)
  have h1' : (⌊x / ω⌋ : ℝ) * ω ≤ x := by
    have := mul_le_mul_of_nonneg_right h1 hω.le
    rwa [div_mul_cancel₀ x hω.ne'] at this
  have h2' : x < ((⌊x / ω⌋ : ℝ) + 1) * ω := by
    have := mul_lt_mul_of_pos_right h2 hω
    rwa [div_mul_cancel₀ x hω.ne'] at this
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_floor_sub_le_one {x y ω : ℝ} (hω : 0 < ω) (hxy : |x - y| ≤ ω) :
    |(⌊x / ω⌋ : ℝ) - ⌊y / ω⌋| ≤ 1 := by
  have hdiv : |x / ω - y / ω| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hω, div_le_one hω]
    exact hxy
  have hx1 := Int.floor_le (x / ω)
  have hx2 := Int.lt_floor_add_one (x / ω)
  have hy1 := Int.floor_le (y / ω)
  have hy2 := Int.lt_floor_add_one (y / ω)
  rw [abs_le] at hdiv ⊢
  have hlt1 : (⌊x / ω⌋ : ℝ) - ⌊y / ω⌋ < 2 := by linarith
  have hlt2 : -2 < (⌊x / ω⌋ : ℝ) - ⌊y / ω⌋ := by linarith
  have hint1 : ⌊x / ω⌋ - ⌊y / ω⌋ < 2 := by exact_mod_cast hlt1
  have hint2 : -2 < ⌊x / ω⌋ - ⌊y / ω⌋ := by exact_mod_cast hlt2
  have hle1 : ⌊x / ω⌋ - ⌊y / ω⌋ ≤ 1 := by omega
  have hle2 : -1 ≤ ⌊x / ω⌋ - ⌊y / ω⌋ := by omega
  constructor
  · exact_mod_cast hle2
  · exact_mod_cast hle1

/-- A point and its rounded representative.  Each coordinate differs by at most
`δ + K₀ / (2T) + wv / 2 + 1 / (2T)`. -/
theorem repPoint_close {Z0 Y0 v tn δ wv K₀ : ℝ} {T : ℕ} {vbin c : ℤ}
    (hT : 0 < T) (hδ : 0 < δ) (hwv : 0 < wv)
    (htn : tn ∈ Set.Icc (0 : ℝ) 1) (htn1 : tn < 1)
    (hZ : |Z0| ≤ K₀) (hv : |v| ≤ K₀)
    (hvb1 : (vbin : ℝ) * wv ≤ v) (hvb2 : v < ((vbin : ℝ) + 1) * wv) :
    ∀ i, |repPoint δ wv T ![⌊Z0 / δ⌋, ⌊Y0 / δ⌋, vbin, c] ⌊(T : ℝ) * tn⌋ i -
      ![tn, Z0 + v * tn, Y0 - Z0 * tn] i| ≤ δ + K₀ / (2 * T) + wv / 2 + 1 / (2 * T) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans hZ
  -- time
  set tc := timeCenter T ⌊(T : ℝ) * tn⌋ with htc
  have ht : |tc - tn| ≤ 1 / (2 * T) := by
    have h1 := Int.floor_le ((T : ℝ) * tn)
    have h2 := Int.lt_floor_add_one ((T : ℝ) * tn)
    rw [htc, timeCenter, abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hTpos]
      have : (1 : ℝ) / (2 * T) * T = 1 / 2 := by field_simp
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hTpos]
      have : (1 : ℝ) / (2 * T) * T = 1 / 2 := by field_simp
      nlinarith
  have htc0 : 0 ≤ tc := by
    rw [htc, timeCenter]
    apply div_nonneg _ hTpos.le
    have : (0 : ℝ) ≤ ⌊(T : ℝ) * tn⌋ := by
      exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hTpos.le htn.1)
    linarith
  have htc1 : tc ≤ 1 := by
    rw [htc, timeCenter, div_le_one hTpos]
    have h1 := Int.floor_le ((T : ℝ) * tn)
    have hlt : ((⌊(T : ℝ) * tn⌋ : ℤ) : ℝ) < T := lt_of_le_of_lt h1 (by nlinarith)
    have hint : ⌊(T : ℝ) * tn⌋ < (T : ℤ) := by exact_mod_cast hlt
    have hle : ⌊(T : ℝ) * tn⌋ + 1 ≤ (T : ℤ) := hint
    have : ((⌊(T : ℝ) * tn⌋ : ℝ) + 1) ≤ T := by exact_mod_cast hle
    linarith
  have htcabs : |tc| ≤ 1 := abs_le.mpr ⟨by linarith, htc1⟩
  have htnabs : |tn| ≤ 1 := abs_le.mpr ⟨by linarith [htn.1], htn.2⟩
  -- bins
  have hZc : |((⌊Z0 / δ⌋ : ℝ) + 1 / 2) * δ - Z0| ≤ δ / 2 := by
    rw [abs_sub_comm]; exact abs_sub_floor_center hδ
  have hYc : |((⌊Y0 / δ⌋ : ℝ) + 1 / 2) * δ - Y0| ≤ δ / 2 := by
    rw [abs_sub_comm]; exact abs_sub_floor_center hδ
  have hvc : |((vbin : ℝ) + 1 / 2) * wv - v| ≤ wv / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  have hpos1 : 0 ≤ K₀ / (2 * T) := by positivity
  have hpos2 : (0 : ℝ) ≤ 1 / (2 * (T : ℝ)) := by positivity
  intro i
  fin_cases i
  · show |tc - tn| ≤ _
    linarith [hδ.le, hwv.le]
  · set Zc := ((⌊Z0 / δ⌋ : ℝ) + 1 / 2) * δ
    set vc := ((vbin : ℝ) + 1 / 2) * wv
    show |Zc + vc * tc - (Z0 + v * tn)| ≤ _
    have hsplit : Zc + vc * tc - (Z0 + v * tn) =
        (Zc - Z0) + (vc - v) * tc + v * (tc - tn) := by ring
    rw [hsplit]
    have h1 : |(vc - v) * tc| ≤ wv / 2 := by
      rw [abs_mul]
      calc |vc - v| * |tc| ≤ wv / 2 * 1 :=
            mul_le_mul hvc htcabs (abs_nonneg _) (by positivity)
        _ = wv / 2 := by ring
    have h2 : |v * (tc - tn)| ≤ K₀ / (2 * T) := by
      rw [abs_mul]
      calc |v| * |tc - tn| ≤ K₀ * (1 / (2 * T)) :=
            mul_le_mul hv ht (abs_nonneg _) hK₀
        _ = K₀ / (2 * T) := by ring
    calc |(Zc - Z0) + (vc - v) * tc + v * (tc - tn)| ≤
          |Zc - Z0| + |(vc - v) * tc| + |v * (tc - tn)| := abs_add_three _ _ _
      _ ≤ δ / 2 + wv / 2 + K₀ / (2 * T) := by linarith
      _ ≤ _ := by linarith
  · set Zc := ((⌊Z0 / δ⌋ : ℝ) + 1 / 2) * δ
    set Yc := ((⌊Y0 / δ⌋ : ℝ) + 1 / 2) * δ
    show |Yc - Zc * tc - (Y0 - Z0 * tn)| ≤ _
    have hsplit : Yc - Zc * tc - (Y0 - Z0 * tn) =
        (Yc - Y0) - (Zc - Z0) * tc - Z0 * (tc - tn) := by ring
    rw [hsplit]
    have h1 : |(Zc - Z0) * tc| ≤ δ / 2 := by
      rw [abs_mul]
      calc |Zc - Z0| * |tc| ≤ δ / 2 * 1 :=
            mul_le_mul hZc htcabs (abs_nonneg _) (by positivity)
        _ = δ / 2 := by ring
    have h2 : |Z0 * (tc - tn)| ≤ K₀ / (2 * T) := by
      rw [abs_mul]
      calc |Z0| * |tc - tn| ≤ K₀ * (1 / (2 * T)) :=
            mul_le_mul hZ ht (abs_nonneg _) hK₀
        _ = K₀ / (2 * T) := by ring
    calc |(Yc - Y0) - (Zc - Z0) * tc - Z0 * (tc - tn)| ≤
          |Yc - Y0| + |(Zc - Z0) * tc| + |Z0 * (tc - tn)| := by
          have := abs_sub (Yc - Y0 - (Zc - Z0) * tc) (Z0 * (tc - tn))
          have := abs_sub (Yc - Y0) ((Zc - Z0) * tc)
          linarith
      _ ≤ δ / 2 + δ / 2 + K₀ / (2 * T) := by linarith
      _ ≤ _ := by linarith [hwv.le]

theorem sum_toReal_measure_eq {β ι : Type*} [MeasurableSpace β] (μ : Measure β)
    [IsFiniteMeasure μ] (s : Finset ι) (f : ι → Set β) (hf : ∀ i, MeasurableSet (f i))
    (hd : Set.PairwiseDisjoint (↑s) f) :
    ∑ i ∈ s, (μ (f i)).toReal = (μ (⋃ i ∈ s, f i)).toReal := by
  rw [measure_biUnion_finset hd (fun i _ => hf i),
    ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]

theorem measurable_armCode {δ : ℝ} {Z0 Y0 : α → ℝ} {vb cb : α → ℤ}
    (hZ0 : Measurable Z0) (hY0 : Measurable Y0) (hvb : Measurable vb) (hcb : Measurable cb) :
    Measurable (armCode δ Z0 Y0 vb cb) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  · exact Int.measurable_floor.comp (hZ0.div_const δ)
  · exact Int.measurable_floor.comp (hY0.div_const δ)
  · exact hvb
  · exact hcb

theorem measurable_timeCode {T : ℕ} {tn : α × ℝ → ℝ} (htn : Measurable tn) :
    Measurable (timeCode T tn) :=
  Int.measurable_floor.comp (htn.const_mul _)

/-- The event of an (arm code, time code) pair. -/
def eventSet (δ : ℝ) (Z0 Y0 : α → ℝ) (vb cb : α → ℤ) (T : ℕ) (tn : α × ℝ → ℝ)
    (a : Fin 4 → ℤ) (t : ℤ) : Set (α × ℝ) :=
  {p | armCode δ Z0 Y0 vb cb p.1 = a ∧ timeCode T tn p = t}

theorem measurableSet_eventSet {δ : ℝ} {Z0 Y0 : α → ℝ} {vb cb : α → ℤ} {T : ℕ}
    {tn : α × ℝ → ℝ} (hZ0 : Measurable Z0) (hY0 : Measurable Y0) (hvb : Measurable vb)
    (hcb : Measurable cb) (htn : Measurable tn) (a : Fin 4 → ℤ) (t : ℤ) :
    MeasurableSet (eventSet δ Z0 Y0 vb cb T tn a t) := by
  have h1 : MeasurableSet {p : α × ℝ | armCode δ Z0 Y0 vb cb p.1 = a} :=
    ((measurable_armCode hZ0 hY0 hvb hcb).comp measurable_fst) (measurableSet_singleton a)
  have h2 : MeasurableSet {p : α × ℝ | timeCode T tn p = t} :=
    (measurable_timeCode htn) (measurableSet_singleton t)
  exact h1.inter h2

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Discretize
