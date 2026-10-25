import Submission.Lib.K4ContinuousKakeya

set_option linter.unusedVariables false

/-!
# Geometry of the frozen trajectories for the velocity graph

Incidences `p = ((index, coefficients), t)` of o092's data have physical point
`physOf p = (t, y_l(t), x_l(t))` (`y = l₀ + t l₁`, `x = l₂ + t l₃ + t² l₄`), lifted velocity
`liftOf p = (1, l₁, l₃ + 2 t l₄)` and unit lifted direction `unitOf p`. Cubes of side `w` are
indexed by `cellIdx w` (the floor of the coordinates over `w`, as in o092's grid maps). This file
gives the facts the Kakeya contradiction (`bad_mass_le`) needs: cube diameters and time sections,
tangent lines with bounded base points (`tangentBase`, `tangentDir`), tube containment of a cube
about the tangent line of any of its incidences (`mem_tube_tangent_of_cell`), closeness of
directions (`norm_unitOf_sub_tangentDir_le`), and the number of coarse cubes a trajectory visits
(`card_visited_le`).
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Submission.Lib.K4ContinuousKakeya
open scoped ENNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- An incidence of the frozen data: a trajectory `l = (index, coefficients)` and a time. -/
abbrev Inc := (ℕ × (Fin 5 → ℝ)) × ℝ

/-- Physical point `(t, y_l(t), x_l(t))` of an incidence. -/
def physOf (p : Inc) : E3 := physPoint (p.1.2 0) (p.1.2 1) (p.1.2 2) (p.1.2 3) (p.1.2 4) p.2

/-- Lifted velocity `(1, V_l, x_l'(t))` of an incidence. -/
def liftOf (p : Inc) : E3 := liftVel (p.1.2 1) (p.1.2 3) (p.1.2 4) p.2

/-- Unit lifted direction of an incidence. -/
def unitOf (p : Inc) : E3 := ‖liftOf p‖⁻¹ • liftOf p

lemma physOf_apply (p : Inc) (e : Fin 3) :
    physOf p e = (![p.2, p.1.2 0 + p.2 * p.1.2 1,
      p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4] : Fin 3 → ℝ) e := by
  fin_cases e <;> simp [physOf, physPoint] <;> ring

lemma continuous_physOf : Continuous physOf := by
  unfold physOf physPoint
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma continuous_liftOf : Continuous liftOf := by
  unfold liftOf liftVel
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma norm_unitOf (p : Inc) : ‖unitOf p‖ = 1 := by
  unfold unitOf
  exact norm_smul_inv_norm (norm_pos_iff.mp (lt_of_lt_of_le one_pos (one_le_norm_liftVel _ _ _ _)))

lemma continuous_unitOf : Continuous unitOf := by
  unfold unitOf
  have hinv : Continuous fun p => ‖liftOf p‖⁻¹ :=
    Continuous.inv₀ (continuous_norm.comp continuous_liftOf) (fun p =>
      (lt_of_lt_of_le one_pos (one_le_norm_liftVel _ _ _ _)).ne')
  exact hinv.smul continuous_liftOf

/-- The index of the half-open cube of side `w` containing a point. -/
def cellIdx (w : ℝ) (x : E3) : Fin 3 → ℤ := fun e => ⌊x e / w⌋

/-- The half-open cube of side `w` with index `q`. -/
def cellSet (w : ℝ) (q : Fin 3 → ℤ) : Set E3 := {x | cellIdx w x = q}

lemma measurable_cellIdx (w : ℝ) : Measurable (cellIdx w) := by
  apply measurable_pi_iff.mpr
  intro e
  have h : Measurable fun x : E3 => x e := (EuclideanSpace.proj (𝕜 := ℝ) e).continuous.measurable
  exact (h.div_const w).floor

lemma measurableSet_cellSet (w : ℝ) (q : Fin 3 → ℤ) : MeasurableSet (cellSet w q) :=
  measurable_cellIdx w (measurableSet_singleton q)

lemma mem_cellSet_iff {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} {x : E3} :
    x ∈ cellSet w q ↔ ∀ e, (q e : ℝ) * w ≤ x e ∧ x e < (q e + 1) * w := by
  simp only [cellSet, Set.mem_ofPred_eq, cellIdx, funext_iff]
  apply forall_congr'
  intro e
  rw [Int.floor_eq_iff, le_div_iff₀ hw, div_lt_iff₀ hw]

/-- Points of the same half-open cube of side `w` are within `2 w`. -/
lemma norm_sub_lt_of_mem_cellSet {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} {x z : E3}
    (hx : x ∈ cellSet w q) (hz : z ∈ cellSet w q) : ‖x - z‖ < 2 * w := by
  rw [mem_cellSet_iff hw] at hx hz
  have hcoord : ∀ e, |(x - z) e| < w := by
    intro e
    have h1 := hx e; have h2 := hz e
    simp only [PiLp.sub_apply]
    rw [abs_lt]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hsq : ‖x - z‖ ^ 2 < (2 * w) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun e _ => sq_nonneg _),
      Fin.sum_univ_three]
    have h0 := hcoord 0; have h1 := hcoord 1; have h2 := hcoord 2
    have e0 : ‖(x - z) 0‖ ^ 2 < w ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]; nlinarith [abs_nonneg ((x - z) 0), sq_abs ((x - z) 0)]
    have e1 : ‖(x - z) 1‖ ^ 2 < w ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]; nlinarith [abs_nonneg ((x - z) 1), sq_abs ((x - z) 1)]
    have e2 : ‖(x - z) 2‖ ^ 2 < w ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]; nlinarith [abs_nonneg ((x - z) 2), sq_abs ((x - z) 2)]
    nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The time coordinate of a point of `cellSet w q` lies in `[q₀ w, (q₀ + 1) w)`. -/
lemma time_mem_of_mem_cellSet {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} {p : Inc}
    (h : physOf p ∈ cellSet w q) : (q 0 : ℝ) * w ≤ p.2 ∧ p.2 < (q 0 + 1) * w := by
  have := (mem_cellSet_iff hw).mp h 0
  simpa [physOf_apply] using this

/-- Time sections of a cube of side `w` have length at most `w`. -/
lemma volume_time_section_le {w : ℝ} (hw : 0 < w) (q : Fin 3 → ℤ) (l : ℕ × (Fin 5 → ℝ)) :
    volume {t : ℝ | physOf (l, t) ∈ cellSet w q} ≤ ENNReal.ofReal w := by
  calc volume {t : ℝ | physOf (l, t) ∈ cellSet w q}
      ≤ volume (Set.Ico ((q 0 : ℝ) * w) ((q 0 + 1) * w)) := by
        apply measure_mono
        intro t ht
        exact time_mem_of_mem_cellSet hw ht
    _ = ENNReal.ofReal w := by rw [Real.volume_Ico]; ring_nf

/-- The tangent line of a trajectory at time `c`: base point, clamped to `0` for trajectories
with a coefficient above `H` so that base points are bounded. -/
def tangentBase (H c : ℝ) (l : ℕ × (Fin 5 → ℝ)) : E3 :=
  if ∀ e, |l.2 e| ≤ H then physOf (l, c) else 0

/-- The unit direction of the tangent line of a trajectory at time `c`. -/
def tangentDir (c : ℝ) (l : ℕ × (Fin 5 → ℝ)) : E3 := unitOf (l, c)

lemma norm_tangentDir (c : ℝ) (l : ℕ × (Fin 5 → ℝ)) : ‖tangentDir c l‖ = 1 := norm_unitOf _

lemma measurable_tangentDir (c : ℝ) : Measurable (tangentDir c) :=
  (continuous_unitOf.comp (Continuous.prodMk_left c)).measurable

lemma measurable_tangentBase (H c : ℝ) : Measurable (tangentBase H c) := by
  unfold tangentBase
  apply Measurable.ite _ ((continuous_physOf.comp (Continuous.prodMk_left c)).measurable)
    measurable_const
  have : {l : ℕ × (Fin 5 → ℝ) | ∀ e, |l.2 e| ≤ H} = ⋂ e, {l | |l.2 e| ≤ H} := by
    ext l; simp
  rw [this]
  exact MeasurableSet.iInter fun e => measurableSet_le
    ((measurable_pi_apply e).comp measurable_snd).abs measurable_const

lemma norm_physOf_le {H : ℝ} {p : Inc} (hH : ∀ e, |p.1.2 e| ≤ H) (ht : |p.2| ≤ 2) :
    ‖physOf p‖ ≤ 2 + 10 * H := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  calc ‖physOf p‖ ≤ |physOf p 0| + |physOf p 1| + |physOf p 2| := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
        simp only [Real.norm_eq_abs, sq_abs]
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [abs_nonneg (physOf p 0), abs_nonneg (physOf p 1), abs_nonneg (physOf p 2),
          sq_abs (physOf p 0), sq_abs (physOf p 1), sq_abs (physOf p 2)]
    _ ≤ 2 + (H + 2 * H) + (H + 2 * H + 4 * H) := by
        simp only [physOf_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        have h0 := hH 0; have h1 := hH 1; have h2 := hH 2; have h3 := hH 3; have h4 := hH 4
        have ht0 : 0 ≤ |p.2| := abs_nonneg _
        have t1 : |p.2 * p.1.2 1| ≤ 2 * H := by
          rw [abs_mul]; nlinarith [abs_nonneg (p.1.2 1)]
        have t2 : |p.2 * p.1.2 3| ≤ 2 * H := by
          rw [abs_mul]; nlinarith [abs_nonneg (p.1.2 3)]
        have t3 : |p.2 ^ 2 * p.1.2 4| ≤ 4 * H := by
          rw [abs_mul, abs_pow]
          have hsq : |p.2| ^ 2 ≤ 4 := by nlinarith
          nlinarith [abs_nonneg (p.1.2 4), sq_nonneg |p.2|]
        have e1 : |p.1.2 0 + p.2 * p.1.2 1| ≤ H + 2 * H :=
          (abs_add_le _ _).trans (by linarith)
        have e2 : |p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4| ≤ H + 2 * H + 4 * H :=
          (abs_add_three _ _ _).trans (by linarith)
        linarith
    _ = 2 + 10 * H := by ring

lemma norm_tangentBase_le {H c : ℝ} (hH0 : 0 ≤ H) (hc : |c| ≤ 2) (l : ℕ × (Fin 5 → ℝ)) :
    ‖tangentBase H c l‖ ≤ 2 + 10 * H := by
  unfold tangentBase
  split_ifs with h
  · exact norm_physOf_le h hc
  · simp; positivity

/-- Points of the cube of an incidence lie in the tube about the incidence's tangent line at a
nearby time `c`. -/
lemma mem_tube_tangent_of_cell {H w T₀ c r : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} {p : Inc}
    (hH : ∀ e, |p.1.2 e| ≤ H) (hp : physOf p ∈ cellSet w q) (hT : |p.2 - c| ≤ T₀)
    (hr : 2 * w + H * T₀ ^ 2 ≤ r) {x : E3} (hx : x ∈ cellSet w q) :
    x ∈ tube r (tangentBase H c p.1) (tangentDir c p.1) := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  set L : E3 := liftOf (p.1, c) with hL
  have hLpos : 0 < ‖L‖ := lt_of_lt_of_le one_pos (one_le_norm_liftVel _ _ _ _)
  have hbase : tangentBase H c p.1 = physOf (p.1, c) := by
    simp [tangentBase, hH]
  rw [hbase]
  apply Metric.mem_thickening_iff.mpr
  refine ⟨physOf (p.1, c) + ((p.2 - c) * ‖L‖) • tangentDir c p.1, ⟨_, rfl⟩, ?_⟩
  have hz : physOf (p.1, c) + ((p.2 - c) * ‖L‖) • tangentDir c p.1 =
      physOf (p.1, c) + (p.2 - c) • L := by
    rw [tangentDir, unitOf, smul_smul, mul_assoc, mul_inv_cancel₀ hLpos.ne', mul_one]
  rw [hz, dist_eq_norm]
  have htan : ‖physOf p - (physOf (p.1, c) + (p.2 - c) • L)‖ ≤ H * T₀ ^ 2 := by
    have := norm_physPoint_sub_tangent (p.1.2 0) (p.1.2 1) (p.1.2 2) (p.1.2 3) (p.1.2 4) c p.2
    simp only [physOf, hL, liftOf] at this ⊢
    rw [this]
    have hT2 : (p.2 - c) ^ 2 ≤ T₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hT 2
    exact mul_le_mul (hH 4) hT2 (sq_nonneg _) hH0
  calc ‖x - (physOf (p.1, c) + (p.2 - c) • L)‖
      ≤ ‖x - physOf p‖ + ‖physOf p - (physOf (p.1, c) + (p.2 - c) • L)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < 2 * w + H * T₀ ^ 2 := by
        have := norm_sub_lt_of_mem_cellSet hw hx hp
        linarith
    _ ≤ r := hr

/-- The unit lifted direction of an incidence is within `4 H |t - c|` of its tangent direction at
time `c`. -/
lemma norm_unitOf_sub_tangentDir_le {H c : ℝ} {p : Inc} (hH : ∀ e, |p.1.2 e| ≤ H) :
    ‖unitOf p - tangentDir c p.1‖ ≤ 4 * H * |p.2 - c| := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  unfold unitOf tangentDir
  calc ‖‖liftOf p‖⁻¹ • liftOf p - unitOf (p.1, c)‖
      = ‖‖liftOf p‖⁻¹ • liftOf p - ‖liftOf (p.1, c)‖⁻¹ • liftOf (p.1, c)‖ := rfl
    _ ≤ 2 * ‖liftOf p - liftOf (p.1, c)‖ :=
        norm_normalize_sub_le (one_le_norm_liftVel _ _ _ _) (one_le_norm_liftVel _ _ _ _)
    _ = 2 * (2 * |p.1.2 4| * |p.2 - c|) := by
        rw [liftOf, liftOf, norm_liftVel_sub]
    _ ≤ 4 * H * |p.2 - c| := by
        have := hH 4
        nlinarith [abs_nonneg (p.2 - c)]

lemma abs_floor_sub_floor_lt (a b : ℝ) : |((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| < |a - b| + 1 := by
  have ha := Int.floor_le a; have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b; have hb' := Int.lt_floor_add_one b
  push_cast
  rw [abs_lt]
  constructor
  · have := neg_abs_le (a - b); linarith
  · have := le_abs_self (a - b); linarith

lemma int_le_of_abs_lt {z : ℤ} {X : ℝ} {A : ℕ} (h : |(z : ℝ)| < X) (hX : X ≤ A) :
    z ∈ Finset.Icc (-(A : ℤ)) A := by
  rw [Finset.mem_Icc]
  have h1 : |(z : ℝ)| < A := lt_of_lt_of_le h hX
  rw [abs_lt] at h1
  constructor
  · have : (-(A : ℝ)) < z := h1.1
    exact_mod_cast this.le
  · exact_mod_cast h1.2.le

/-- A trajectory with coefficients at most `H` visits at most
`(⌊1/w₀⌋ + 1)(2(⌈H⌉ + 1) + 1)(2(⌈3H⌉ + 1) + 1)` cubes of side `w₀` during `[0, 1]`. -/
lemma card_visited_le {w₀ H : ℝ} (hw₀ : 0 < w₀) (l : ℕ × (Fin 5 → ℝ))
    (hl : ∀ e, |l.2 e| ≤ H) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ Q ∈ S, ∃ t ∈ Set.Icc (0 : ℝ) 1, cellIdx w₀ (physOf (l, t)) = Q) :
    S.card ≤ (⌊1 / w₀⌋₊ + 1) * (2 * (⌈H⌉₊ + 1) + 1) * (2 * (⌈3 * H⌉₊ + 1) + 1) := by
  classical
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hl 0)
  set A : ℕ := ⌈H⌉₊ + 1
  set A' : ℕ := ⌈3 * H⌉₊ + 1
  set M : ℕ := ⌊1 / w₀⌋₊
  let yv : ℝ → ℝ := fun t => l.2 0 + t * l.2 1
  let xv : ℝ → ℝ := fun t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4
  let f : (Fin 3 → ℤ) → ℤ × ℤ × ℤ := fun Q =>
    (Q 0, Q 1 - ⌊yv (Q 0 * w₀) / w₀⌋, Q 2 - ⌊xv (Q 0 * w₀) / w₀⌋)
  have hinj : Set.InjOn f S := by
    intro Q _ Q' _ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    funext e
    fin_cases e
    · exact h0
    · simp only [h0] at h1; simpa using h1
    · simp only [h0] at h2; simpa using h2
  have hmaps : ∀ Q ∈ S, f Q ∈ (Finset.Icc (0 : ℤ) M) ×ˢ (Finset.Icc (-(A : ℤ)) A) ×ˢ
      (Finset.Icc (-(A' : ℤ)) A') := by
    intro Q hQ
    obtain ⟨t, ⟨ht0, ht1⟩, hQt⟩ := hS Q hQ
    have hQe : ∀ e, Q e = ⌊physOf (l, t) e / w₀⌋ := fun e => by rw [← hQt]; rfl
    have hq0 : Q 0 = ⌊t / w₀⌋ := by rw [hQe 0]; simp [physOf_apply]
    have hfl := Int.floor_le (t / w₀); have hfl' := Int.lt_floor_add_one (t / w₀)
    set t₀ : ℝ := (Q 0 : ℝ) * w₀ with ht₀
    have ht₀le : t₀ ≤ t := by
      rw [ht₀, hq0]; have := (le_div_iff₀ hw₀).mp hfl; linarith
    have htlt : t < t₀ + w₀ := by
      rw [ht₀, hq0]; have := (div_lt_iff₀ hw₀).mp hfl'; nlinarith
    have ht₀0 : 0 ≤ t₀ := by
      rw [ht₀, hq0]
      have : (0 : ℤ) ≤ ⌊t / w₀⌋ := Int.floor_nonneg.mpr (div_nonneg ht0 hw₀.le)
      exact mul_nonneg (by exact_mod_cast this) hw₀.le
    have hdt : |t - t₀| ≤ w₀ := by rw [abs_le]; constructor <;> linarith
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · simp only [f, Finset.mem_Icc]
      rw [hq0]
      refine ⟨Int.floor_nonneg.mpr (div_nonneg ht0 hw₀.le), ?_⟩
      have : ⌊t / w₀⌋ ≤ ⌊1 / w₀⌋ := Int.floor_mono (div_le_div_of_nonneg_right ht1 hw₀.le)
      have hM : ((⌊1 / w₀⌋₊ : ℕ) : ℤ) = ⌊1 / w₀⌋ :=
        Int.natCast_floor_eq_floor (div_nonneg zero_le_one hw₀.le)
      rw [hM]; exact this
    · simp only [f]
      have hy : Q 1 = ⌊yv t / w₀⌋ := by rw [hQe 1]; simp [physOf_apply, yv]
      rw [hy]
      apply int_le_of_abs_lt (abs_floor_sub_floor_lt _ _)
      have : |yv t / w₀ - yv t₀ / w₀| ≤ H := by
        rw [← sub_div, abs_div, abs_of_pos hw₀, div_le_iff₀ hw₀]
        have : yv t - yv t₀ = (t - t₀) * l.2 1 := by simp only [yv]; ring
        rw [this, abs_mul]
        calc |t - t₀| * |l.2 1| ≤ w₀ * H := mul_le_mul hdt (hl 1) (abs_nonneg _) hw₀.le
          _ = H * w₀ := by ring
      have hc := Nat.le_ceil H
      push_cast [A]
      linarith
    · simp only [f]
      have hx : Q 2 = ⌊xv t / w₀⌋ := by rw [hQe 2]; simp [physOf_apply, xv]
      rw [hx]
      apply int_le_of_abs_lt (abs_floor_sub_floor_lt _ _)
      have : |xv t / w₀ - xv t₀ / w₀| ≤ 3 * H := by
        rw [← sub_div, abs_div, abs_of_pos hw₀, div_le_iff₀ hw₀]
        have : xv t - xv t₀ = (t - t₀) * (l.2 3 + (t + t₀) * l.2 4) := by simp only [xv]; ring
        rw [this, abs_mul]
        have hsum : |l.2 3 + (t + t₀) * l.2 4| ≤ 3 * H := by
          calc |l.2 3 + (t + t₀) * l.2 4| ≤ |l.2 3| + |t + t₀| * |l.2 4| := by
                rw [← abs_mul]; exact abs_add_le _ _
            _ ≤ H + 2 * H := by
                have h1 := hl 3; have h2 := hl 4
                have htt : |t + t₀| ≤ 2 := by
                  rw [abs_le]; constructor <;> linarith
                nlinarith [abs_nonneg (t + t₀), abs_nonneg (l.2 4)]
            _ = 3 * H := by ring
        calc |t - t₀| * |l.2 3 + (t + t₀) * l.2 4| ≤ w₀ * (3 * H) :=
              mul_le_mul hdt hsum (abs_nonneg _) hw₀.le
          _ = 3 * H * w₀ := by ring
      have hc := Nat.le_ceil (3 * H)
      push_cast [A']
      linarith
  calc S.card ≤ ((Finset.Icc (0 : ℤ) M) ×ˢ (Finset.Icc (-(A : ℤ)) A) ×ˢ
        (Finset.Icc (-(A' : ℤ)) A')).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = (M + 1) * (2 * A + 1) * (2 * A' + 1) := by
        simp only [Finset.card_product, Int.card_Icc]
        have e1 : ((M : ℤ) + 1 - 0) = ((M + 1 : ℕ) : ℤ) := by push_cast; ring
        have e2 : ((A : ℤ) + 1 - -(A : ℤ)) = ((2 * A + 1 : ℕ) : ℤ) := by push_cast; ring
        have e3 : ((A' : ℤ) + 1 - -(A' : ℤ)) = ((2 * A' + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e1, e2, e3, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast]
        ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
