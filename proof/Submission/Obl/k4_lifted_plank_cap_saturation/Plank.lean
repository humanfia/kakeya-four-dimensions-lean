import Mathlib

/-!
# Geometry and Tonelli for the heavy lifted plank

A lifted trace `t ↦ (a₀ + t (a₁ - D), D + t a₂)` that stays in a full-time plank with
orthonormal axes `e₁, e₂` and half-widths `u ≤ v` has its endpoint coordinates bounded
by `v`; these recover the coefficients, so `a` lies in the ball of radius `5 v` about
`plankCenter b₀ w`.  The narrow constraint at `t = 0` or `t = 1` accepts a dummy
parameter `D` only in a strip of length at most `8 u`.  Tonelli then bounds the lifted
mass by `8 u` times the label mass of that coefficient ball (`lifted_plank_mass_le`).
-/

namespace Submission.Obl.k4_lifted_plank_cap_saturation

open Set MeasureTheory Metric

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem inner_two (x e : E2) : inner ℝ x e = x 0 * e 0 + x 1 * e 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]

theorem norm_sq_two (e : E2) : ‖e‖ ^ 2 = e 0 ^ 2 + e 1 ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq e

theorem inner_trace (x y t : ℝ) (b₀ w e : E2) :
    inner ℝ (WithLp.toLp 2 ![x, y] - b₀ - t • w) e =
      (x - b₀ 0 - t * w 0) * e 0 + (y - b₀ 1 - t * w 1) * e 1 := by
  rw [inner_two]
  simp

/-- Parseval for an orthonormal pair of the plane. -/
theorem parseval_two (x e₁ e₂ : E2) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (he : inner ℝ e₁ e₂ = 0) :
    x 0 ^ 2 + x 1 ^ 2 = (inner ℝ x e₁) ^ 2 + (inner ℝ x e₂) ^ 2 := by
  have h1 : e₁ 0 ^ 2 + e₁ 1 ^ 2 = 1 := by rw [← norm_sq_two, he₁]; norm_num
  have h2 : e₂ 0 ^ 2 + e₂ 1 ^ 2 = 1 := by rw [← norm_sq_two, he₂]; norm_num
  have h3 : e₁ 0 * e₂ 0 + e₁ 1 * e₂ 1 = 0 := by rw [← inner_two]; exact he
  rw [inner_two, inner_two]
  set a := e₁ 0
  set b := e₁ 1
  set c := e₂ 0
  set d := e₂ 1
  set D := a * d - b * c
  have hc : c = -b * D := by linear_combination a * h3 - c * h1
  have hd : d = a * D := by linear_combination b * h3 - d * h1
  have hD : D ^ 2 = 1 := by
    have : D ^ 2 + (a * c + b * d) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
    rw [h1, h2, h3] at this
    linarith
  rw [hc, hd]
  linear_combination (-(x 0 * b - x 1 * a) ^ 2) * hD - (x 0 ^ 2 + x 1 ^ 2) * h1

/-- A vector of the plane whose two orthonormal components are at most `u ≤ v` has
squared coordinates summing to at most `2 v ^ 2`. -/
theorem coord_sq_le (x e₁ e₂ : E2) (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (he : inner ℝ e₁ e₂ = 0) {u v : ℝ} (huv : u ≤ v) (h1 : |inner ℝ x e₁| ≤ u)
    (h2 : |inner ℝ x e₂| ≤ v) : x 0 ^ 2 + x 1 ^ 2 ≤ 2 * v ^ 2 := by
  rw [parseval_two x e₁ e₂ he₁ he₂ he]
  have h1' : (inner ℝ x e₁) ^ 2 ≤ v ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans huv) 2
  have h2' : (inner ℝ x e₂) ^ 2 ≤ v ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  linarith

/-- The endpoint bounds of one lifted trace in the plank: the coefficients are within
`4 v` of the plank's center, and the narrow constraints at `t = 0` and `t = 1` are affine
in the dummy parameter `D`. -/
theorem plank_endpoint_bounds (a0 a1 a2 D : ℝ) (b₀ w e₁ e₂ : E2) (he₁ : ‖e₁‖ = 1)
    (he₂ : ‖e₂‖ = 1) (he : inner ℝ e₁ e₂ = 0) {u v : ℝ} (huv : u ≤ v)
    (h : ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (WithLp.toLp 2 ![a0 + t * (a1 - D), D + t * a2] - b₀ - t • w) e₁| ≤ u ∧
      |inner ℝ (WithLp.toLp 2 ![a0 + t * (a1 - D), D + t * a2] - b₀ - t • w) e₂| ≤ v) :
    (a0 - b₀ 0) ^ 2 + (a1 - (w 0 + b₀ 1)) ^ 2 + (a2 - w 1) ^ 2 ≤ 16 * v ^ 2 ∧
    |e₁ 1 * D + ((a0 - b₀ 0) * e₁ 0 - b₀ 1 * e₁ 1)| ≤ u ∧
    |(e₁ 1 - e₁ 0) * D + ((a0 + a1 - b₀ 0 - w 0) * e₁ 0 + (a2 - b₀ 1 - w 1) * e₁ 1)| ≤ u := by
  obtain ⟨h0u, h0v⟩ := h 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨h1u, h1v⟩ := h 1 ⟨zero_le_one, le_rfl⟩
  have s0 := coord_sq_le _ e₁ e₂ he₁ he₂ he huv h0u h0v
  have s1 := coord_sq_le _ e₁ e₂ he₁ he₂ he huv h1u h1v
  rw [inner_trace] at h0u h1u
  simp only [PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    smul_eq_mul] at s0 s1
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (a0 - b₀ 0 + (a0 + 1 * (a1 - D) - b₀ 0 - 1 * w 0)),
      sq_nonneg (a0 + 1 * (a1 - D) - b₀ 0 - 1 * w 0 - (D - b₀ 1)),
      sq_nonneg (a0 - b₀ 0 + (D - b₀ 1)),
      sq_nonneg (D + 1 * a2 - b₀ 1 - 1 * w 1 + (D - b₀ 1))]
  · convert h0u using 2; ring
  · convert h1u using 2; ring

/-- A strip `|A D + β| ≤ u` with `1/4 ≤ |A|` has length at most `8 u`. -/
theorem volume_strip_le (A β u : ℝ) (hA : 1 / 4 ≤ |A|) (hu : 0 ≤ u) :
    volume {D : ℝ | |A * D + β| ≤ u} ≤ ENNReal.ofReal (8 * u) := by
  have hA0 : 0 < |A| := lt_of_lt_of_le (by norm_num) hA
  have hA0' : A ≠ 0 := abs_pos.mp hA0
  have hsub : {D : ℝ | |A * D + β| ≤ u} ⊆ closedBall (-β / A) (u / |A|) := by
    intro D hD
    rw [mem_closedBall, Real.dist_eq, le_div_iff₀ hA0]
    have : (D - -β / A) * A = A * D + β := by field_simp; ring
    calc |D - -β / A| * |A| = |A * D + β| := by rw [← abs_mul, this]
      _ ≤ u := hD
  calc volume {D : ℝ | |A * D + β| ≤ u} ≤ volume (closedBall (-β / A) (u / |A|)) :=
        measure_mono hsub
    _ = ENNReal.ofReal (2 * (u / |A|)) := Real.volume_closedBall _ _
    _ ≤ ENNReal.ofReal (8 * u) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_div_assoc', div_le_iff₀ hA0]
        nlinarith

/-- Tonelli for a measurable strip of dummy parameters over a measurable label set. -/
theorem prod_strip_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (S : Set X)
    (hS : MeasurableSet S) (A : ℝ) (β : X → ℝ) (hβ : Measurable β) (hA : 1 / 4 ≤ |A|)
    {u : ℝ} (hu : 0 ≤ u) :
    (ν.prod (volume.restrict (Icc (0 : ℝ) 1)))
        {z : X × ℝ | z.1 ∈ S ∧ |A * z.2 + β z.1| ≤ u} ≤
      ENNReal.ofReal (8 * u) * ν S := by
  have hmeas : MeasurableSet {z : X × ℝ | z.1 ∈ S ∧ |A * z.2 + β z.1| ≤ u} := by
    apply (measurable_fst hS).inter
    exact measurableSet_le (by fun_prop : Measurable fun z : X × ℝ => |A * z.2 + β z.1|)
      measurable_const
  rw [Measure.prod_apply hmeas, ← lintegral_indicator_const hS]
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx]
    calc (volume.restrict (Icc (0 : ℝ) 1))
          (Prod.mk x ⁻¹' {z : X × ℝ | z.1 ∈ S ∧ |A * z.2 + β z.1| ≤ u})
        ≤ volume (Prod.mk x ⁻¹' {z : X × ℝ | z.1 ∈ S ∧ |A * z.2 + β z.1| ≤ u}) :=
          Measure.restrict_apply_le _ _
      _ ≤ volume {D : ℝ | |A * D + β x| ≤ u} := by
          apply measure_mono
          intro D hD
          exact hD.2
      _ ≤ ENNReal.ofReal (8 * u) := volume_strip_le A (β x) u hA hu
  · have : Prod.mk x ⁻¹' {z : X × ℝ | z.1 ∈ S ∧ |A * z.2 + β z.1| ≤ u} = ∅ := by
      ext D
      simp [hx]
    rw [this, measure_empty]
    exact zero_le

/-- The center of the coefficient ball containing every trajectory of the plank. -/
noncomputable def plankCenter (b₀ w : E2) : E3 := WithLp.toLp 2 ![b₀ 0, w 0 + b₀ 1, w 1]

theorem mem_ball_plankCenter (x : E3) (b₀ w : E2) {v : ℝ} (hv : 0 < v)
    (h : (x 0 - b₀ 0) ^ 2 + (x 1 - (w 0 + b₀ 1)) ^ 2 + (x 2 - w 1) ^ 2 ≤ 16 * v ^ 2) :
    x ∈ ball (plankCenter b₀ w) (5 * v) := by
  rw [mem_ball, EuclideanSpace.dist_eq, Real.sqrt_lt' (by positivity)]
  simp only [Fin.sum_univ_three, Real.dist_eq, sq_abs, plankCenter, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  nlinarith

/-- A unit vector of the plane has `1/4 ≤ |e 1|` or `1/4 ≤ |e 1 - e 0|`. -/
theorem quarter_le_of_unit (e : E2) (he : ‖e‖ = 1) (h : ¬ 1 / 4 ≤ |e 1|) :
    1 / 4 ≤ |e 1 - e 0| := by
  have h1 : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_two, he]; norm_num
  have h' : |e 1| < 1 / 4 := lt_of_not_ge h
  have hb : e 1 ^ 2 < 1 / 16 := by
    have := sq_abs (e 1)
    nlinarith [abs_nonneg (e 1)]
  have ha : 9 / 16 < e 0 ^ 2 := by linarith
  have ha' : 3 / 4 < |e 0| := by
    have := sq_abs (e 0)
    nlinarith [abs_nonneg (e 0)]
  have := abs_sub_abs_le_abs_sub (e 0) (e 1)
  rw [abs_sub_comm] at this
  linarith

/-- The heavy lifted plank has product mass at most `8 u` times the label mass of the
coefficient ball of radius `5 v` about `plankCenter b₀ w`. -/
theorem lifted_plank_mass_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a : α → E3) (G : Set α) (ha : Measurable a) (hG : MeasurableSet G)
    (b₀ w e₁ e₂ : E2) {u v : ℝ} (he₁ : ‖e₁‖ = 1) (he₂ : ‖e₂‖ = 1)
    (he : inner ℝ e₁ e₂ = 0) (hu : 0 < u) (huv : u ≤ v) :
    (ν.prod (volume.restrict (Icc (0 : ℝ) 1))) {z : α × ℝ | z.1 ∈ G ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ -
          t • w) e₁| ≤ u ∧
        |inner ℝ (WithLp.toLp 2 ![a z.1 0 + t * (a z.1 1 - z.2), z.2 + t * a z.1 2] - b₀ -
          t • w) e₂| ≤ v} ≤
      ENNReal.ofReal (8 * u) * ν {l | a l ∈ ball (plankCenter b₀ w) (5 * v) ∧ l ∈ G} := by
  set S := {l | a l ∈ ball (plankCenter b₀ w) (5 * v) ∧ l ∈ G}
  have hS : MeasurableSet S := (ha measurableSet_ball).inter hG
  have hv : 0 < v := hu.trans_le huv
  by_cases hA : 1 / 4 ≤ |e₁ 1|
  · refine le_trans (measure_mono ?_) (prod_strip_le ν S hS (e₁ 1)
      (fun l => (a l 0 - b₀ 0) * e₁ 0 - b₀ 1 * e₁ 1) (by fun_prop) hA hu.le)
    intro z hz
    obtain ⟨hzG, hz⟩ := hz
    obtain ⟨hb, h0, -⟩ := plank_endpoint_bounds (a z.1 0) (a z.1 1) (a z.1 2) z.2 b₀ w e₁ e₂
      he₁ he₂ he huv hz
    exact ⟨⟨mem_ball_plankCenter _ b₀ w hv hb, hzG⟩, h0⟩
  · refine le_trans (measure_mono ?_) (prod_strip_le ν S hS (e₁ 1 - e₁ 0)
      (fun l => (a l 0 + a l 1 - b₀ 0 - w 0) * e₁ 0 + (a l 2 - b₀ 1 - w 1) * e₁ 1)
      (by fun_prop) (quarter_le_of_unit e₁ he₁ hA) hu.le)
    intro z hz
    obtain ⟨hzG, hz⟩ := hz
    obtain ⟨hb, -, h1⟩ := plank_endpoint_bounds (a z.1 0) (a z.1 1) (a z.1 2) z.2 b₀ w e₁ e₂
      he₁ he₂ he huv hz
    exact ⟨⟨mem_ball_plankCenter _ b₀ w hv hb, hzG⟩, h1⟩

end Submission.Obl.k4_lifted_plank_cap_saturation
