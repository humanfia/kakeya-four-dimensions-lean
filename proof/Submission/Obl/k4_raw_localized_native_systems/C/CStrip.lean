import Submission.Obl.k4_raw_localized_native_systems.C.FullTimeSample

/-
Adapted from this LOT tree, o178, session x0596, `CStrip.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Geometric (mask-free) full-time strips

For a world `γ`, a binning time `t₀` and a representative later chart `b`, the
geometric strip assignment is the union of the assignments of all later charts
of the world that contain `t₀` in their block, have a long major axis, unclipped
intercept and speed, and the same normal/intercept/speed bin as `b`.  Every line
of it with bounded positions at times `0` and `1` lies, over the whole unit
interval, in the strip of normal `q2normal b`, intercept `q2intercept b` and
speed `q2speed b`, with width `2ρ + 2G(K' + 1)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The later charts binned with a representative `b` at time `t₀` in world `γ`. -/
def binMates (a : Atlas p k) (γ : Fin (p.W k)) (t₀ lam Kc G : ℝ) (b : Fin a.C) :
    Finset (Fin a.C) := by
  classical
  exact Finset.univ.filter fun b' =>
    a.γ b' = γ ∧ blockIdx a.T t₀ = ((a.j b' : ℕ) : ℤ) ∧ lam ≤ ‖longCol (a.Q b')‖ ∧
      |inner ℝ (q2normal a b') (a.c b')| ≤ Kc ∧ |inner ℝ (q2normal a b') (a.u b')| ≤ Kc ∧
      q2bin a Kc G b' = q2bin a Kc G b

/-- The geometric strip assignment. -/
def stripLines (a : Atlas p k) (γ : Fin (p.W k)) (t₀ lam Kc G K' : ℝ) (b : Fin a.C) :
    Set Line :=
  (⋃ b' ∈ binMates a γ t₀ lam Kc G b, a.A b') ∩ {l | ‖y l 0‖ ≤ K' ∧ ‖y l 1‖ ≤ K'}

theorem floor_eq_imp_abs_sub_lt {x x' G : ℝ} (hG : 0 < G) (h : ⌊x / G⌋ = ⌊x' / G⌋) :
    |x - x'| < G := by
  have h1 := Int.floor_le (x / G)
  have h2 := Int.lt_floor_add_one (x / G)
  have h3 := Int.floor_le (x' / G)
  have h4 := Int.lt_floor_add_one (x' / G)
  rw [h] at h1 h2
  have : |x / G - x' / G| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hG, div_lt_one hG] at this
  exact this

theorem q2bin_eq_close {a : Atlas p k} {Kc G : ℝ} (hG : 0 < G) {b b' : Fin a.C}
    (h : q2bin a Kc G b' = q2bin a Kc G b) :
    |q2normal a b' 0 - q2normal a b 0| < G ∧ |q2normal a b' 1 - q2normal a b 1| < G ∧
      |q2intercept a Kc b' - q2intercept a Kc b| < G ∧ |q2speed a Kc b' - q2speed a Kc b| < G := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [q2bin, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
  exact ⟨floor_eq_imp_abs_sub_lt hG h0, floor_eq_imp_abs_sub_lt hG h1,
    floor_eq_imp_abs_sub_lt hG h2, floor_eq_imp_abs_sub_lt hG h3⟩

theorem norm_y_le_of_ends (l : Line) {K' t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h0 : ‖y l 0‖ ≤ K') (h1 : ‖y l 1‖ ≤ K') : ‖y l t‖ ≤ K' := by
  have heq : y l t = (1 - t) • y l 0 + t • y l 1 := by
    ext i
    fin_cases i <;> simp [y, x] <;> ring
  rw [heq]
  calc ‖(1 - t) • y l 0 + t • y l 1‖ ≤ ‖(1 - t) • y l 0‖ + ‖t • y l 1‖ := norm_add_le _ _
    _ = (1 - t) * ‖y l 0‖ + t * ‖y l 1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
          Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * K' + t * K' := by
        gcongr
        · linarith [ht.2]
        · exact ht.1
    _ = K' := by ring

/-- **The geometric strip.** -/
theorem stripLines_strip {M D : ℕ} {κ r : ℝ} {a : Atlas p k} {ex : Fin a.C → Prop}
    (hc : ChartsHyp a M D κ r ex) {γ : Fin (p.W k)} {t₀ lam Kc G K' ρ : ℝ} (hG : 0 < G)
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (b : Fin a.C) {l : Line} (hl : l ∈ stripLines a γ t₀ lam Kc G K' b)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ (q2normal a b) (y l t) - q2intercept a Kc b - t * q2speed a Kc b| ≤
      2 * ρ + 2 * G * K' + 2 * G := by
  classical
  obtain ⟨hU, h0, h1⟩ := hl
  simp only [Set.mem_iUnion, exists_prop] at hU
  obtain ⟨b', hb', hlA⟩ := hU
  simp only [binMates, Finset.mem_filter, Finset.mem_univ, true_and] at hb'
  obtain ⟨-, -, hlong, hint, hsp, hbin⟩ := hb'
  obtain ⟨hn0, hn1, hi, hs⟩ := q2bin_eq_close hG hbin
  have hpos := (hc.normal_position_zero b' hlA).trans (hρ b' hlong)
  have hvel := (hc.normal_velocity b' hlA).trans (hρ b' hlong)
  have hyt : ‖y l t‖ ≤ K' := norm_y_le_of_ends l ht h0 h1
  have hyt0 := abs_coord_le_norm_fin2 (y l t) 0
  have hyt1 := abs_coord_le_norm_fin2 (y l t) 1
  have hint' : q2intercept a Kc b' = inner ℝ (q2normal a b') (a.c b') := clip_eq hint
  have hsp' : q2speed a Kc b' = inner ℝ (q2normal a b') (a.u b') := clip_eq hsp
  -- decompose
  have hyt_eq : y l t = y l 0 + t • v l := by
    have := y_sub_y l 0 t
    rw [sub_zero] at this
    rw [← this]; abel
  have key : inner ℝ (q2normal a b) (y l t) - q2intercept a Kc b - t * q2speed a Kc b =
      inner ℝ (q2normal a b') (y l 0 - a.c b') + t * inner ℝ (q2normal a b') (v l - a.u b') +
      inner ℝ (q2normal a b - q2normal a b') (y l t) +
      (q2intercept a Kc b' - q2intercept a Kc b) + t * (q2speed a Kc b' - q2speed a Kc b) := by
    rw [hint', hsp', hyt_eq]
    simp only [inner_add_right, inner_smul_right, inner_sub_left, inner_sub_right]
    ring
  rw [key]
  have hdn : |inner ℝ (q2normal a b - q2normal a b') (y l t)| ≤ 2 * G * K' := by
    rw [inner_fin2]
    simp only [PiLp.sub_apply]
    calc |(q2normal a b 0 - q2normal a b' 0) * y l t 0 + (q2normal a b 1 - q2normal a b' 1) * y l t 1|
        ≤ |q2normal a b 0 - q2normal a b' 0| * |y l t 0| +
            |q2normal a b 1 - q2normal a b' 1| * |y l t 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ G * K' + G * K' := by
          gcongr
          · rw [abs_sub_comm]; exact hn0.le
          · exact hyt0.trans hyt
          · rw [abs_sub_comm]; exact hn1.le
          · exact hyt1.trans hyt
      _ = 2 * G * K' := by ring
  have ht0 := ht.1
  have ht1 := ht.2
  calc |inner ℝ (q2normal a b') (y l 0 - a.c b') + t * inner ℝ (q2normal a b') (v l - a.u b') +
        inner ℝ (q2normal a b - q2normal a b') (y l t) +
        (q2intercept a Kc b' - q2intercept a Kc b) + t * (q2speed a Kc b' - q2speed a Kc b)|
      ≤ |inner ℝ (q2normal a b') (y l 0 - a.c b')| +
          t * |inner ℝ (q2normal a b') (v l - a.u b')| +
          |inner ℝ (q2normal a b - q2normal a b') (y l t)| +
          |q2intercept a Kc b' - q2intercept a Kc b| +
          t * |q2speed a Kc b' - q2speed a Kc b| := by
        have e1 := abs_add_le (inner ℝ (q2normal a b') (y l 0 - a.c b') +
            t * inner ℝ (q2normal a b') (v l - a.u b') +
            inner ℝ (q2normal a b - q2normal a b') (y l t) +
            (q2intercept a Kc b' - q2intercept a Kc b)) (t * (q2speed a Kc b' - q2speed a Kc b))
        have e2 := abs_add_le (inner ℝ (q2normal a b') (y l 0 - a.c b') +
            t * inner ℝ (q2normal a b') (v l - a.u b') +
            inner ℝ (q2normal a b - q2normal a b') (y l t)) (q2intercept a Kc b' - q2intercept a Kc b)
        have e3 := abs_add_le (inner ℝ (q2normal a b') (y l 0 - a.c b') +
            t * inner ℝ (q2normal a b') (v l - a.u b')) (inner ℝ (q2normal a b - q2normal a b') (y l t))
        have e4 := abs_add_le (inner ℝ (q2normal a b') (y l 0 - a.c b'))
          (t * inner ℝ (q2normal a b') (v l - a.u b'))
        rw [abs_mul, abs_of_nonneg ht0] at e4 e1
        linarith
    _ ≤ ρ + 1 * ρ + 2 * G * K' + G + 1 * G := by
        have hA : |inner ℝ (q2normal a b') (y l 0 - a.c b')| ≤ ρ := hpos
        have hB : t * |inner ℝ (q2normal a b') (v l - a.u b')| ≤ 1 * ρ :=
          mul_le_mul ht1 hvel (abs_nonneg _) zero_le_one
        have hC : t * |q2speed a Kc b' - q2speed a Kc b| ≤ 1 * G :=
          mul_le_mul ht1 hs.le (abs_nonneg _) zero_le_one
        linarith [hi.le]
    _ = 2 * ρ + 2 * G * K' + 2 * G := by ring

end

end Submission.Obl.k4_raw_localized_native_systems.C
