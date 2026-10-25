import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeMatch
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.ChartCount

set_option linter.unusedVariables false

/-!
# The density step of the coefficient agreement

A source cell (coefficient class with its layer-1 offset bin, time cell) restricted to one
transverse cell is a moving box with a hidden window of width `a (2H+1) N^-u`, charged to the
frozen joint caps with the palette weight of the chart velocity bin; summing over transverse
cells and using the matching-set volume gives the density bound.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter Metric
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

namespace Frame

variable (F : Frame)

/-- Normalized coordinates of a base point `(t, x₁, x₂)`. -/
def ζt (y : Fin 3 → ℝ) : ℝ := (y 0 - F.t₀) / F.q
def ζZ (y : Fin 3 → ℝ) : ℝ := (y 1 - F.c 0 - y 0 * F.c 1) / F.q
def ζU (y : Fin 3 → ℝ) : ℝ := (y 2 - F.c 2 - y 0 * F.c 3 - F.c 4 * y 1) / (F.q * F.g)
def Lform (y : Fin 3 → ℝ) : ℝ := F.L 0 + F.L 1 * y 0 + F.L 2 * y 1 + F.L 3 * y 2

end Frame

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

theorem basePoint_zeta (F : Frame) (k : ℕ) (p : α × ℝ) :
    F.ζt (basePoint cfg k p) = F.zt p.2 ∧
    F.ζZ (basePoint cfg k p) = F.zZ (cfg.b k p.1) p.2 ∧
    F.ζU (basePoint cfg k p) = F.tr (cfg.b k p.1) p.2 ∧
    F.Lform (basePoint cfg k p) =
      F.L 0 + F.L 1 * p.2 + F.L 2 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) +
        F.L 3 * (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) := by
  simp only [Frame.ζt, Frame.ζZ, Frame.ζU, Frame.Lform, basePoint, Frame.zt, Frame.zZ, Frame.tr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, and_self]

theorem window_of_fit {X Lf a resid Q D d η H : ℝ} (ha : 0 < a) (hres : X = Lf + a * resid)
    (hfit : |resid - Q - D| ≤ H * η) (hd1 : d * η ≤ D) (hd2 : D < (d + 1) * η) :
    Lf + a * (Q + (d - H) * η) ≤ X ∧ X ≤ Lf + a * (Q + (d - H) * η) + a * (2 * H + 1) * η := by
  obtain ⟨h1, h2⟩ := abs_le.mp hfit
  rw [hres]
  constructor
  · have : Q + (d - H) * η ≤ resid := by nlinarith
    nlinarith
  · have : resid ≤ Q + (d - H) * η + (2 * H + 1) * η := by nlinarith
    nlinarith

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- The hidden offset of a source on a base point. -/
def srcOffset (sr : CB.Γ × ℤ) (y : Fin 3 → ℝ) : ℝ :=
  CB.frame.Lform y + CB.frame.a * (predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt y)
    (CB.frame.ζZ y) (CB.frame.ζU y) + ((sr.2 : ℝ) - H) * cfg.N k ^ (-u))

/-- The offset is Lipschitz on the mesh scale. -/
theorem srcOffset_lip (hK : 1 ≤ cfg.K k) (hH : 1 ≤ H) (hB : BlocksAt cfg k s R)
    (hq : 0 < CB.frame.q) (hg : 0 < CB.frame.g) (hg1 : CB.frame.g ≤ 1) (ha : 0 < CB.frame.a)
    {Lb ρ : ℝ} (hLb : ∀ e, |CB.L e| ≤ Lb) (hρ : 0 ≤ ρ)
    (hstep : (3 + 3 * cfg.K k) * ρ ≤ CB.frame.q * CB.frame.g)
    (sr : CB.Γ × ℤ) {x y : Fin 3 → ℝ}
    (hx0 : 0 ≤ CB.frame.ζt x ∧ CB.frame.ζt x ≤ 1) (hx1 : |CB.frame.ζZ x| ≤ cfg.K k)
    (hx2 : |CB.frame.ζU x| ≤ cfg.K k) (hxy : ∀ i, |x i - y i| ≤ ρ) :
    |CB.srcOffset sr x - CB.srcOffset sr y| ≤
      3 * Lb * ρ + CB.frame.a * H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) * ρ /
        (CB.frame.q * CB.frame.g) := by
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hc : ∀ e, |CB.frame.c e| ≤ cfg.K k := fun e => hB.c_bd CB.i e
  have hqg1 : CB.frame.q * CB.frame.g ≤ CB.frame.q := by nlinarith
  -- normalized steps
  have hdt : |CB.frame.ζt x - CB.frame.ζt y| ≤ ρ / CB.frame.q := by
    simp only [Frame.ζt]
    rw [show (x 0 - CB.frame.t₀) / CB.frame.q - (y 0 - CB.frame.t₀) / CB.frame.q =
      (x 0 - y 0) / CB.frame.q by ring, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right (hxy 0) hq.le
  have hdZ : |CB.frame.ζZ x - CB.frame.ζZ y| ≤ (1 + cfg.K k) * ρ / CB.frame.q := by
    simp only [Frame.ζZ]
    rw [show (x 1 - CB.frame.c 0 - x 0 * CB.frame.c 1) / CB.frame.q -
        (y 1 - CB.frame.c 0 - y 0 * CB.frame.c 1) / CB.frame.q =
      ((x 1 - y 1) - (x 0 - y 0) * CB.frame.c 1) / CB.frame.q by ring, abs_div, abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ hq.le
    calc _ ≤ |x 1 - y 1| + |x 0 - y 0| * |CB.frame.c 1| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ ρ + ρ * cfg.K k := by gcongr <;> first | exact hxy _ | exact hc 1
      _ = _ := by ring
  have hdU : |CB.frame.ζU x - CB.frame.ζU y| ≤ (1 + 2 * cfg.K k) * ρ / (CB.frame.q * CB.frame.g) := by
    simp only [Frame.ζU]
    rw [show (x 2 - CB.frame.c 2 - x 0 * CB.frame.c 3 - CB.frame.c 4 * x 1) / (CB.frame.q * CB.frame.g) -
        (y 2 - CB.frame.c 2 - y 0 * CB.frame.c 3 - CB.frame.c 4 * y 1) / (CB.frame.q * CB.frame.g) =
      ((x 2 - y 2) - (x 0 - y 0) * CB.frame.c 3 - CB.frame.c 4 * (x 1 - y 1)) /
        (CB.frame.q * CB.frame.g) by ring, abs_div, abs_of_pos (mul_pos hq hg)]
    apply div_le_div_of_nonneg_right _ (mul_pos hq hg).le
    calc _ ≤ |x 2 - y 2| + |x 0 - y 0| * |CB.frame.c 3| + |CB.frame.c 4| * |x 1 - y 1| := by
          have := abs_sub (x 2 - y 2 - (x 0 - y 0) * CB.frame.c 3) (CB.frame.c 4 * (x 1 - y 1))
          have := abs_sub (x 2 - y 2) ((x 0 - y 0) * CB.frame.c 3)
          rw [abs_mul] at *
          linarith
      _ ≤ ρ + ρ * cfg.K k + cfg.K k * ρ := by
          gcongr <;> first | exact hxy _ | exact hc _
      _ = _ := by ring
  -- the normalized steps are at most one
  have hstep1 : ρ / CB.frame.q ≤ 1 := by
    rw [div_le_one hq]; nlinarith
  have hstep2 : (1 + cfg.K k) * ρ / CB.frame.q ≤ 1 := by
    rw [div_le_one hq]; nlinarith
  have hstep3 : (1 + 2 * cfg.K k) * ρ / (CB.frame.q * CB.frame.g) ≤ 1 := by
    rw [div_le_one (mul_pos hq hg)]; nlinarith
  have hy0 : |CB.frame.ζt y| ≤ 2 := by
    have : |CB.frame.ζt y| ≤ |CB.frame.ζt x| + |CB.frame.ζt x - CB.frame.ζt y| := by
      have := abs_sub_abs_le_abs_sub (CB.frame.ζt y) (CB.frame.ζt x)
      rw [abs_sub_comm (CB.frame.ζt y)] at this; linarith
    have hx' : |CB.frame.ζt x| ≤ 1 := abs_le.mpr ⟨by linarith [hx0.1], hx0.2⟩
    linarith
  have hy1 : |CB.frame.ζZ y| ≤ cfg.K k + 1 := by
    have : |CB.frame.ζZ y| ≤ |CB.frame.ζZ x| + |CB.frame.ζZ x - CB.frame.ζZ y| := by
      have := abs_sub_abs_le_abs_sub (CB.frame.ζZ y) (CB.frame.ζZ x)
      rw [abs_sub_comm (CB.frame.ζZ y)] at this; linarith
    linarith
  have hy2 : |CB.frame.ζU y| ≤ cfg.K k + 1 := by
    have : |CB.frame.ζU y| ≤ |CB.frame.ζU x| + |CB.frame.ζU x - CB.frame.ζU y| := by
      have := abs_sub_abs_le_abs_sub (CB.frame.ζU y) (CB.frame.ζU x)
      rw [abs_sub_comm (CB.frame.ζU y)] at this; linarith
    linarith
  have hQ := predQ_diff (CB.pc_bd sr.1) (CB.tc_bd sr.1) (X := 2) (Y := cfg.K k + 1)
    (Ub := cfg.K k + 1) (x := CB.frame.ζt x) (y := CB.frame.ζZ x) (U := CB.frame.ζU x)
    (x' := CB.frame.ζt y) (y' := CB.frame.ζZ y) (U' := CB.frame.ζU y)
    (abs_le.mpr ⟨by linarith [hx0.1], by linarith [hx0.2]⟩) hy0 (by linarith) hy1
    (by linarith) hy2
  have hLf : |CB.frame.Lform x - CB.frame.Lform y| ≤ 3 * Lb * ρ := by
    simp only [Frame.Lform]
    rw [show CB.frame.L 0 + CB.frame.L 1 * x 0 + CB.frame.L 2 * x 1 + CB.frame.L 3 * x 2 -
        (CB.frame.L 0 + CB.frame.L 1 * y 0 + CB.frame.L 2 * y 1 + CB.frame.L 3 * y 2) =
      CB.frame.L 1 * (x 0 - y 0) + CB.frame.L 2 * (x 1 - y 1) + CB.frame.L 3 * (x 2 - y 2) by ring]
    calc _ ≤ |CB.frame.L 1| * |x 0 - y 0| + |CB.frame.L 2| * |x 1 - y 1| +
          |CB.frame.L 3| * |x 2 - y 2| := by
          refine (abs_add_three _ _ _).trans ?_; simp only [abs_mul, le_refl]
      _ ≤ Lb * ρ + Lb * ρ + Lb * ρ := by
          have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
          have h1 : |CB.frame.L 1| ≤ Lb := hLb 1
          have h2 : |CB.frame.L 2| ≤ Lb := hLb 2
          have h3 : |CB.frame.L 3| ≤ Lb := hLb 3
          gcongr <;> first | exact hxy _ | assumption
      _ = 3 * Lb * ρ := by ring
  have hQ' : |predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt x) (CB.frame.ζZ x) (CB.frame.ζU x) -
      predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt y) (CB.frame.ζZ y) (CB.frame.ζU y)| ≤
      H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) * ρ / (CB.frame.q * CB.frame.g) := by
    refine hQ.trans ?_
    have hH0 : 0 ≤ H := by linarith
    have hqgq : ρ / CB.frame.q ≤ ρ / (CB.frame.q * CB.frame.g) :=
      div_le_div_of_nonneg_left hρ (mul_pos hq hg) hqg1
    have hqgq' : (1 + cfg.K k) * ρ / CB.frame.q ≤ (1 + cfg.K k) * ρ / (CB.frame.q * CB.frame.g) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hq hg) hqg1
    have e1 : (1 + 2 * 2 + (cfg.K k + 1) + (cfg.K k + 1)) ≤ 3 * cfg.K k + 7 := by linarith
    have e2 : (1 + 2 + 2 * (cfg.K k + 1) + (cfg.K k + 1)) ≤ 3 * cfg.K k + 7 := by linarith
    have e3 : (1 + 2 + (cfg.K k + 1) + 2 * (cfg.K k + 1)) ≤ 3 * cfg.K k + 7 := by linarith
    have hdt' := hdt.trans hqgq
    have hdZ' := hdZ.trans hqgq'
    have hsum : (3 * cfg.K k + 7) * (ρ / (CB.frame.q * CB.frame.g)) +
        (3 * cfg.K k + 7) * ((1 + cfg.K k) * ρ / (CB.frame.q * CB.frame.g)) +
        (3 * cfg.K k + 7) * ((1 + 2 * cfg.K k) * ρ / (CB.frame.q * CB.frame.g)) =
        (3 * cfg.K k + 7) * (3 * cfg.K k + 3) * ρ / (CB.frame.q * CB.frame.g) := by
      field_simp; ring
    calc H * ((1 + 2 * 2 + (cfg.K k + 1) + (cfg.K k + 1)) * |CB.frame.ζt x - CB.frame.ζt y| +
          (1 + 2 + 2 * (cfg.K k + 1) + (cfg.K k + 1)) * |CB.frame.ζZ x - CB.frame.ζZ y| +
          (1 + 2 + (cfg.K k + 1) + 2 * (cfg.K k + 1)) * |CB.frame.ζU x - CB.frame.ζU y|)
        ≤ H * ((3 * cfg.K k + 7) * (ρ / (CB.frame.q * CB.frame.g)) +
          (3 * cfg.K k + 7) * ((1 + cfg.K k) * ρ / (CB.frame.q * CB.frame.g)) +
          (3 * cfg.K k + 7) * ((1 + 2 * cfg.K k) * ρ / (CB.frame.q * CB.frame.g))) := by
          gcongr
      _ = _ := by rw [hsum]; ring
  simp only [srcOffset]
  rw [show CB.frame.Lform x + CB.frame.a * (predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt x)
        (CB.frame.ζZ x) (CB.frame.ζU x) + ((sr.2 : ℝ) - H) * cfg.N k ^ (-u)) -
      (CB.frame.Lform y + CB.frame.a * (predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt y)
        (CB.frame.ζZ y) (CB.frame.ζU y) + ((sr.2 : ℝ) - H) * cfg.N k ^ (-u))) =
      (CB.frame.Lform x - CB.frame.Lform y) + CB.frame.a *
        (predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt x) (CB.frame.ζZ x) (CB.frame.ζU x) -
          predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt y) (CB.frame.ζZ y) (CB.frame.ζU y)) by ring]
  calc _ ≤ |CB.frame.Lform x - CB.frame.Lform y| + CB.frame.a *
        |predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt x) (CB.frame.ζZ x) (CB.frame.ζU x) -
          predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.ζt y) (CB.frame.ζZ y) (CB.frame.ζU y)| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_pos ha]
    _ ≤ 3 * Lb * ρ + CB.frame.a * (H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) * ρ /
          (CB.frame.q * CB.frame.g)) := by gcongr
    _ = _ := by ring

/-- **The cap of one source cell in one transverse cell.** -/
theorem cell_cap_step (hcap : CapsAt cfg k R) (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    (hK : 1 ≤ cfg.K k) (hb : Measurable (cfg.b k)) (hL : HorizontalForm (cfg.F k s CB.i) CB.L)
    (hχ : 0 < χ) (hH : 1 ≤ H) (hδt : 0 < P.δt) (hδU : 0 < P.δU)
    {r s' v' Lb : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R)
    (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (hwin : CB.frame.a * (2 * H + 1) * cfg.N k ^ (-u) = cfg.N k ^ (-s'))
    (hLb : ∀ e, |CB.L e| ≤ Lb) (hg1 : CB.frame.g ≤ 1)
    (hδv : cfg.N k ^ (-v') ≤ χ) (hχK : χ ≤ cfg.K k)
    (hm1 : cfg.N k ^ (-r) ≤ CB.frame.q * P.δt / 2)
    (hm2 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ χ)
    (hm3 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g * P.δU / 2)
    (hm4 : (3 + 3 * cfg.K k) * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g)
    (hlip : 3 * Lb * cfg.N k ^ (-r) + CB.frame.a * H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) *
      cfg.N k ^ (-r) / (CB.frame.q * CB.frame.g) ≤ cfg.N k ^ (-s'))
    (lam1 : Measure (α × ℝ)) (hlam1 : lam1 ≤ CB.lam) (hlamμ : lam1 ≤ cfg.μ k)
    (sr : CB.Γ × ℤ) (c w' : ℤ) :
    lam1 {p | CB.src p = sr ∧ CB.cell P p = c ∧ ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w'} ≤
      ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
        (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d) *
      paletteBins (cfg.π k) (cfg.N k ^ (-v')) (Vt (cfg.N k ^ (-v')) χ (CB.chartOf sr.1).1) := by
  have hq : 0 < CB.frame.q := by simp only [frame, blockFrame]; positivity
  have hg : 0 < CB.frame.g := Real.rpow_pos_of_pos hN _
  have ha : 0 < CB.frame.a := Real.rpow_pos_of_pos hN _
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hr0 : 0 < cfg.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have hv0 : 0 < cfg.N k ^ (-v') := Real.rpow_pos_of_pos hN _
  have hc : ∀ e, |CB.frame.c e| ≤ cfg.K k := fun e => hB.c_bd CB.i e
  set S₀ := {p : α × ℝ | CB.src p = sr ∧ CB.cell P p = c ∧
    ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w'}
  set E := {p : α × ℝ | CB.Good p ∧ CB.src p = sr ∧ CB.cell P p = c ∧
    ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w'}
  have hac : lam1 ≪ CB.lam := Measure.absolutelyContinuous_of_le hlam1
  have hgood : ∀ᵐ p ∂lam1, CB.Good p := hac.ae_le CB.ae_good
  have h1 : lam1 S₀ ≤ cfg.μ k E := by
    calc lam1 S₀ ≤ lam1 E := by
          apply measure_mono_ae
          filter_upwards [hgood] with p hp hS
          exact ⟨hp, hS⟩
      _ ≤ cfg.μ k E := hlamμ E
  refine h1.trans ?_
  set n := (CB.chartOf sr.1).1
  set m := (CB.chartOf sr.1).2
  have hEv : E = {p | p ∈ E ∧ vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ Vt (cfg.N k ^ (-v')) χ n} := by
    ext p
    simp only [mem_ofPred_eq]
    constructor
    · intro hp
      refine ⟨hp, ?_⟩
      have hch := hp.1.chart
      have hsrc : CB.cls p = sr.1 := congrArg Prod.fst hp.2.1
      have : ⌊cfg.b k p.1 3 / χ⌋ = n := by
        simp only [chart, cls] at hch hsrc
        simp only [n]; rw [← hsrc, ← hch]
      rw [← this]
      exact vbin_mem_Vt hv0 hχ hδv
    · exact fun h => h.1
  rw [hEv]
  -- the moving box
  let time : ℝ := CB.frame.t₀ + CB.frame.q * (((c : ℝ) + 1 / 2) * P.δt)
  let center : Fin 2 → ℝ := ![((m : ℝ) + 1 / 2) * χ, CB.frame.c 2 + CB.frame.c 4 *
    (((m : ℝ) + 1 / 2) * χ) + CB.frame.q * CB.frame.g * (((w' : ℝ) + 1 / 2) * P.δU)]
  let velocity : Fin 2 → ℝ := ![((n : ℝ) + 1 / 2) * χ, CB.frame.c 3 + CB.frame.c 4 *
    (((n : ℝ) + 1 / 2) * χ)]
  let width : Fin 2 → ℝ := ![χ, CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ]
  by_cases hne : E.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp
  obtain ⟨p₀, hp₀⟩ := hne
  -- facts about good points of the source cell
  have hpt : ∀ p ∈ E, (⌊cfg.b k p.1 3 / χ⌋ = n ∧ ⌊cfg.b k p.1 0 / χ⌋ = m) ∧
      ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ = sr.2 := by
    intro p hp
    have hch := hp.1.chart
    have hsrc1 : CB.cls p = sr.1 := congrArg Prod.fst hp.2.1
    have hsrc2 : ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋ = sr.2 := congrArg Prod.snd hp.2.1
    simp only [chart, cls] at hch hsrc1
    rw [hsrc1] at hch
    exact ⟨⟨congrArg Prod.fst hch, congrArg Prod.snd hch⟩, hsrc2⟩
  have hvel0 : |((n : ℝ) + 1 / 2) * χ| ≤ 4 * cfg.K k := by
    obtain ⟨⟨hn, -⟩, -⟩ := hpt p₀ hp₀
    obtain ⟨-, -, -, -, hb3⟩ := CB.good_bounds hB hN hK hL hp₀.1
    have e1 := abs_sub_center_of_floor hχ hn
    calc |((n : ℝ) + 1 / 2) * χ| = |(cfg.b k p₀.1 3 - CB.frame.c 1) + CB.frame.c 1 -
          (cfg.b k p₀.1 3 - χ * ((n : ℝ) + 1 / 2))| := by ring_nf
      _ ≤ |cfg.b k p₀.1 3 - CB.frame.c 1| + |CB.frame.c 1| +
          |cfg.b k p₀.1 3 - χ * ((n : ℝ) + 1 / 2)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ 4 * cfg.K k := by
          have hb3' : |cfg.b k p₀.1 3 - CB.frame.c 1| ≤ 2 * cfg.K k := hb3
          linarith [hc 1]
  have hv : ∀ i, |velocity i| ≤ 5 * cfg.K k ^ 2 := by
    intro i; fin_cases i
    · simp only [velocity, Fin.zero_eta, Matrix.cons_val_zero]; nlinarith
    · simp only [velocity, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      calc _ ≤ |CB.frame.c 3| + |CB.frame.c 4| * |((n : ℝ) + 1 / 2) * χ| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ cfg.K k + cfg.K k * (4 * cfg.K k) := by gcongr <;> exact hc _
        _ ≤ 5 * cfg.K k ^ 2 := by nlinarith
  have hrK : cfg.N k ^ (-r) ≤ 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) := by
    have : 1 ≤ 5 * cfg.K k ^ 2 := by nlinarith
    nlinarith
  have hdw : ∀ i, cfg.N k ^ (-r) ≤ width i := by
    intro i; fin_cases i
    · simp only [width, Fin.zero_eta, Matrix.cons_val_zero]; linarith
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have : 0 ≤ cfg.K k * χ := by positivity
      linarith
  have hmove : ∀ i, 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ width i := by
    intro i; fin_cases i
    · simp only [width, Fin.zero_eta, Matrix.cons_val_zero]; linarith
    · simp only [width, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have : 0 ≤ cfg.K k * χ := by positivity
      linarith
  have hθ0 : 0 ≤ 3 * Lb * cfg.N k ^ (-r) + CB.frame.a * H * (3 * cfg.K k + 7) *
      (3 * cfg.K k + 3) * cfg.N k ^ (-r) / (CB.frame.q * CB.frame.g) := by
    have hLb0 : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
    have hH0 : 0 ≤ H := by linarith
    positivity
  have hbox := box_cap_bins hcap hN hK0 hb hr1 hr2 hs1 hs2 hv1 hv2 E (CB.srcOffset sr) hθ0 hlip
    hm1 (by positivity) time center velocity width hv hdw hmove ?_ ?_ (Vt (cfg.N k ^ (-v')) χ n)
  · simpa only [width, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hbox
  · -- Lipschitz offset
    intro p hp y hy
    obtain ⟨hzt, hzZ, htr, -, -⟩ := CB.good_bounds hB hN hK hL hp.1
    obtain ⟨e0, e1, e2, -⟩ := basePoint_zeta CB.frame k p
    exact CB.srcOffset_lip hK hH hB hq hg hg1 ha hLb hr0.le hm4 sr (by rw [e0]; exact hzt)
      (by rw [e1]; exact hzZ) (by rw [e2]; exact htr) hy
  · -- membership and window
    intro p hp
    obtain ⟨⟨hn, hm⟩, hd⟩ := hpt p hp
    obtain ⟨hzt, hzZ, htr, -, -⟩ := CB.good_bounds hB hN hK hL hp.1
    obtain ⟨e0, e1, e2, e3⟩ := basePoint_zeta CB.frame k p
    have hcell : ⌊CB.frame.zt p.2 / P.δt⌋ = c := hp.2.2.1
    have hU : ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w' := hp.2.2.2
    have ht := I_subset_unit hp.1.I
    have habs1 : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hct := abs_sub_center_of_floor hδt hcell
    have hcU := abs_sub_center_of_floor hδU hU
    have hbn := abs_sub_center_of_floor hχ hn
    have hbm := abs_sub_center_of_floor hχ hm
    -- x1 band
    have hx1 : |(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (((m : ℝ) + 1 / 2) * χ +
        p.2 * (((n : ℝ) + 1 / 2) * χ))| ≤ χ := by
      rw [show (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (((m : ℝ) + 1 / 2) * χ +
          p.2 * (((n : ℝ) + 1 / 2) * χ)) = (cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)) +
          p.2 * (cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)) by ring]
      calc _ ≤ |cfg.b k p.1 0 - χ * ((m : ℝ) + 1 / 2)| + |p.2| * |cfg.b k p.1 3 - χ * ((n : ℝ) + 1 / 2)| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ χ / 2 + 1 * (χ / 2) := by gcongr
        _ = χ := by ring
    refine ⟨?_, ?_⟩
    · simp only [movingBox, mem_ofPred_eq, Fin.forall_fin_two, basePoint, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Matrix.cons_val_two, Matrix.tail_cons, time, center, velocity, width]
      refine ⟨?_, ?_, ?_⟩
      · rw [show p.2 - (CB.frame.t₀ + CB.frame.q * (((c : ℝ) + 1 / 2) * P.δt)) =
            CB.frame.q * (CB.frame.zt p.2 - P.δt * ((c : ℝ) + 1 / 2)) by
              simp only [Frame.zt]; field_simp; ring, abs_mul, abs_of_pos hq]
        calc CB.frame.q * |CB.frame.zt p.2 - P.δt * ((c : ℝ) + 1 / 2)| ≤ CB.frame.q * (P.δt / 2) := by
              gcongr
          _ = CB.frame.q * P.δt / 2 := by ring
      · exact hx1
      · have hU' : |(cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - CB.frame.c 2 - p.2 * CB.frame.c 3 -
            CB.frame.c 4 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3)) -
            CB.frame.q * CB.frame.g * (((w' : ℝ) + 1 / 2) * P.δU)| ≤
            CB.frame.q * CB.frame.g * P.δU / 2 := by
          rw [show (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - CB.frame.c 2 - p.2 * CB.frame.c 3 -
              CB.frame.c 4 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3)) -
              CB.frame.q * CB.frame.g * (((w' : ℝ) + 1 / 2) * P.δU) =
              (CB.frame.q * CB.frame.g) * (CB.frame.tr (cfg.b k p.1) p.2 - P.δU * ((w' : ℝ) + 1 / 2)) by
                simp only [Frame.tr]; field_simp,
            abs_mul, abs_of_pos (mul_pos hq hg)]
          calc (CB.frame.q * CB.frame.g) * |CB.frame.tr (cfg.b k p.1) p.2 - P.δU * ((w' : ℝ) + 1 / 2)|
              ≤ (CB.frame.q * CB.frame.g) * (P.δU / 2) := by gcongr
            _ = _ := by ring
        rw [show cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - (CB.frame.c 2 + CB.frame.c 4 *
            (((m : ℝ) + 1 / 2) * χ) + CB.frame.q * CB.frame.g * (((w' : ℝ) + 1 / 2) * P.δU) +
            p.2 * (CB.frame.c 3 + CB.frame.c 4 * (((n : ℝ) + 1 / 2) * χ))) =
            ((cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - CB.frame.c 2 - p.2 * CB.frame.c 3 -
            CB.frame.c 4 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3)) -
            CB.frame.q * CB.frame.g * (((w' : ℝ) + 1 / 2) * P.δU)) +
            CB.frame.c 4 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (((m : ℝ) + 1 / 2) * χ +
              p.2 * (((n : ℝ) + 1 / 2) * χ))) by ring]
        calc _ ≤ CB.frame.q * CB.frame.g * P.δU / 2 + |CB.frame.c 4| * χ := by
              refine (abs_add_le _ _).trans ?_; rw [abs_mul]; gcongr
          _ ≤ CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ := by gcongr; exact hc 4
    · -- windows
      have hfit := hp.1.fit1
      have hsr : CB.crs (CB.lab p.1) = sr.1 := congrArg Prod.fst hp.2.1
      rw [hsr] at hfit
      have hη : 0 < cfg.N k ^ (-u) := Real.rpow_pos_of_pos hN _
      have hD1 := Int.floor_le (CB.D1 (CB.lab p.1) / cfg.N k ^ (-u))
      have hD2 := Int.lt_floor_add_one (CB.D1 (CB.lab p.1) / cfg.N k ^ (-u))
      rw [hd, le_div_iff₀ hη] at hD1
      rw [hd, div_lt_iff₀ hη] at hD2
      have hw := window_of_fit ha (X := cfg.b k p.1 2 + p.2 * cfg.b k p.1 5)
        (Lf := CB.frame.Lform (basePoint cfg k p)) (resid := CB.frame.resid (cfg.b k p.1) p.2)
        (Q := predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)
          (CB.frame.tr (cfg.b k p.1) p.2)) (D := CB.D1 (CB.lab p.1)) (d := (sr.2 : ℝ))
        (η := cfg.N k ^ (-u)) (H := H) ?_ ?_ hD1 hD2
      · have hoff : CB.srcOffset sr (basePoint cfg k p) = CB.frame.Lform (basePoint cfg k p) +
            CB.frame.a * (predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.zt p.2)
              (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) +
              ((sr.2 : ℝ) - H) * cfg.N k ^ (-u)) := by
          unfold srcOffset
          rw [e0, e1, e2]
        constructor
        · rw [hoff]; exact hw.1
        · rw [hoff, ← hwin]
          calc _ ≤ _ := hw.2
            _ = _ := by ring
      · rw [e3]; simp only [Frame.resid, frame_L]; field_simp; ring
      · have e : CB.frame.resid (cfg.b k p.1) p.2 - predQ (CB.pc sr.1) (CB.tc sr.1) (CB.frame.zt p.2)
            (CB.frame.zZ (cfg.b k p.1) p.2) (CB.frame.tr (cfg.b k p.1) p.2) - CB.D1 (CB.lab p.1) =
            CB.frame.resid (cfg.b k p.1) p.2 - quadZ (CB.pc sr.1) (CB.frame.zt p.2)
              (CB.frame.zZ (cfg.b k p.1) p.2) - CB.D1 (CB.lab p.1) -
            transv (CB.tc sr.1) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)
              (CB.frame.tr (cfg.b k p.1) p.2) := by
          simp only [predQ]; ring
        rw [e]; exact hfit

/-- The cap constant of a source in one transverse cell. -/
def capcell (r s' v' : ℝ) (sr : CB.Γ × ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
    (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d) *
  paletteBins (cfg.π k) (cfg.N k ^ (-v')) (Vt (cfg.N k ^ (-v')) χ (CB.chartOf sr.1).1)

/-- **The density step.** -/
theorem dens_step (hcap : CapsAt cfg k R) (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    (hK : 1 ≤ cfg.K k) (hb : Measurable (cfg.b k)) (hL : HorizontalForm (cfg.F k s CB.i) CB.L)
    (hχ : 0 < χ) (hH : 1 ≤ H) (hδt : 0 < P.δt) (hδU : 0 < P.δU) (he : 0 < P.e)
    {r s' v' Lb θm w LipU : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R)
    (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (hwin : CB.frame.a * (2 * H + 1) * cfg.N k ^ (-u) = cfg.N k ^ (-s'))
    (hLb : ∀ e, |CB.L e| ≤ Lb) (hg1 : CB.frame.g ≤ 1)
    (hδv : cfg.N k ^ (-v') ≤ χ) (hχK : χ ≤ cfg.K k)
    (hm1 : cfg.N k ^ (-r) ≤ CB.frame.q * P.δt / 2)
    (hm2 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ χ)
    (hm3 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g * P.δU / 2)
    (hm4 : (3 + 3 * cfg.K k) * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g)
    (hlip : 3 * Lb * cfg.N k ^ (-r) + CB.frame.a * H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) *
      cfg.N k ^ (-r) / (CB.frame.q * CB.frame.g) ≤ cfg.N k ^ (-s'))
    (hθm : 0 < θm) (hθme : θm ≤ P.e / 2) (hw : 0 ≤ w)
    (lam1 : Measure (α × ℝ)) (hlam1 : lam1 ≤ CB.lam) (hlamμ : lam1 ≤ cfg.μ k)
    (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ)
    (hLipU : |CB.cδ₁ P sr c γ'| + 2 * |CB.cδ₂ sr γ'| * (cfg.K k + P.δU) ≤ LipU) :
    lam1 {p | CB.src p = sr ∧ CB.cell P p = c ∧
        CB.frame.tr (cfg.b k p.1) p.2 ∈ CB.Mset P w (cfg.K k) sr c γ'} ≤
      CB.capcell P r s' v' sr / ENNReal.ofReal P.δU *
        ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
          4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) := by
  have hK0 : 0 ≤ cfg.K k := by linarith
  by_cases hgap : P.e ≤ |CB.cδ₁ P sr c γ'| + |CB.cδ₂ sr γ'|
  swap
  · have : {p | CB.src p = sr ∧ CB.cell P p = c ∧
        CB.frame.tr (cfg.b k p.1) p.2 ∈ CB.Mset P w (cfg.K k) sr c γ'} = ∅ := by
      ext p; simp [Mset, hgap]
    rw [this, measure_empty]; exact zero_le
  have hM : CB.Mset P w (cfg.K k) sr c γ' = offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ')
      (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ') := by simp [Mset, hgap]
  rw [hM]
  set S := {p : α × ℝ | CB.src p = sr ∧ CB.cell P p = c}
  have hcells := measure_le_of_cells lam1 S (fun p => CB.frame.tr (cfg.b k p.1) p.2) hδU
    (CB.capcell P r s' v' sr) (fun w' => by
      have := CB.cell_cap_step P hcap hB hN hK hb hL hχ hH hδt hδU hr1 hr2 hs1 hs2 hv1 hv2 hwin
        hLb hg1 hδv hχK hm1 hm2 hm3 hm4 hlip lam1 hlam1 hlamμ sr c w'
      have hset : {p : α × ℝ | p ∈ S ∧ ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w'} =
          {p | CB.src p = sr ∧ CB.cell P p = c ∧ ⌊CB.frame.tr (cfg.b k p.1) p.2 / P.δU⌋ = w'} := by
        ext p; simp [S, and_assoc]
      rw [hset]; exact this)
    (offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ') (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ'))
    (offsetMatch_subset_Icc _ _ _ _ _ _)
  have hthick := thickening_offsetMatch (δ₀ := CB.cδ₀ P sr c γ') (δ₁ := CB.cδ₁ P sr c γ')
    (δ₂ := CB.cδ₂ sr γ') (w := w) (CB.Om γ') hK0 hδU
  have hLip' : P.δU * (|CB.cδ₁ P sr c γ'| + 2 * |CB.cδ₂ sr γ'| * (cfg.K k + P.δU)) ≤
      P.δU * LipU := by
    gcongr
  have hcardO : ((CB.Om γ').card : ℝ) ≤ H * cfg.N k ^ (cfg.d * u) :=
    (Nat.cast_le.mpr Finset.card_image_le).trans (CB.F1_card _ _)
  have hvol := volume_offsetMatch_le (δ₀ := CB.cδ₀ P sr c γ') (δ₁ := CB.cδ₁ P sr c γ')
    (δ₂ := CB.cδ₂ sr γ') (CB.Om γ') (by positivity : 0 ≤ cfg.K k + P.δU) he hgap hθm hθme
    (by positivity : 0 ≤ w + P.δU * (|CB.cδ₁ P sr c γ'| + 2 * |CB.cδ₂ sr γ'| * (cfg.K k + P.δU)))
  have hvol' : volume (thickening P.δU (offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ')
      (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ'))) ≤
      ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
        4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) := by
    refine (measure_mono hthick).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
    gcongr
  have hset : {p : α × ℝ | CB.src p = sr ∧ CB.cell P p = c ∧
      CB.frame.tr (cfg.b k p.1) p.2 ∈ offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ')
        (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ')} =
      {p | p ∈ S ∧ (fun p : α × ℝ => CB.frame.tr (cfg.b k p.1) p.2) p ∈ offsetMatch
        (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ') (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ')} := by
    ext p; simp [S, and_assoc]
  rw [hset]
  have hδU' : ENNReal.ofReal P.δU ≠ 0 := by simpa using hδU
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  calc _ = (ENNReal.ofReal P.δU)⁻¹ * (lam1 {p | p ∈ S ∧ (fun p : α × ℝ =>
        CB.frame.tr (cfg.b k p.1) p.2) p ∈ offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ')
          (CB.cδ₂ sr γ') w (cfg.K k) (CB.Om γ')} * ENNReal.ofReal P.δU) := by
        rw [mul_comm _ (ENNReal.ofReal P.δU), ← mul_assoc, ENNReal.inv_mul_cancel hδU'
          ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal P.δU)⁻¹ * (CB.capcell P r s' v' sr * volume (thickening P.δU
          (offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ') (CB.cδ₂ sr γ') w (cfg.K k)
            (CB.Om γ')))) := mul_le_mul_right hcells _
    _ ≤ _ := by gcongr

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
