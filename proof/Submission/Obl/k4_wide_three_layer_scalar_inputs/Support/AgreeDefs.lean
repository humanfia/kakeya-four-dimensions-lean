import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.GoodBounds
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.PointMatch
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.MatchCells
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Sigma

set_option linter.unusedVariables false

/-!
# Coefficient agreement for a compared block: definitions and the matching step

Fine states, coefficient classes (coarse predictors), sources (coarse predictor and layer-1
offset bin), time cells, the reference base point of a source cell, the target charts near it,
and the matching sets of a source cell and a target.  The matching step: if a target occurs at
the fine state of a good incidence and disagrees there, its chart crosses the source cell and the
transverse coordinate of the incidence lies in the matching set.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H : ℝ}

/-- Resolutions and thresholds of the coefficient agreement. -/
structure AgreeParams where
  δz : ℝ
  δU : ℝ
  δX : ℝ
  δt : ℝ
  eR : ℝ
  e : ℝ

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- The fine state. -/
def sig (p : α × ℝ) : Fin 4 → ℤ := sigmaState CB.frame P.δz P.δU P.δX (cfg.b k p.1) p.2

/-- The coefficient class (coarse predictor). -/
def cls (p : α × ℝ) : CB.Γ := CB.crs (CB.lab p.1)

/-- The base center of a fine state. -/
def zcx (q : Fin 4 → ℤ) : ℝ := ((q 0 : ℝ) + 1 / 2) * P.δz
def zcy (q : Fin 4 → ℤ) : ℝ := ((q 1 : ℝ) + 1 / 2) * P.δz

/-- The nonconstant transverse coefficient gap of two classes at a base point. -/
def gapAt (γ γ' : CB.Γ) (x y : ℝ) : ℝ :=
  |lin1 (CB.tc γ) x y - lin1 (CB.tc γ') x y| + |CB.tc γ 3 - CB.tc γ' 3|

/-- Agreement at a fine state. -/
def Rg (q : Fin 4 → ℤ) (γ γ' : CB.Γ) : Prop := CB.gapAt γ γ' (zcx P q) (zcy P q) < P.eR

/-- The source: coefficient class and layer-1 offset bin. -/
def src (p : α × ℝ) : CB.Γ × ℤ := (CB.cls p, ⌊CB.D1 (CB.lab p.1) / cfg.N k ^ (-u)⌋)

/-- The time cell. -/
def cell (p : α × ℝ) : ℤ := ⌊CB.frame.zt p.2 / P.δt⌋

/-- Reference time of a time cell (normalized and original). -/
def refX (c : ℤ) : ℝ := ((c : ℝ) + 1 / 2) * P.δt
def refT (c : ℤ) : ℝ := CB.frame.t₀ + CB.frame.q * refX P c

/-- The chart center line of a coefficient class at the reference time. -/
def x1ref (γ : CB.Γ) (c : ℤ) : ℝ :=
  (((CB.chartOf γ).2 : ℝ) + 1 / 2) * χ + CB.refT P c * (((CB.chartOf γ).1 : ℝ) + 1 / 2) * χ

def refZ (γ : CB.Γ) (c : ℤ) : ℝ :=
  (CB.x1ref P γ c - CB.frame.c 0 - CB.refT P c * CB.frame.c 1) / CB.frame.q

/-- Target classes whose chart crosses the source cell. -/
def Near (ρN : ℝ) (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ) : Prop :=
  |(((CB.chartOf γ').2 : ℝ) + 1 / 2) * χ -
      (CB.x1ref P sr.1 c - CB.refT P c * (((CB.chartOf γ').1 : ℝ) + 1 / 2) * χ)| ≤ ρN ∧
    γ' ∈ CB.G (CB.chartOf γ')

/-- Coefficients of the difference of the two predictors at the reference point. -/
def cδ₀ (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ) : ℝ :=
  quadZ (CB.pc sr.1) (refX P c) (CB.refZ P sr.1 c) + (sr.2 : ℝ) * cfg.N k ^ (-u) -
    quadZ (CB.pc γ') (refX P c) (CB.refZ P sr.1 c)

def cδ₁ (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ) : ℝ :=
  lin1 (CB.tc sr.1) (refX P c) (CB.refZ P sr.1 c) - lin1 (CB.tc γ') (refX P c) (CB.refZ P sr.1 c)

def cδ₂ (sr : CB.Γ × ℤ) (γ' : CB.Γ) : ℝ := CB.tc sr.1 3 - CB.tc γ' 3

/-- Offsets of a target class. -/
def Om (γ' : CB.Γ) : Finset ℝ :=
  (CB.F1 (CB.chartOf γ') γ').image (fun d : ℤ => (d : ℝ) * cfg.N k ^ (-u))

/-- The matching set of a source cell and a target class. -/
def Mset (w Lu : ℝ) (sr : CB.Γ × ℤ) (c : ℤ) (γ' : CB.Γ) : Set ℝ :=
  if P.e ≤ |CB.cδ₁ P sr c γ'| + |CB.cδ₂ sr γ'| then
    offsetMatch (CB.cδ₀ P sr c γ') (CB.cδ₁ P sr c γ') (CB.cδ₂ sr γ') w Lu (CB.Om γ')
  else ∅

theorem sig_close {p p' : α × ℝ} (hδz : 0 < P.δz) (hδU : 0 < P.δU) (hδX : 0 < P.δX)
    (h : CB.sig P p = CB.sig P p') :
    |CB.frame.zt p.2 - CB.frame.zt p'.2| < P.δz ∧
    |CB.frame.zZ (cfg.b k p.1) p.2 - CB.frame.zZ (cfg.b k p'.1) p'.2| < P.δz ∧
    |CB.frame.tr (cfg.b k p.1) p.2 - CB.frame.tr (cfg.b k p'.1) p'.2| < P.δU ∧
    |CB.frame.resid (cfg.b k p.1) p.2 - CB.frame.resid (cfg.b k p'.1) p'.2| < P.δX := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [sig, sigmaState, coords, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
  exact ⟨abs_sub_lt_of_floor_eq hδz h0, abs_sub_lt_of_floor_eq hδz h1,
    abs_sub_lt_of_floor_eq hδU h2, abs_sub_lt_of_floor_eq hδX h3⟩

theorem gapAt_comm (γ γ' : CB.Γ) (x y : ℝ) : CB.gapAt γ γ' x y = CB.gapAt γ' γ x y := by
  simp only [gapAt]; rw [abs_sub_comm, abs_sub_comm (CB.tc γ 3)]

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
