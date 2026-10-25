import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.Planar

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The scalar-normal first jet in list form (statement)

Paper Definition 5.3 (`a04:scalar-data`) and Proposition 5.4 (`prop:scalar-normal`) in the case
used by the parameter bootstrap (paper "One bootstrap step"): `j = 2`, static tangential
coordinates `y_l ∈ ℝ²`, affine scalars `x̄_l(t) = x0 l + t x1 l`, a time-only row `F(t) ∈ ℝ²`,
`S_l(t) = x̄_l(t) - F(t) · y_l` and residual slope `R_l = x̄'_l = x1 l` (as `y' = 0`).

`JetHyp D ζ K d` collects the hypotheses at floor `ζ` with subpower constant `K`:
bounds, the scalar support count (`a04:scalar-support`), the absolute cap (`a04:absolute-cap`),
the row and residual comparisons (`a04:row-comparison`, `a04:residual-comparison`), the
dense labels (the coefficient-bin caps `a04:bin-cap` are not needed for the row fits and are
not assumed here).

`JetList D E' A list w K'` is the list form of the first-jet conclusion at reading scale `w`:
dense sub-labels `E'`, a bounded time-only row `A`, and for every time and scalar `w`-bin a list
of at most `K'` bins of the residual slope `J₁ = x̄' - A(t) · y` (paper: "subpower lists of the
indicated residual bin", obtained from the entropy statement `a04:first-jet-entropy`; here the
paper's final deterministic cover and its fine-to-coarse transfer give the list directly).

`FirstJetList` is the asymptotic statement: finest length `H = N^{-cH}`, floor `ζ = N^{-3cH}`
(`ζ ≤ H³`), reading scale `w = N^{-cw}` with `cw ≤ cH (1-d)/64` (`w ≥ H^{(1-d)/64}`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

/-- The data of a scalar-normal chart: prior, labels, affine scalar, static tangential
coordinates and a time-only row. -/
structure JetData (Ω : Type*) [MeasurableSpace Ω] where
  ν : Measure Ω
  E : Set (Ω × ℝ)
  x0 : Ω → ℝ
  x1 : Ω → ℝ
  y : Ω → Fin 2 → ℝ
  F : ℝ → Fin 2 → ℝ

namespace JetData

variable {Ω : Type*} [MeasurableSpace Ω] (D : JetData Ω)

/-- The affine scalar `x̄_l(t)`. -/
def xb (l : Ω) (t : ℝ) : ℝ := D.x0 l + t * D.x1 l

/-- The row applied to the static coordinates. -/
def Fy (t : ℝ) (l : Ω) : ℝ := D.F t 0 * D.y l 0 + D.F t 1 * D.y l 1

/-- The normal scalar `S_l(t) = x̄_l(t) - F(t) · y_l`. -/
def S (l : Ω) (t : ℝ) : ℝ := D.xb l t - D.Fy t l

/-- The residual slope `J₁ = x̄'_l - A(t) · y_l` for a row `A`. -/
def J1 (A : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) : ℝ := D.x1 l - (A t 0 * D.y l 0 + A t 1 * D.y l 1)

/-- The spatial `q`-cube of `(x̄_l(t), y_l)`. -/
def cube (q : ℝ) (l : Ω) (t : ℝ) : Fin 3 → ℤ :=
  ![⌊D.xb l t / q⌋, ⌊D.y l 0 / q⌋, ⌊D.y l 1 / q⌋]

/-- The coefficient `r`-bin of `(x0, x1, y)`. -/
def coeffBin (r : ℝ) (l : Ω) : Fin 4 → ℤ :=
  ![⌊D.x0 l / r⌋, ⌊D.x1 l / r⌋, ⌊D.y l 0 / r⌋, ⌊D.y l 1 / r⌋]

end JetData

/-- The hypotheses of the scalar-normal first jet (paper Definition 5.3, `j = 2`, static `y`,
affine `x̄`) at floor `ζ`, subpower constant `K` and dimension `d`. -/
structure JetHyp {Ω : Type*} [MeasurableSpace Ω] (D : JetData Ω) (ζ K d : ℝ) : Prop where
  prob : IsProbabilityMeasure D.ν
  measE : MeasurableSet D.E
  E01 : ∀ q ∈ D.E, q.2 ∈ Icc (0:ℝ) 1
  meas_x0 : Measurable D.x0
  meas_x1 : Measurable D.x1
  meas_y : ∀ i, Measurable (fun l => D.y l i)
  meas_F : ∀ i, Measurable (fun t => D.F t i)
  bound_x : ∀ l, |D.x0 l| + |D.x1 l| ≤ K
  bound_y : ∀ l i, |D.y l i| ≤ K
  bound_F : ∀ t i, |D.F t i| ≤ K
  /-- `a04:scalar-support`: at every time the normal scalars have local upper `d`-count. -/
  supp : ∀ t, LocalCount {s | ∃ l, (l, t) ∈ D.E ∧ s = D.S l t} ζ K d
  /-- `a04:absolute-cap`. -/
  abscap : ∀ (t q : ℝ), ζ ≤ q → q ≤ 1 → ∀ m : Fin 3 → ℤ,
    D.ν {l | (l, t) ∈ D.E ∧ D.cube q l t = m} ≤ ENNReal.ofReal (K * q ^ (2 + d))
  /-- `a04:row-comparison`, at labeled times. -/
  rowcomp : ∀ l t l' u, (l, t) ∈ D.E → (l', u) ∈ D.E → ∀ i,
    |D.F t i - D.F u i| ≤ K * (|t - u| + ζ)
  /-- `a04:residual-comparison` (the residual slope is `x1`, as `y` is static). -/
  rescomp : ∀ l t l' u, (l, t) ∈ D.E → (l', u) ∈ D.E →
    |D.x1 l - D.x1 l'| ≤ K * (|t - u| + |D.xb l t - D.xb l' u| + |D.y l 0 - D.y l' 0| +
      |D.y l 1 - D.y l' 1| + ζ)
  /-- Dense labels. -/
  mass : ENNReal.ofReal (1 / K) ≤ (D.ν.prod volume) D.E

/-- The list form of the first-jet conclusion at reading scale `w` with constant `K'`. -/
def JetList {Ω : Type*} [MeasurableSpace Ω] (D : JetData Ω) (E' : Set (Ω × ℝ))
    (A : ℝ → Fin 2 → ℝ) (list : ℝ → ℤ → Finset ℤ) (w K' : ℝ) : Prop :=
  E' ⊆ D.E ∧ MeasurableSet E' ∧ ENNReal.ofReal (1 / K') ≤ (D.ν.prod volume) E' ∧
    (∀ t i, |A t i| ≤ K') ∧ (∀ t s, ((list t s).card : ℝ) ≤ K') ∧
    ∀ q ∈ E', ⌊D.J1 A q.1 q.2 / w⌋ ∈ list q.2 ⌊D.S q.1 q.2 / w⌋

/-- **The scalar-normal first jet, list form** (asymptotic statement). -/
def FirstJetList : Prop :=
  ∀ (d cH cw : ℝ), 0 ≤ d → d < 1 → 0 < cH → 0 < cw → cw ≤ cH * (1 - d) / 64 →
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Ω : Type) [MeasurableSpace Ω] (D : JetData Ω), JetHyp D (N ^ (-3 * cH)) (N ^ η) d →
        ∃ (E' : Set (Ω × ℝ)) (A : ℝ → Fin 2 → ℝ) (list : ℝ → ℤ → Finset ℤ),
          JetList D E' A list (N ^ (-cw)) (N ^ ε)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
