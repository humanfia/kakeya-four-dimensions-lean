import Submission.Obl.k4_scalar_candidate_original_return.Core.Globalize
import Submission.Obl.k4_scalar_candidate_original_return.Core.Posterior
import Submission.Obl.k4_scalar_candidate_original_return.Core.MatchApply
import Submission.Obl.k4_scalar_candidate_original_return.Core.Cells
import Submission.Obl.k4_scalar_candidate_original_return.Core.Normalize

/-!
# Per-plank comparison data

For a fixed scenario and slack (`CmpParams`), a stage `k`, a layer `ℓ` and a plank `i`:
the greedy candidates `cand m`, their first-fit line assignments `asg m` and covered
incidences `cvd m`; coarse records of the original observation; the plank normalization
`psi` (ζ-coordinates: the plank's lines lie in `[1/3,2/3] × [1/4,3/4]`); the normalized graphs
`Gζ m = N^{s₀}(P_m - F_i) ∘ psi` and `Gz m = Gζ m (2 z + 1/2)` (the plank lies in the square of
half-width `1/4`); and the six-point jet bins at step `N^{-εm c₀}`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial
open Submission.Lib.K4FinitePlankAtlases

noncomputable section

/-- Fixed numerical parameters of the comparison. -/
structure CmpParams where
  θ : ℝ
  εm : ℝ
  R₀ : ℝ
  σ : Scenario

namespace CmpParams

variable (π : CmpParams)

/-- Hidden-coordinate exponent of a candidate fit: `fitTol = N^{-s'}`. -/
def s' : ℝ := π.σ.s₀ + π.σ.c₀ - π.θ * π.σ.c₀

/-- Base-cell exponent. -/
def r : ℝ := (π.σ.R : ℝ) + 3 * π.σ.s₀ + π.σ.c₀ + 2

end CmpParams

/-- The base cell of exponent `r` with integer index `q`. -/
def baseBox (N r : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {u | ∀ e, ⌊u e / N ^ (-r)⌋ = q e}

namespace PreparedData

variable (a : PreparedData) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)

/-- Number of greedy candidates of the plank. -/
def ncand : ℕ := (a.greedy π.θ π.σ k ℓ i).length

/-- The candidates. -/
def cand (m : Fin (a.ncand π k ℓ i)) : Poly := (a.greedy π.θ π.σ k ℓ i).get m

/-- Lines of the plank fitting candidate `m` on the whole block. -/
def fitSet (m : Fin (a.ncand π k ℓ i)) : Set Line :=
  (a.ls k ℓ).prior i ∩
    Fit (a.cand π k ℓ i m) (a.tStart k ℓ i) (a.tEnd k ℓ i) (a.fitTol π.θ π.σ k)

/-- First-fit assignment of the plank's lines to candidates. -/
def asg (m : Fin (a.ncand π k ℓ i)) : Set Line := firstAssignment (a.fitSet π k ℓ i) m

/-- Covered incidences of candidate `m`. -/
def cvd (m : Fin (a.ncand π k ℓ i)) : Set Inc :=
  a.asg π k ℓ i m ×ˢ I (a.ls k ℓ).T ((a.ls k ℓ).time i)

/-- The original hidden-bin resolution of the frozen observation. -/
def obsRes : ℝ := a.original k ^ (-L (a.p k))

/-- The frozen original observation of an incidence. -/
def obs (p : Inc) : (Fin 2 → ℝ) × ℤ := (![p.2, y p.1 p.2], ⌊x p.1 p.2 / a.obsRes k⌋)

/-- Number of original hidden bins grouped in one coarse hidden bin. -/
def mzero : ℕ := ⌊a.fitTol π.θ π.σ k / a.obsRes k⌋₊

/-- The coarse record of an observation: base cell at exponent `r`, grouped hidden bin. -/
def recObs (z : (Fin 2 → ℝ) × ℤ) : (Fin 2 → ℤ) × ℤ :=
  ((fun e => ⌊z.1 e / a.tangent k ^ (-π.r)⌋), ⌊(z.2 : ℝ) / (a.mzero π k : ℝ)⌋)

/-- The coarse record of an incidence. -/
def recordOf (p : Inc) : (Fin 2 → ℤ) × ℤ := a.recObs π k (a.obs k p)

/-- Linear part of the ζ-normalization of plank `i`. -/
def psiA : Fin 2 → Fin 2 → ℝ :=
  ![![3 / (2 : ℝ) ^ (a.ls k ℓ).T, 0],
    ![3 * (a.ls k ℓ).v i / (2 : ℝ) ^ (a.ls k ℓ).T, 4 * a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T]]

/-- Translation part of the ζ-normalization of plank `i`. -/
def psib : Fin 2 → ℝ :=
  ![a.tStart k ℓ i - 1 / (2 : ℝ) ^ (a.ls k ℓ).T,
    (a.ls k ℓ).u i + (a.ls k ℓ).v i * (a.tStart k ℓ i - 1 / (2 : ℝ) ^ (a.ls k ℓ).T) -
      2 * a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T]

/-- The base point `(t, y)` of normalized coordinates `ζ`:
`t = tStart + (3ζ₀ - 1)/2^T`, `y = u + t v + K (4ζ₁ - 2)/2^T`. -/
def psi (ζ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun e => a.psiA k ℓ i e 0 * ζ 0 + a.psiA k ℓ i e 1 * ζ 1 + a.psib k ℓ i e

/-- Normalized coordinates of a base point (inverse of `psi`). -/
def zeta (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![((2 : ℝ) ^ (a.ls k ℓ).T * (u 0 - a.tStart k ℓ i) + 1) / 3,
    ((2 : ℝ) ^ (a.ls k ℓ).T * (u 1 - (a.ls k ℓ).u i - u 0 * (a.ls k ℓ).v i) / a.rK k + 2) / 4]

/-- The normalized graph difference `N^{s₀} (P_m - F_i) ∘ psi` in ζ-coordinates. -/
def Gzeta (m : Fin (a.ncand π k ℓ i)) : Poly :=
  Normalize.affSubst
    (C (a.tangent k ^ π.σ.s₀) * (a.cand π k ℓ i m - (a.ls k ℓ).poly i))
    (a.psiA k ℓ i) (a.psib k ℓ i)

/-- The plank's own fit polynomial in ζ-coordinates. -/
def Fzeta : Poly := Normalize.affSubst ((a.ls k ℓ).poly i) (a.psiA k ℓ i) (a.psib k ℓ i)

/-- The normalized graph difference in matching coordinates `z` (`ζ = 2 z + 1/2`). -/
def Gz (m : Fin (a.ncand π k ℓ i)) : Poly :=
  Normalize.affSubst (a.Gzeta π k ℓ i m) ![![2, 0], ![0, 2]] ![1 / 2, 1 / 2]

/-- Matching coordinates of a base point. -/
def zOf (u : Fin 2 → ℝ) : Fin 2 → ℝ := fun e => (a.zeta k ℓ i u e - 1 / 2) / 2

/-- The matching cell of a base cell: the matching coordinates whose base point lies in it. -/
def cellZ (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {z | a.psi k ℓ i (fun e => 2 * z e + 1 / 2) ∈ baseBox (a.tangent k) π.r q}

/-- Base cells whose matching cell lies in the square of half-width `1/4`. -/
def GoodCell : Type :=
  {q : Fin 2 → ℤ // a.cellZ π k ℓ i q ⊆ MatchApply.sq (1 / 4)}

/-- Covered mass of candidate `m` on a record. -/
def recMass (m : Fin (a.ncand π k ℓ i)) (O : (Fin 2 → ℤ) × ℤ) : ENNReal :=
  a.ρ k ((a.ls k ℓ).world i) (a.cvd π k ℓ i m ∩ a.recordOf π k ⁻¹' {O})

/-- Total covered mass on a record. -/
def recTotal (O : (Fin 2 → ℤ) × ℤ) : ENNReal :=
  a.ρ k ((a.ls k ℓ).world i) ((⋃ m, a.cvd π k ℓ i m) ∩ a.recordOf π k ⁻¹' {O})

/-- The conditional pair law on records, indexed by good cells. -/
def pairW (m m' : Fin (a.ncand π k ℓ i)) (q : a.GoodCell π k ℓ i) (c : ℤ) : ENNReal :=
  a.recMass π k ℓ i m (q.1, c) * a.recMass π k ℓ i m' (q.1, c) / a.recTotal π k ℓ i (q.1, c)

/-- The jet step `N^{-εm c₀}`. -/
def jetStep : ℝ := a.tangent k ^ (-(π.εm * π.σ.c₀))

/-- Six-point jet bins of the normalized graphs. -/
def jetBin (m : Fin (a.ncand π k ℓ i)) : Fin 6 → ℤ :=
  fun j => ⌊eval (QuadBounds.sixPts j) (a.Gz π k ℓ i m) / a.jetStep π k⌋

/-- Neighbouring bins. -/
def Nbr (b b' : Fin 6 → ℤ) : Prop := ∀ j, |b j - b' j| ≤ 1

/-- The common smallness exponent `θ c₀ / 1000`. -/
def kap0 : ℝ := π.θ * π.σ.c₀ / 1000

/-- Everything the per-plank comparison may use at stage `k`, for plank `i` of layer `ℓ`
(tangent depth `s`): tangent-input facts at `s`, the layer's line bounds, the
non-concentration at the cell exponents, and numerical smallness of all slacks. -/
structure PlankHyp (s : ℝ) : Prop where
  par_pos : 0 < π.σ.s₀ ∧ 0 < π.σ.c₀ ∧ 0 < π.θ ∧ π.θ ≤ π.εm / 16 ∧ 0 < π.εm ∧ π.εm ≤ 1 / 2
  d_range : 0 ≤ a.rd ∧ a.rd < 1
  κ_range : 0 < a.κ ∧ a.κ ≤ 1
  s_win : |s - π.σ.s₀| ≤ π.θ * π.σ.c₀ / 4 ∧ |s - π.σ.s₀| ≤ π.σ.s₀ / 2
  N_ge : 2 ≤ a.tangent k
  K_ge : 1 ≤ a.rK k
  H_ge : 2 ≤ a.H k
  K_small : a.rK k ≤ a.tangent k ^ (kap0 π)
  H_small : a.H k ≤ a.tangent k ^ (kap0 π)
  N_large : (10 : ℝ) ^ 30 ≤ a.tangent k ^ (kap0 π)
  R0_le : π.R₀ ≤ a.tangent k ^ π.σ.c₀
  obs_small : a.obsRes k ≤ a.tangent k ^ (-π.s') / 4
  T_lower : a.tangent k ^ (a.κ * s) / a.rK k ≤ (2 : ℝ) ^ (a.ls k ℓ).T
  T_upper : (2 : ℝ) ^ (a.ls k ℓ).T ≤ a.rK k * a.tangent k ^ (a.κ * s)
  nu_lower : ENNReal.ofReal (a.tangent k ^ (-a.rd * s) / (a.rK k * (2 : ℝ) ^ (a.ls k ℓ).T)) ≤
    ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)
  nu_upper : ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) ≤
    ENNReal.ofReal (a.rK k * a.tangent k ^ (-a.rd * s) / (2 : ℝ) ^ (a.ls k ℓ).T)
  nu_prob : IsProbabilityMeasure (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i))
  rho_le : a.ρ k ((a.ls k ℓ).world i) ≤
    ENNReal.ofReal (a.rK k) • ((ν (a.p k) (a.sm k) ((a.ls k ℓ).world i)).prod volume)
  rho_finite : IsFiniteMeasure (a.ρ k ((a.ls k ℓ).world i))
  uv_le : |(a.ls k ℓ).u i| + |(a.ls k ℓ).v i| ≤ a.rK k
  F_deg : ((a.ls k ℓ).poly i).totalDegree ≤ 2
  F_bound : ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
    |MvPolynomial.eval ![t, (a.ls k ℓ).u i + t * (a.ls k ℓ).v i + w / (2 : ℝ) ^ (a.ls k ℓ).T]
      ((a.ls k ℓ).poly i)| ≤ a.rK k
  fit : ∀ l ∈ (a.ls k ℓ).prior i, ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i),
    |y l t - (a.ls k ℓ).u i - t * (a.ls k ℓ).v i| ≤ a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T ∧
    |x l t - MvPolynomial.eval ![t, y l t] ((a.ls k ℓ).poly i)| ≤
      a.rK k * a.tangent k ^ (-s)
  lines : ∀ l ∈ (a.ls k ℓ).prior i, ∀ e, |l.2 e| ≤ a.H k
  prior_meas : MeasurableSet ((a.ls k ℓ).prior i)
  noncon : ∀ (q : Fin 2 → ℤ) (c : ℤ),
    a.ρ k ((a.ls k ℓ).world i)
      {p | baseBin (a.tangent k) π.r p = q ∧ hiddenBin (a.tangent k) π.s' p = c} ≤
      ENNReal.ofReal (a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s'))

end PreparedData

end

end Submission.Obl.k4_scalar_candidate_original_return
