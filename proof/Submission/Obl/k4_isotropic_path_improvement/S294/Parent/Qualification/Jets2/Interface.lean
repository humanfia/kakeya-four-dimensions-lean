-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Jets2.Interface, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Jets2/Interface.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/Interface.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/Jets2/Interface.lean.
-- Existing source attributions are preserved below.

import Mathlib
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

/-!
# Scalar-normal data in one zoomed world, version 2 (paper Def. `a04:scalar-data`, `j = 2`)

This interface is from this LOT tree, o106, session x0358, branch x0358,
commit 0bc78744c544fdffbd857f8e1a27334edbe5df34.

Adapted from this LOT tree: obligation o229 (`k4_scalar_grid_polynomial_qualification`),
session x0801, branch `x0801` at commit `b03d2c4a`, file `Jets/Interface.lean`, which states the
interface for `j = 1`.  Here the tangential position lies in `ℝ²` (paper `tex-06-isotropic.tex`,
l. 17–18: version 2 has `j = 2`), as needed by o106's isotropic step.

A zoomed world consists of
* a probability `ν` on an arbitrary measurable trajectory space `Λ`;
* coefficients `c l : Fin 7 → ℝ`, with `x_l(t) = c 0 + c 1 t + c 2 t²` (`zx`) and
  `y_l(t) = (c 3 + c 4 t, c 5 + c 6 t)` (`zy`), velocity `y_l' = (c 4, c 6)` (`zv`);
* a measurable set of labelled incidences `E ⊆ Λ × ℝ`;
* a time-only row `F : ℝ → Fin 2 → ℝ`; the scalar is `S_l(t) = x_l(t) - F(t) · y_l(t)` (`zS`)
  and the residual slope is `R_l(t) = x_l'(t) - F(t) · y_l'` (`zR`);
* for every scale `r` a labelling `piece r : Λ → Fin 7 → ℤ` of the trajectories by coefficient
  pieces of diameter at most `r`.

`ScalarNormal ν c E F piece K ζ d` collects the paper's hypotheses at all resolutions between the
floor `ζ` and `1`: bounded coefficients and row, dense labels, the scalar support count `SS`
(as `IntervalAD`), the absolute spatial cap `AC` on cubes of `ℝ³ = (x, y)`, row comparison `RC`,
residual comparison `ResC`, and the conditional spatial cap in coefficient pieces `BC`.
Norms on `Fin n → ℝ` are sup norms.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- Zoomed hidden coordinate `x_l(t)`. -/
def zx (c : Fin 7 → ℝ) (t : ℝ) : ℝ := c 0 + c 1 * t + c 2 * t ^ 2

/-- Zoomed tangential position `y_l(t) ∈ ℝ²`. -/
def zy (c : Fin 7 → ℝ) (t : ℝ) : Fin 2 → ℝ := ![c 3 + c 4 * t, c 5 + c 6 * t]

/-- The tangential velocity `y_l'`. -/
def zv (c : Fin 7 → ℝ) : Fin 2 → ℝ := ![c 4, c 6]

/-- The scalar `S_l(t) = x_l(t) - F(t) · y_l(t)`. -/
def zS (F : ℝ → Fin 2 → ℝ) (c : Fin 7 → ℝ) (t : ℝ) : ℝ := zx c t - F t ⬝ᵥ zy c t

/-- The residual slope `R_l(t) = x_l'(t) - F(t) · y_l'`. -/
def zR (F : ℝ → Fin 2 → ℝ) (c : Fin 7 → ℝ) (t : ℝ) : ℝ := c 1 + 2 * c 2 * t - F t ⬝ᵥ zv c

/-- The spacetime point `(t, x_l(t), y_l(t))`. -/
def zpos (c : Fin 7 → ℝ) (t : ℝ) : Fin 4 → ℝ := ![t, zx c t, zy c t 0, zy c t 1]

/-- The dyadic block of length `2⁻ᵀ` containing `t` (left endpoints included). -/
def dyadicBlock (T : ℕ) (t : ℝ) : Set ℝ :=
  Icc ((⌊t * 2 ^ T⌋ : ℝ) / 2 ^ T) (((⌊t * 2 ^ T⌋ : ℝ) + 1) / 2 ^ T)

/-- The spatial cube `[a, a + q) × [b₀, b₀ + q) × [b₁, b₁ + q)` in `(x, y)`, read at time `t`. -/
def InCube (c : Fin 7 → ℝ) (t a : ℝ) (b : Fin 2 → ℝ) (q : ℝ) : Prop :=
  zx c t ∈ Ico a (a + q) ∧ ∀ i, zy c t i ∈ Ico (b i) (b i + q)

/-- Scalar-normal data in one world, at all resolutions between `ζ` and `1` (version 2). -/
structure ScalarNormal {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ d : ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  one_le_K : 1 ≤ K
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  measurable_c : Measurable c
  measurableSet_E : MeasurableSet E
  measurable_F : Measurable F
  measurable_piece : ∀ r, Measurable (piece r)
  time_mem : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1
  coeff_le : ∀ p ∈ E, ∀ e, |c p.1 e| ≤ K
  row_le : ∀ p ∈ E, ‖F p.2‖ ≤ K
  dense : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  /-- `SS`: the labelled scalar values at one time have upper `d`-dimensional covering counts. -/
  support : ∀ t, IntervalAD ζ d K {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s}
  /-- `AC`: labelled spatial cubes of side `q` carry prior mass at most `K q^(2+d)`. -/
  abs_cap : ∀ t a (b : Fin 2 → ℝ) q, ζ ≤ q → q ≤ 1 →
    ν {l | (l, t) ∈ E ∧ InCube (c l) t a b q} ≤ ENNReal.ofReal (K * q ^ (2 + d))
  /-- `RC`: the row is Lipschitz in time up to the floor, at labelled times. -/
  row_cmp : ∀ p ∈ E, ∀ p' ∈ E, ‖F p.2 - F p'.2‖ ≤ K * (|p.2 - p'.2| + ζ)
  /-- `ResC`: the residual slope is Lipschitz in spacetime up to the floor. -/
  resid_cmp : ∀ p ∈ E, ∀ p' ∈ E, |zR F (c p.1) p.2 - zR F (c p'.1) p'.2| ≤
    K * (‖zpos (c p.1) p.2 - zpos (c p'.1) p'.2‖ + ζ)
  /-- Coefficient pieces at scale `r` have coefficient diameter at most `r`. -/
  piece_diam : ∀ r, ζ ≤ r → r ≤ 1 → ∀ l l', piece r l = piece r l' → ‖c l - c l'‖ ≤ r
  /-- `BC`: the conditional spatial cap inside a coefficient piece. -/
  bin_cap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ (b : Fin 7 → ℤ) (t a : ℝ) (b' : Fin 2 → ℝ) (q : ℝ),
    ζ ≤ q → q ≤ r →
    ν {l | piece r l = b ∧ (l, t) ∈ E ∧ InCube (c l) t a b' q} ≤
      ENNReal.ofReal (K * (q / r) ^ (2 + d)) * ν {l | piece r l = b}

/-- The fitting conclusion of the higher-jet theorem at one labelled incidence: a row-valued
polynomial `P` (one polynomial per component). -/
def JetFit {Λ : Type*} (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (M T : ℕ) (C δ τ : ℝ) (p : Λ × ℝ)
    (P : Fin 2 → Polynomial ℝ) : Prop :=
  (∀ i, (P i).natDegree ≤ M) ∧ (∀ i k, |(P i).coeff k| ≤ C) ∧
    (∀ i, |F p.2 i - (P i).eval p.2| ≤ δ) ∧
    ENNReal.ofReal τ ≤
      volume {v : ℝ | v ∈ dyadicBlock T p.2 ∧ (p.1, v) ∈ E ∧ ∀ i, |F v i - (P i).eval v| ≤ δ}

/-- **Higher-jet polynomial fitting** (paper Prop. `prop:higher-jets`, `j = 2`), in the
fixed-power form of the `j = 1` statement of o229 (x0801): for fixed `d < 1`, degree `M ≥ 2`,
block exponent `c_h` and loss `ε`, there are a floor exponent `c_ζ`, a constant-budget exponent
`α` and a threshold `N₀` such that every version-2 scalar-normal world with constants
`K ≤ N ^ α`, dyadic block length `h = 2⁻ᵀ ≈ N ^ (-c_h)` and floor `ζ ≤ h ^ c_ζ` has a labelled
incidence with a degree-`M` row-polynomial fit of the row, with coefficients `≤ N ^ ε`, error
`h ^ (M + 1/8)`, on labelled times of its own trajectory in its own block of total length
`≥ h N ^ (-ε)`. -/
def HigherJetsStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ M : ℕ, 2 ≤ M → ∀ c_h : ℝ, 0 < c_h →
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
        (F : ℝ → Fin 2 → ℝ) (piece : ℝ → Λ → Fin 7 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ → ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
        ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → ScalarNormal ν c E F piece K ζ d →
        ∃ p ∈ E, ∃ P : Fin 2 → Polynomial ℝ, JetFit E F M T (N ^ ε)
          (((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8)) (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) p P

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
