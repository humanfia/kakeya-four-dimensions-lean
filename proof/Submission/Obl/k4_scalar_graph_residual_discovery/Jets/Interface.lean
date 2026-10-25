/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Jets/Interface.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Mathlib
import Submission.WZ.Obl.wz_slab_local_linearity.Covering

/-!
# Scalar-normal data in one zoomed world (paper Def. `a04:scalar-data`, `j = 1`)

This is the interface between the Section-6 reduction of o229 (graph certificate → one zoomed
world) and the Section-5 higher-jet theorem (`prop:higher-jets`).

A zoomed world consists of
* a probability `ν` on an arbitrary measurable trajectory space `Λ`;
* coefficients `c l : Fin 5 → ℝ`, with `x_l(t) = c 0 + c 1 t + c 2 t²` (`zx`) and
  `y_l(t) = c 3 + c 4 t` (`zy`), in zoomed units;
* a measurable set of labelled incidences `E ⊆ Λ × ℝ`;
* a time-only row `F : ℝ → ℝ`; the scalar is `S_l(t) = x_l(t) - F(t) y_l(t)` (`zS`) and the
  residual slope is `R_l(t) = x_l'(t) - F(t) y_l'` (`zR`);
* for every scale `r` a labelling `piece r : Λ → Fin 5 → ℤ` of the trajectories by coefficient
  pieces of diameter at most `r` (for instance floor bins of a grid at a scale just below `r`).

`ScalarNormal ν c E F piece K ζ d` collects the paper's hypotheses at all resolutions between the
floor `ζ` and `1`: bounded coefficients and row, dense labels, the scalar support count `SS`
(as `IntervalAD`), the absolute spatial cap `AC`, row comparison `RC`, residual comparison
`ResC`, and the conditional spatial cap in coefficient pieces `BC`.
-/

namespace Submission.Obl.k4_scalar_graph_residual_discovery.Jets

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- Zoomed hidden coordinate `x_l(t)`. -/
def zx (c : Fin 5 → ℝ) (t : ℝ) : ℝ := c 0 + c 1 * t + c 2 * t ^ 2

/-- Zoomed tangential coordinate `y_l(t)`. -/
def zy (c : Fin 5 → ℝ) (t : ℝ) : ℝ := c 3 + c 4 * t

/-- The scalar `S_l(t) = x_l(t) - F(t) y_l(t)`. -/
def zS (F : ℝ → ℝ) (c : Fin 5 → ℝ) (t : ℝ) : ℝ := zx c t - F t * zy c t

/-- The residual slope `R_l(t) = x_l'(t) - F(t) y_l'`. -/
def zR (F : ℝ → ℝ) (c : Fin 5 → ℝ) (t : ℝ) : ℝ := c 1 + 2 * c 2 * t - F t * c 4

/-- The spacetime point `(t, x_l(t), y_l(t))`. -/
def zpos (c : Fin 5 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, zx c t, zy c t]

/-- The dyadic block of length `2⁻ᵀ` containing `t` (left endpoints included). -/
def dyadicBlock (T : ℕ) (t : ℝ) : Set ℝ :=
  Icc ((⌊t * 2 ^ T⌋ : ℝ) / 2 ^ T) (((⌊t * 2 ^ T⌋ : ℝ) + 1) / 2 ^ T)

/-- Scalar-normal data in one world, at all resolutions between `ζ` and `1`. -/
structure ScalarNormal {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 5 → ℝ)
    (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ d : ℝ) : Prop where
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
  row_le : ∀ p ∈ E, |F p.2| ≤ K
  dense : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  /-- `SS`: the labelled scalar values at one time have upper `d`-dimensional covering counts. -/
  support : ∀ t, IntervalAD ζ d K {s | ∃ l, (l, t) ∈ E ∧ zS F (c l) t = s}
  /-- `AC`: labelled spatial squares of side `q` carry prior mass at most `K q^(1+d)`. -/
  abs_cap : ∀ t a b q, ζ ≤ q → q ≤ 1 →
    ν {l | (l, t) ∈ E ∧ zx (c l) t ∈ Ico a (a + q) ∧ zy (c l) t ∈ Ico b (b + q)} ≤
      ENNReal.ofReal (K * q ^ (1 + d))
  /-- `RC`: the row is Lipschitz in time up to the floor, at labelled times. -/
  row_cmp : ∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ)
  /-- `ResC`: the residual slope is Lipschitz in spacetime up to the floor. -/
  resid_cmp : ∀ p ∈ E, ∀ p' ∈ E, |zR F (c p.1) p.2 - zR F (c p'.1) p'.2| ≤
    K * (‖zpos (c p.1) p.2 - zpos (c p'.1) p'.2‖ + ζ)
  /-- Coefficient pieces at scale `r` have coefficient diameter at most `r`. -/
  piece_diam : ∀ r, ζ ≤ r → r ≤ 1 → ∀ l l', piece r l = piece r l' → ‖c l - c l'‖ ≤ r
  /-- `BC`: the conditional spatial cap inside a coefficient piece. -/
  bin_cap : ∀ r, ζ ≤ r → r ≤ 1 → ∀ (b : Fin 5 → ℤ) (t a a' q : ℝ), ζ ≤ q → q ≤ r →
    ν {l | piece r l = b ∧ (l, t) ∈ E ∧ zx (c l) t ∈ Ico a (a + q) ∧ zy (c l) t ∈ Ico a' (a' + q)} ≤
      ENNReal.ofReal (K * (q / r) ^ (1 + d)) * ν {l | piece r l = b}

/-- The fitting conclusion of the higher-jet theorem at one labelled incidence. -/
def JetFit {Λ : Type*} (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (M T : ℕ) (C δ τ : ℝ) (p : Λ × ℝ)
    (P : Polynomial ℝ) : Prop :=
  P.natDegree ≤ M ∧ (∀ i, |P.coeff i| ≤ C) ∧ |F p.2 - P.eval p.2| ≤ δ ∧
    ENNReal.ofReal τ ≤
      volume {v : ℝ | v ∈ dyadicBlock T p.2 ∧ (p.1, v) ∈ E ∧ |F v - P.eval v| ≤ δ}

/-- **Higher-jet polynomial fitting** (paper Prop. `prop:higher-jets`, `j = 1`), in the
fixed-power form used by o229: for fixed `d < 1`, degree `M ≥ 2`, block exponent `c_h` and
loss `ε`, there are a floor exponent `c_ζ`, a constant-budget exponent `α` and a threshold `N₀`
such that every scalar-normal world with constants `K ≤ N ^ α`, dyadic block length
`h = 2⁻ᵀ ≈ N ^ (-c_h)` and floor `ζ ≤ h ^ c_ζ` has a labelled incidence with a degree-`M`
polynomial fit of the row, with coefficients `≤ N ^ ε`, error `h ^ (M + 1/8)`, on labelled times
of its own trajectory in its own block of total length `≥ h N ^ (-ε)`. -/
def HigherJetsStatement : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ M : ℕ, 2 ≤ M → ∀ c_h : ℝ, 0 < c_h →
    ∃ c_ζ : ℝ, 0 < c_ζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type) [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 5 → ℝ) (E : Set (Λ × ℝ))
        (F : ℝ → ℝ) (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ : ℝ) (T : ℕ),
        K ≤ N ^ α → N ^ (-c_h) / K ≤ ((2 : ℝ) ^ T)⁻¹ → ((2 : ℝ) ^ T)⁻¹ ≤ K * N ^ (-c_h) →
        ζ ≤ ((2 : ℝ) ^ T)⁻¹ ^ c_ζ → ScalarNormal ν c E F piece K ζ d →
        ∃ p ∈ E, ∃ P : Polynomial ℝ, JetFit E F M T (N ^ ε) (((2 : ℝ) ^ T)⁻¹ ^ ((M : ℝ) + 1 / 8))
          (((2 : ℝ) ^ T)⁻¹ * N ^ (-ε)) p P

end

end Submission.Obl.k4_scalar_graph_residual_discovery.Jets
