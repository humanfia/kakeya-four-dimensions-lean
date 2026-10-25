import Submission.Obl.k4_native_finite_terminal_atlas_lift.FiniteLifting

/-!
# Normalization through given parents

Paper, Lemma 2.13 (`lem:normalization`), as used in Proposition 4.3(2) ("Nested true
systems"): to build nested forests the remainder problem must be normalized through
the parent charts that the forest already contains.

The accepted terminal lifting (o183) works for any `Remainder p q r h w`, whose
parent atlases are part of the structure.  The interface below asks for a remainder
whose parent atlases are sub-atlases of a given sequence of known parents.  Then the
lifted true terminal charts of the remainder are nested in the given parents.
-/

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- One explicitly given known parent atlas at one sample: the conditions of
`KnownAt`, with the atlas and its terminal lists given, and the original slack
dominated by the atlas slack. -/
def KnownParentAt (p : Data) (M D : ℕ) (r h w ε : ℝ) {k : ℕ} (a : Atlas p k)
    (lst : Fin (p.W k) → Observation → Finset (Fin a.C)) : Prop :=
  1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
    (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧
    (∀ γ o, ((lst γ o).card : ℝ) ≤ a.κ) ∧
    (∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b))
      (p.E k (a.γ b)) (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b)
      (∀ z ∈ a.F b, b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))) ∧
    ENNReal.ofReal a.κ⁻¹ ≤ a.mass

/-- `a'` (at sample `k'`) is a sub-atlas of `a` (at sample `k`) through `e`: the same
sample, the same time partition, and every retained chart keeps its world, block,
center, velocity, frame, test and full assignment; only its incidence selection may
shrink.  Worlds and blocks are compared as natural numbers, so that the two samples
need not be definitionally equal. -/
def SubAtlas {p : Data} {k k' : ℕ} (a' : Atlas p k') (a : Atlas p k)
    (e : Fin a'.C → Fin a.C) : Prop :=
  k' = k ∧ Function.Injective e ∧ a'.T = a.T ∧
    ∀ b, ((a'.γ b : ℕ) = (a.γ (e b) : ℕ)) ∧ ((a'.j b : ℕ) = (a.j (e b) : ℕ)) ∧
      a'.c b = a.c (e b) ∧ a'.u b = a.u (e b) ∧ a'.Q b = a.Q (e b) ∧
      a'.R b = a.R (e b) ∧ a'.A b = a.A (e b) ∧ a'.F b ⊆ a.F (e b)

/-- **Normalization through given parents.**  For a valid problem, a depth
`0 ≤ r < L`, a fixed format, a subsequence of samples and explicitly given known
parents along it with vanishing slack exponents, there is a calibrated homogeneous
remainder (o183's `Remainder`) along a further subsequence whose parent atlases are
sub-atlases of the given ones. -/
def ParentRemainderConstruction : Prop :=
  ∀ (p : Data), p.Valid → ∀ r h w : ℝ, 0 ≤ r → r < p.L →
    ∀ (M D : ℕ) (φ : ℕ → ℕ) (ε : ℕ → ℝ) (par : (n : ℕ) → Atlas p (φ n))
      (lst : (n : ℕ) → Fin (p.W (φ n)) → Observation → Finset (Fin (par n).C)),
      StrictMono φ → (∀ n, 0 < ε n) → Tendsto ε atTop (nhds 0) →
      (∀ n, KnownParentAt p M D r h w (ε n) (par n) (lst n)) →
      ∃ (q : Data) (rem : Remainder p q r h w) (ψ : ℕ → ℕ), StrictMono ψ ∧
        ∀ k, ∃ e : Fin (rem.parent k).C → Fin (par (ψ k)).C,
          SubAtlas (rem.parent k) (par (ψ k)) e

namespace Remainder'

variable {p q : Data} {r h w : ℝ} (rem : Remainder p q r h w)

/-- The lifted labels lie in the world of their parent label. -/
theorem liftAtlas_world {k : ℕ} (a : Atlas q k) (b : Fin a.C) :
    (rem.liftAtlas k a).γ b = (rem.parent k).γ (rem.parentIndex k (a.γ b)) := rfl

/-- The lifted assignments are contained in the parent assignments. -/
theorem liftAtlas_A_subset_parent {k : ℕ} (a : Atlas q k) (b : Fin a.C) :
    (rem.liftAtlas k a).A b ⊆ (rem.parent k).A (rem.parentIndex k (a.γ b)) :=
  Set.inter_subset_left

/-- The lifted time partition refines the parent partition. -/
theorem liftAtlas_T {k : ℕ} (a : Atlas q k) :
    (rem.liftAtlas k a).T = (rem.parent k).T + a.T := rfl

/-- The lifted time block lies in the parent block. -/
theorem liftAtlas_block_nested {k : ℕ} (a : Atlas q k) (b : Fin a.C) :
    (((rem.parent k).j (rem.parentIndex k (a.γ b)) : ℕ) : ℝ) / (2 : ℝ) ^ (rem.parent k).T ≤
        (((rem.liftAtlas k a).j b : ℕ) : ℝ) / (2 : ℝ) ^ (rem.liftAtlas k a).T ∧
      ((((rem.liftAtlas k a).j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (rem.liftAtlas k a).T ≤
        ((((rem.parent k).j (rem.parentIndex k (a.γ b)) : ℕ) : ℝ) + 1) /
          (2 : ℝ) ^ (rem.parent k).T := by
  have hlo := compositeBlock_lower ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b)
  have hhi := compositeBlock_upper ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b)
  have hj : ((a.j b : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ a.T := by
    have := (a.j b).isLt
    exact_mod_cast this
  have hT : (0 : ℝ) < (2 : ℝ) ^ (rem.parent k).T := by positivity
  have hU : (0 : ℝ) < (2 : ℝ) ^ a.T := by positivity
  change _ ≤ ((compositeBlock ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b) : ℕ) : ℝ) /
      (2 : ℝ) ^ ((rem.parent k).T + a.T) ∧
    (((compositeBlock ((rem.parent k).j (rem.parentIndex k (a.γ b))) (a.j b) : ℕ) : ℝ) + 1) /
      (2 : ℝ) ^ ((rem.parent k).T + a.T) ≤ _
  rw [hlo, hhi]
  constructor
  · have : (0 : ℝ) ≤ ((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T / (2 : ℝ) ^ (rem.parent k).T := by
      positivity
    linarith
  · have h1 : (((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T ≤ 1 := (div_le_one hU).mpr hj
    have h2 : (((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T / (2 : ℝ) ^ (rem.parent k).T ≤
        1 / (2 : ℝ) ^ (rem.parent k).T := div_le_div_of_nonneg_right h1 hT.le
    rw [add_div (((rem.parent k).j (rem.parentIndex k (a.γ b)) : ℕ) : ℝ) 1]
    linarith

/-- Jacobians and time lengths multiply under lifting, so logarithmic widths add. -/
theorem liftAtlas_width {k : ℕ} (a : Atlas q k) (b : Fin a.C) :
    |Matrix.det ((rem.liftAtlas k a).Q b)| * (4 : ℝ) ^ (rem.liftAtlas k a).T =
      (|Matrix.det ((rem.parent k).Q (rem.parentIndex k (a.γ b)))| *
          (4 : ℝ) ^ (rem.parent k).T) *
        (|Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T) := by
  change |Matrix.det ((rem.parent k).Q (rem.parentIndex k (a.γ b)) * a.Q b)| *
      (4 : ℝ) ^ ((rem.parent k).T + a.T) = _
  rw [Matrix.det_mul, abs_mul, pow_add]
  ring

end Remainder'

end Submission.Obl.k4_raw_critical_segment_forests
