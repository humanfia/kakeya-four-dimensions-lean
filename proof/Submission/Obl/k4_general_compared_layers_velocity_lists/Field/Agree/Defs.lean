-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Defs; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Interfaces

/-!
# Objects of the coefficient-agreement step (paper Prop. 8.4)

For one compared sample `s` at index `k`:

* `agPairAt`, `agCoeffAt`: the transverse coefficients `(A, B, D)` of a projected quadratic
  `G(t, Y)` at a base point `(t, Z)` of an original block, in the normalized transverse
  coordinate `U`;
* `agRepTime`, `agRepZ`: the representative base point of a native state;
* `agEvQ Q`: the color-0 events of parent `Q`, `agBlk`: the block label of an incidence;
* `box M`, `agStF`: the finite combined state (block, native state) used for consensus;
* `agEntF`: the coarse label of an incidence;
* `agreeRel`: agreement of two coarse labels' transverse pairs at a state;
* sources (`agSrc`, `agSrcTime`, `agSrcZ`, `agSrcPoly`), targets (`agTgtPoly`, `agTgtOffsets`,
  `agTagCenter`, `agTgtList`), the three-bin palette `agPal3`, and the agGood set `agGood`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The transverse coefficient pair `(B, D)` of `G` at the base point `(t, Z)` of block `Q`. -/
def agPairAt (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ) (t Z : ℝ) :
    Fin 2 → ℝ :=
  ![transB G (p.tiltY k r Q) (p.blockWidth k r) t Z, transD G (p.blockWidth k r)]

theorem agree_transPair_eq_pairAt (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ)
    (ω : α × ℝ) : p.transPair k r Q G ω = p.agPairAt k r Q G ω.2 (p.x k ω.1 ω.2 1) := rfl

/-- The three transverse coefficients `(A, B, D)` of `G` at the base point `(t, Z)`. -/
def agCoeffAt (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ) (t Z : ℝ) :
    Fin 3 → ℝ :=
  ![transA G (p.tiltY k r Q) t Z, transB G (p.tiltY k r Q) (p.blockWidth k r) t Z,
    transD G (p.blockWidth k r)]

/-- Representative time of a native state: the lower corner of its time cell. -/
def agRepTime (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb : ℝ) (σ : Fin 4 → ℤ) : ℝ :=
  p.blockStart k r Q + p.blockLen k r * ((σ 0 : ℝ) * δb)

/-- Representative major coordinate of a native state: the lower corner of its cell. -/
def agRepZ (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (δb : ℝ) (σ : Fin 4 → ℤ) : ℝ :=
  p.c k r Q 0 + p.c k r Q 1 * p.agRepTime k r Q δb σ + p.blockLen k r * ((σ 1 : ℝ) * δb)

/-- The box of native states with all coordinates in `[-M, M]`. -/
def agStateBox (M : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M

/-- The three-bin palette weight around the velocity bin `a` at mesh `χ`. -/
def agPal3 (k : ℕ) (χ : ℝ) (a : ℤ) : ℝ≥0∞ :=
  p.π k (Ico (((a : ℝ) - 1) * χ) (((a : ℝ) + 2) * χ))

namespace ComparedSample

variable {p}
variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

/-- The color-0 events of parent `Q`. -/
def agEvQ (Q : Fin (p.n k r)) : Set (α × ℝ) :=
  ⋃ (e : Fin (s.count 0)) (_ : s.parent 0 e = Q), s.event 0 e

/-- The block label of an incidence: the parent of its color-0 event. -/
def agBlk (ω : α × ℝ) : Option (Fin (p.n k r)) := by
  classical
  exact if h : ∃ Q, ω ∈ s.agEvQ Q then some (Classical.choose h) else none

/-- The finite combined state used for consensus: block label and native state (inside the
box `agStateBox M`). -/
def agStF (δb δs : ℝ) (M : ℕ) (ω : α × ℝ) :
    Option (Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}) := by
  classical
  exact (s.agBlk ω).bind fun Q =>
    if h : p.nativeState k r Q δb δs ω ∈ agStateBox M then some (Q, ⟨_, h⟩) else none

/-- The coarse label of an incidence. -/
def agEntF (ω : α × ℝ) : Option (Fin (s.layers 0).count) := by
  classical
  exact if h : ∃ i, ω.1 ∈ (s.layers 0).C i then some (Classical.choose h) else none

/-- Agreement of the transverse pairs of two coarse labels at the representative point of a
combined state, to `E / 2`. A missing target label disagrees; anything else agrees. -/
def agreeRel (δb E : ℝ) (M : ℕ) :
    Option (Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}) →
      Option (Fin (s.layers 0).count) → Option (Fin (s.layers 0).count) → Prop
  | some (Q, σ), some i, some i' => ∀ c : Fin 2,
      |p.agPairAt k r Q ((s.layers 0).G i) (p.agRepTime k r Q δb σ.1) (p.agRepZ k r Q δb σ.1) c -
        p.agPairAt k r Q ((s.layers 0).G i') (p.agRepTime k r Q δb σ.1) (p.agRepZ k r Q δb σ.1) c| ≤
        E / 2
  | some _, some _, none => False
  | _, _, _ => True

/-- A source: a color-0 event and a time cell of its parent block. -/
def agSrc (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) : Set (α × ℝ) :=
  s.event 0 e ∩ {ω | ⌊p.tauN k r (s.parent 0 e) ω / δb⌋ = c}

/-- The freezing time of a source: the lower corner of its time cell. -/
def agSrcTime (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) : ℝ :=
  p.blockStart k r (s.parent 0 e) + p.blockLen k r * ((c : ℝ) * δb)

/-- The freezing major coordinate of a source: its coarse tag line at the freezing time. -/
def agSrcZ (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) : ℝ :=
  ((s.layers 0).tag (s.coarse 0 e) 1 : ℝ) * p.N k ^ (-m) +
    s.agSrcTime δb e c * (((s.layers 0).tag (s.coarse 0 e) 0 : ℝ) * p.N k ^ (-m))

/-- The frozen transverse quadratic of a source (its coarse predictor). -/
def agSrcPoly (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) : Fin 3 → ℝ :=
  p.agCoeffAt k r (s.parent 0 e) ((s.layers 0).G (s.coarse 0 e)) (s.agSrcTime δb e c) (s.agSrcZ δb e c)

/-- The frozen transverse quadratic of a target coarse label, at the source's freezing point. -/
def agTgtPoly (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) (i' : Fin (s.layers 0).count) : Fin 3 → ℝ :=
  p.agCoeffAt k r (s.parent 0 e) ((s.layers 0).G i') (s.agSrcTime δb e c) (s.agSrcZ δb e c)

/-- The offset differences available to a target coarse label against a source. -/
def agTgtOffsets (e : Fin (s.count 0)) (i' : Fin (s.layers 0).count) : Finset ℝ :=
  (s.fineChoices 0 (s.parent 0 e) i').image fun j' =>
    s.offset 0 (s.parent 0 e) i' j' -
      s.offset 0 (s.parent 0 e) (s.coarse 0 e) (s.fine 0 e)

/-- The intercept bin predicted by the source's freezing point for a target velocity bin `a`. -/
def agTagCenter (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) (a : ℤ) : ℤ :=
  ⌊(s.agSrcZ δb e c - s.agSrcTime δb e c * ((a : ℝ) * p.N k ^ (-m))) / p.N k ^ (-m)⌋

/-- The target coarse labels compatible with a source. -/
def agTgtList (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) : Finset (Fin (s.layers 0).count) := by
  classical
  exact Finset.univ.filter fun i' =>
    i' ∈ s.coarseChoices (s.parent 0 e) ((s.layers 0).tag i') ∧
      |(s.layers 0).tag i' 1 - s.agTagCenter δb e c ((s.layers 0).tag i' 0)| ≤ 7

/-- The agGood incidences: in some color-0 event, with native signal at most `K`. -/
def agGood : Set (α × ℝ) :=
  (⋃ e, s.event 0 e) ∩ {ω | |p.signal k ω.1 ω.2| ≤ p.K k}

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
