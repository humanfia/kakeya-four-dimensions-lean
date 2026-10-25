-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Interfaces; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Setup
import Submission.Obl.k4_general_compared_layers_velocity_lists.ComparedInterface

/-!
# Interfaces of the common-field stage

The second half of the wide-interval argument (paper Prop. 8.4) on one compared
sample, cut into three stages with explicit interfaces:

* `ConsensusLaw` - after native fine-state palette pruning and coefficient
  agreement: a submeasure of the sample law inside one original block on which
  the transverse coefficient pair of the coarse projected predictor is, up to
  `E`, a function `center` of the native fine state, with conditional velocity
  domination by the original palette at native states;
* `FieldReady` - after the common affine field (o273): one affine `C₁(τ, ζ)` and
  one constant `C₂` matching the coarse transverse pairs on a dense submeasure;
* `Parent.ListFrame` (`Lists/Interface.lean`) - the residual velocity lists.

All laws are original (submeasures of the sample law `≤ ρ`); masses are measured
against the full original reference `2^(-T) ν(A_Q)` of the selected block.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The transverse coefficient pair `(B, D)` of a projected quadratic `G(t, Y)`
at an incidence, in the normalized coordinates of the original block `Q`. -/
def transPair (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (G : MvPolynomial (Fin 2) ℝ)
    (ω : α × ℝ) : Fin 2 → ℝ :=
  ![transB G (p.tiltY k r Q) (p.blockWidth k r) ω.2 (p.x k ω.1 ω.2 1),
    transD G (p.blockWidth k r)]

/-- The original reference weight `2^(-T) ν(A_Q)` of a block. -/
def blockWeight (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : ENNReal :=
  ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q)

/-- Output of native-state pruning and coefficient agreement on one block. -/
structure ConsensusLaw (k : ℕ) {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (βb w mv E C : ℝ) where
  block : Fin (p.n k r)
  law : Measure (α × ℝ)
  le_law : law ≤ s.law
  finite : IsFiniteMeasure law
  support : ∀ᵐ ω ∂law, ω.1 ∈ p.B k r block ∧ ω.2 ∈ Parent.block (p.T k r) (p.j k r block) ∧
    ω ∈ p.baseGood k
  mass_lower : ENNReal.ofReal (1 / (4 * H)) * p.blockWeight k r block ≤ law univ
  domination : ∀ (σ : Fin 4 → ℤ) (j : ℤ),
    law {ω | p.nativeState k r block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω = σ ∧
        ⌊p.b k ω.1 3 / p.N k ^ (-mv)⌋ = j} ≤
      ENNReal.ofReal C *
        law {ω | p.nativeState k r block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω = σ} *
        p.π k {x | ⌊x / p.N k ^ (-mv)⌋ = j}
  center : (Fin 4 → ℤ) → Fin 2 → ℝ
  agree : ∀ᵐ ω ∂law, ∃ i, ω.1 ∈ (s.layers 0).C i ∧
    ∀ e : Fin 2, |p.transPair k r block ((s.layers 0).G i) ω e -
      center (p.nativeState k r block (p.N k ^ (-βb)) (p.N k ^ (-w)) ω) e| ≤ E

/-- Output of the common affine field on one block: an affine first transverse
coefficient `C 0 + C 1 τ + C 2 ζ` and a constant second one `C 3`. -/
structure FieldReady (k : ℕ) {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (E ε : ℝ) where
  block : Fin (p.n k r)
  law : Measure (α × ℝ)
  le_law : law ≤ s.law
  finite : IsFiniteMeasure law
  support : ∀ᵐ ω ∂law, ω.1 ∈ p.B k r block ∧ ω.2 ∈ Parent.block (p.T k r) (p.j k r block) ∧
    ω ∈ p.baseGood k
  mass_lower : ENNReal.ofReal (p.N k ^ (-ε)) * p.blockWeight k r block ≤ law univ
  C : Fin 4 → ℝ
  C_bound : ∀ i, |C i| ≤ p.N k ^ ε
  field : ∀ᵐ ω ∂law, ∃ i, ω.1 ∈ (s.layers 0).C i ∧
    |p.transPair k r block ((s.layers 0).G i) ω 0 -
        (C 0 + C 1 * p.tauN k r block ω + C 2 * p.zetaN k r block ω)| ≤ p.N k ^ ε * E ∧
    |p.transPair k r block ((s.layers 0).G i) ω 1 - C 3| ≤ p.N k ^ ε * E

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
