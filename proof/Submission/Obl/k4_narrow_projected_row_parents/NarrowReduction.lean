import Submission.Obl.k4_narrow_projected_row_parents.ExponentFront
import Submission.Obl.k4_narrow_projected_row_parents.NarrowVel

/-!
# The front reduced to the comparison

`NarrowComparison` is the paper's Lemma 8.3 for a narrow projected layer on an already
normalized exponent sequence: the comparison of the true labels at the layer's depth with
the layer itself, along the sequence (`CompareSeq`).

`exponentVelocityComparison_of_narrowComparison`: it gives x0975's
`ExponentVelocityComparison 2`, hence (by `narrowFront_of_exponent_velocity` and
`raw_of_front`) the frozen statement.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter

/-- The comparison of the true labels with a narrow projected layer, along the sequence. -/
def NarrowComparison : Prop :=
  Match → ∀ (α : Type) [MeasurableSpace α] (cfg : Model α), Model.Valid cfg →
    ∀ L a s : ℝ, 2 < L → 0 < a → a ≤ s → s ≤ 2 * a → s ≤ cfg.U →
    ∀ (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
      (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
      (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
      (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
      (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
      Model.NarrowWitness cfg L a ((L + 1) * a) s id H ρ' β n' C tag u v G →
      ∀ B : ℝ, cfg.ℓ * s < B → B ≤ cfg.ℓ * s + L * a →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
        cfg.N k ^ (-B - δ) ≤ β k s ∧ β k s ≤ cfg.N k ^ (-B + δ)) →
      CompareSeq cfg s ((L + 1) * a) (fun k => β k s) (fun k => n' k s) (fun k => C k s)

/-- The comparison gives the normalized velocity lists. -/
theorem exponentVelocityComparison_of_narrowComparison (h : NarrowComparison) :
    ExponentVelocityComparison 2 := by
  intro hMatch α _ cfg hv L a s hL ha has hs2 H ρ' β n' C tag u v G hw B hB hBA hfit
    r e mesh hsr hrU hrB hBr he heB hem hmesh
  right
  have hcmp := h hMatch α cfg hv L a s hL ha has hs2 (hsr.le.trans hrU.le)
    H ρ' β n' C tag u v G hw B hB hBA hfit
  have hs : 0 < s := ha.trans_le has
  have hm : 0 < (L + 1) * a := by positivity
  have hvel : ∀ k (i : Fin (n' k s)), ∀ l ∈ C k s i,
      |cfg.b k l 4 - v k s i| ≤ 2 * (H k * β k s) := by
    intro k i l hl
    have hsl := (hw.slice k).2.2.2.2.2.1 i
    exact slice_velocity (b := cfg.b k l) (u := u k s i) (w := H k * β k s)
      (fun t ht => ((hsl.2.2.2.1 l hl).2.2 t ht).1)
  exact velocityLists_of_compareSeq cfg hv hs hm hsr hrU.le hBr he (by linarith)
    (by linarith) (fun k => (hw.loss k).1) hw.loss_subpower hvel hfit hcmp

end Submission.Obl.k4_narrow_projected_row_parents

namespace Submission.Obl.k4_narrow_projected_row_parents

/-- The frozen statement from the comparison of true labels with narrow projected layers. -/
theorem raw_of_narrowComparison (h : NarrowComparison) : RawNarrowFront :=
  raw_of_front (narrowFront_of_exponent_velocity (le_refl 2)
    (exponentVelocityComparison_of_narrowComparison h))

end Submission.Obl.k4_narrow_projected_row_parents
