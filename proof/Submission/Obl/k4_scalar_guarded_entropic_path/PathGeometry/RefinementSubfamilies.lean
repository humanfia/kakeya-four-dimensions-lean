/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/RefinementSubfamilies.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementWitness

/-! Tracking a supplied scalar atlas through subsequences, injected
subfamilies and later incidence restrictions. The full assignments and
all scalar coordinate data are recorded literally. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def RefinementData.subfamily {p q : Code} (w : RefinementData p q) (z : Code)
    (ψ : ℕ → ℕ) (e : (k : ℕ) → Fin (W z k) ↪ Fin (W q (ψ k)))
    (loss : ℕ → ℝ) (exponent : ℕ)
    (selected : (k : ℕ) → Fin (W z k) → Set ((ℕ × ScalarCoeff) × ℝ))
    (lists : (k : ℕ) → Fin (W p (w.sample (ψ k))) →
      ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W z k))) : RefinementData p z where
  sample := w.sample ∘ ψ
  loss := loss
  exponent := exponent
  T := w.T ∘ ψ
  world k i := w.world (ψ k) (e k i)
  block k i := w.block (ψ k) (e k i)
  assignment k i := w.assignment (ψ k) (e k i)
  selected := selected
  center k i := w.center (ψ k) (e k i)
  speed k i := w.speed (ψ k) (e k i)
  width k i := w.width (ψ k) (e k i)
  polynomial k i := w.polynomial (ψ k) (e k i)
  lists := lists
  trajectory k i := w.trajectory (ψ k) (e k i)

/-- The source true-atlas floor implies a lower bound for the entire
assigned trajectory prior. This is the part preserved by incidence masks. -/
def RefinementData.Saturated {p q : Code} (w : RefinementData p q) (r : ℝ)
    (σ : ℕ → ℝ) : Prop :=
  ∀ k i, ENNReal.ofReal (N p (w.sample k) ^ (-f p r - σ k) * w.width k i) ≤
    ν p (w.sample k) (w.world k i) (w.assignment k i)

structure RetainedRefinement {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) where
  code : Code
  sample : ℕ → ℕ
  sample_strictMono : StrictMono sample
  embedding : (k : ℕ) → Fin (W code k) ↪ Fin (W q (sample k))
  lists : (k : ℕ) → Fin (W p (w.sample (sample k))) →
    ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W code k))
  witness : RefinementWitness p code r b h
  data_eq : witness.toRefinementData =
    w.toRefinementData.subfamily code sample embedding witness.loss witness.exponent
      witness.selected lists
  selected_subset : ∀ k i, witness.selected k i ⊆ w.selected (sample k) (embedding k i)

namespace RetainedRefinement

theorem saturation {p q : Code} {r b h : ℝ} {w : RefinementWitness p q r b h}
    (a : RetainedRefinement w) (σ : ℕ → ℝ)
    (hsat : w.toRefinementData.Saturated r σ) :
    a.witness.toRefinementData.Saturated r (σ ∘ a.sample) := by
  unfold RefinementData.Saturated
  rw [a.data_eq]
  exact fun k i => hsat (a.sample k) (a.embedding k i)

theorem sample_eq {p q : Code} {r b h : ℝ} {w : RefinementWitness p q r b h}
    (a : RetainedRefinement w) : a.witness.sample = w.sample ∘ a.sample := by
  exact congrArg RefinementData.sample a.data_eq

theorem assignment_eq {p q : Code} {r b h : ℝ} {w : RefinementWitness p q r b h}
    (a : RetainedRefinement w) (k : ℕ) (i : Fin (W a.code k)) :
    a.witness.assignment k i = w.assignment (a.sample k) (a.embedding k i) := by
  exact congrArg (fun d : RefinementData p a.code => d.assignment k i) a.data_eq

end RetainedRefinement

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
