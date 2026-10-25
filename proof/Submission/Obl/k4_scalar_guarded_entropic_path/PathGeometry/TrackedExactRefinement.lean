/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrackedExactRefinement.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrackedPureRefinement
import Submission.Obl.k4_scalar_normalized_exact_refinement

/-! Complete a chosen raw refinement to an exact problem while retaining
its original atlas. Only the joint density is installed after the tracked
pure restriction; the accepted profile and angular stages supply it. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

theorem specExact_of_exact {p : Code} (hp : Exact p) : Spec.Exact p :=
  ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩,
    hp.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩

theorem exact_of_specExact {p : Code} (hp : Spec.Exact p) : Exact p :=
  ⟨hp.1.1, hp.1.2, hp.2.1.1, hp.2.2.1, hp.2.1.2.1, hp.2.1.2.2,
    hp.2.2.2.1, hp.2.2.2.2⟩

def RefinementData.withJoint {p q : Code} (w : RefinementData p q)
    (G : (k : ℕ) → Fin (W q k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) :
    RefinementData p (Stages.withJoint q G) where
  sample := w.sample
  loss := w.loss
  exponent := w.exponent
  T := w.T
  world := w.world
  block := w.block
  assignment := w.assignment
  selected := w.selected
  center := w.center
  speed := w.speed
  width := w.width
  polynomial := w.polynomial
  lists := w.lists
  trajectory := w.trajectory

def RefinementWitness.withJoint {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h)
    (G : (k : ℕ) → Fin (W q k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) :
    RefinementWitness p (Stages.withJoint q G) r b h where
  toRefinementData := w.toRefinementData.withJoint G
  sample_strictMono := w.sample_strictMono
  loss_pos := w.loss_pos
  loss_tendsto := w.loss_tendsto
  exponent_one := w.exponent_one
  charts := w.charts
  maps := w.maps
  weights := w.weights

def RetainedRefinement.withJoint {p q : Code} {r b h : ℝ}
    {w : RefinementWitness p q r b h} (a : RetainedRefinement w)
    (G : (k : ℕ) → Fin (W a.code k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) :
    RetainedRefinement w where
  code := Stages.withJoint a.code G
  sample := a.sample
  sample_strictMono := a.sample_strictMono
  embedding := a.embedding
  lists := a.lists
  witness := a.witness.withJoint G
  data_eq := congrArg (fun d : RefinementData p a.code => d.withJoint G) a.data_eq
  selected_subset := a.selected_subset

/-- The exact normalization can be completed through the PROVIDED raw
atlas, with the same full assignments, maps and selected-subset tracking. -/
theorem exists_exact_retained_refinement {p q : Code} {r b h : ℝ}
    (hp : Exact p) (hq : Spec.RawScalar q) (w : RefinementWitness p q r b h)
    (hr : 0 ≤ r) (hrL : r < L p) (hrb : r ≤ b) (hbL : b ≤ L p)
    (hLq : L q = L p - r) (hSq : S q = S p)
    (hUq : U q = U p * (L p - r) / L p)
    (htail : ∀ s, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d q * (L p - s)) :
    ∃ a : RetainedRefinement w, Exact a.code ∧
      L a.code = L q ∧ d a.code = d q ∧ S a.code = S q ∧ U a.code = U q ∧
      (∀ s, 0 ≤ s → s ≤ L a.code →
        f a.code (L a.code) - f a.code s ≤ f p (L p) - f p (r + s)) ∧
      (b = r → ∀ s, 0 ≤ s → s ≤ L a.code →
        f a.code s - f a.code 0 = f p (r + s) - f p r) := by
  obtain ⟨a, hraw, hpure, hL₀, hd₀, hS₀, hU₀⟩ := exists_pure_retained_refinement hp hq w
  have hL : L a.code = L p - r := hL₀.trans hLq
  have hS : S a.code = S p := hS₀.trans hSq
  have hU : U a.code = U p * (L p - r) / L p := hU₀.trans hUq
  have href : Refinement p a.code r b h := refinement_iff_nonempty_witness.mpr ⟨a.witness⟩
  obtain ⟨hrelative, hequal⟩ := Analysis.relativeProfiles_stage p a.code r b h
    (specExact_of_exact hp) hraw hpure hr hrL hrb hbL hL href
  obtain ⟨G, hjoint, hangle⟩ := Analysis.angularTransfer_stage p a.code r b h
    (specExact_of_exact hp) hraw hpure hr hrL hrb hbL hL hS hU href
  have hcap : Stages.TailCap a.code := by
    intro s hs hsL
    change s ≤ L a.code at hsL
    have hrs : r ≤ r + s := by linarith
    have hsrL : r + s ≤ L p := by linarith [hL]
    calc
      _ ≤ f p (L p) - f p (r + s) := hrelative s hs hsL
      _ ≤ d q * (L p - (r + s)) := htail (r + s) hrs hsrL
      _ = d a.code * (L a.code - s) := by rw [hd₀, hL]; ring
  have hfinal : Exact (Stages.withJoint a.code G) :=
    exact_of_specExact ⟨hraw, hpure, hjoint, hcap, hangle⟩
  exact ⟨a.withJoint G, hfinal, hL₀, hd₀, hS₀, hU₀, hrelative, hequal⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
