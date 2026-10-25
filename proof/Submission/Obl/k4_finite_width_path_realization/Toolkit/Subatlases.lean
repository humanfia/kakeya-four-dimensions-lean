/- Adapted from same-tree o119, session x0401, commit 19d6f4b3eda81f6d7228948a9996d889733ab672,
   Submission/Obl/k4_finite_width_critical_contradiction/Subatlases.lean (namespace renamed; any
   earlier provenance is kept below). -/
import Submission.Obl.k4_finite_width_path_realization.Toolkit.Monotonicity

/-! Selecting chart subfamilies retains their original assignments and floors. -/

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory

/-- Relabel charts without changing any geometric or measure data. -/
def Atlas.reindex {p : Data} {k : ℕ} (a : Atlas p k) {C : ℕ}
    (e : Fin C → Fin a.C) : Atlas p k where
  κ := a.κ
  T := a.T
  C := C
  γ := a.γ ∘ e
  j := a.j ∘ e
  c := a.c ∘ e
  u := a.u ∘ e
  Q := a.Q ∘ e
  R := a.R ∘ e
  A := a.A ∘ e
  F := a.F ∘ e

/-- The finite subset is reindexed by its own cardinality. -/
noncomputable def Atlas.restrictTo {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) : Atlas p k :=
  a.reindex (s.orderEmbOfFin rfl)

theorem Atlas.mass_restrictTo {p : Data} {k : ℕ} (a : Atlas p k)
    (s : Finset (Fin a.C)) :
    (a.restrictTo s).mass =
      ∑ b ∈ s, ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b) := by
  classical
  unfold Atlas.mass Atlas.restrictTo Atlas.reindex
  simp only [Function.comp_apply]
  calc
    _ = ∑ b ∈ Finset.univ.image (s.orderEmbOfFin rfl),
        ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => (s.orderEmbOfFin rfl).injective h
    _ = _ := by rw [s.image_orderEmbOfFin_univ rfl]

theorem Atlas.Separated.reindex {p : Data} {k C : ℕ} {a : Atlas p k}
    (ha : a.Separated) {e : Fin C → Fin a.C} (he : Function.Injective e) :
    (a.reindex e).Separated := by
  intro b b' hbb hγ hj
  exact ha (e b) (e b') (fun h => hbb (he h)) hγ hj

/-- Subselection only needs a new total-mass bound. The original-prior floor
on every retained chart is preserved when its slack is enlarged. -/
theorem Atlas.TrueAt.restrictTo {p : Data} (hp : p.Valid) {k M D : ℕ}
    {a : Atlas p k} {r κ' : ℝ} (ha : a.TrueAt M D r)
    (hκ : 1 ≤ a.κ) (hκ' : a.κ ≤ κ') (s : Finset (Fin a.C))
    (hmass : ENNReal.ofReal κ'⁻¹ ≤
      ∑ b ∈ s, ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b)) :
    ((a.restrictTo s).enlarge κ').TrueAt M D r := by
  have hlarge := ha.enlarge hp hκ hκ'
  change ((a.enlarge κ').restrictTo s).TrueAt M D r
  refine ⟨?_, hlarge.2.1.reindex (s.orderEmbOfFin rfl).injective,
    fun b => hlarge.2.2.1 (s.orderEmbOfFin rfl b), ?_⟩
  · apply le_trans _ hlarge.1
    change (s.card : ℝ) ≤ (a.C : ℝ)
    exact_mod_cast (le_trans (Finset.card_le_univ s) (by simp))
  · change ENNReal.ofReal κ'⁻¹ ≤ (a.restrictTo s).mass
    rw [Atlas.mass_restrictTo]
    exact hmass

end Submission.Obl.k4_finite_width_path_realization
