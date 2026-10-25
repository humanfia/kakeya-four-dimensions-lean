import Mathlib

namespace Submission.Obl.k4_weighted_convex_tubes

open MeasureTheory Set

abbrev Space := EuclideanSpace ℝ (Fin 3)

def tube (r : ℝ) (x v : Space) : Set Space :=
  Metric.thickening r (segment ℝ x (x + v))

def WeightedClustering {n : ℕ} (r : ℝ) (x v : Fin n → Space)
    (w : Fin n → ℝ) (A : ℝ) : Prop :=
  ∀ W : Set Space, Convex ℝ W → ∀ F : Finset (Fin n),
    (∀ i ∈ F, tube r (x i) (v i) ⊆ W) →
    ENNReal.ofReal ((∑ i ∈ F, w i) * r ^ 2) ≤ ENNReal.ofReal A * volume W

def ConvexCount {n : ℕ} (r M : ℝ) (x v : Fin n → Space)
    (S : Finset (Fin n)) : Prop :=
  ∀ W : Set Space, Convex ℝ W → ∀ F : Finset (Fin n), F ⊆ S →
    (∀ i ∈ F, tube r (x i) (v i) ⊆ W) →
    ENNReal.ofReal ((F.card : ℝ) * r ^ 2) ≤ ENNReal.ofReal M * volume W

/-- The geometric sampling assertion, independent of the shadings. -/
def SamplingPrinciple : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 / 100 → r ≤ r₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (w : Fin n → ℝ) (A : ℝ),
    (∀ i, ‖v i‖ = 1) →
    (∀ i, tube r (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i, 0 < w i) → 0 < A → WeightedClustering r x v w A →
    (∑ i, w i) ≤ K * A ∨
      ∃ S : Finset (Fin n), (∑ i, w i) ≤ K * A * S.card ∧
        ConvexCount r (r ^ (-τ)) x v S

def EstimateAt (ε η a : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    (∀ i, ‖v i‖ = 1) →
    (∀ i, tube r (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube r (x i) (v i)) →
    (∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Y i)) →
    ConvexCount r (r ^ (-η)) x v Finset.univ →
    ENNReal.ofReal (a * r ^ ε * (n : ℝ) * r ^ 2) ≤ volume (⋃ i, Y i)

theorem estimate_subfamily {ε η a : ℝ} (h : EstimateAt ε η a)
    {r : ℝ} (hr : 0 < r) (hr100 : r ≤ 1 / 100)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, tube r (x i) (v i) ⊆ Metric.ball 0 1)
    (hY : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ tube r (x i) (v i))
    (hdense : ∀ i, ENNReal.ofReal (r ^ η * r ^ 2) ≤ volume (Y i))
    (S : Finset (Fin n)) (hcount : ConvexCount r (r ^ (-η)) x v S) :
    ENNReal.ofReal (a * r ^ ε * (S.card : ℝ) * r ^ 2) ≤ volume (⋃ i, Y i) := by
  classical
  let e : Fin S.card → Fin n := fun i => (S.equivFin.symm i).1
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have heS (i) : e i ∈ S := (S.equivFin.symm i).2
  have hsmall := h r hr hr100 S.card (x ∘ e) (v ∘ e) (Y ∘ e)
    (fun i => hv (e i)) (fun i => hball (e i)) (fun i => hY (e i))
    (fun i => hYT (e i)) (fun i => hdense (e i))
  have hc : ConvexCount r (r ^ (-η)) (x ∘ e) (v ∘ e) Finset.univ := by
    intro W hW F hF hFW
    have himage : F.image e ⊆ S := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact heS j
    have ht : ∀ i ∈ F.image e, tube r (x i) (v i) ⊆ W := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hFW j hj
    have hh := hcount W hW (F.image e) himage ht
    simpa only [Finset.card_image_of_injective _ he] using hh
  exact (hsmall hc).trans (measure_mono (iUnion_subset fun i => subset_iUnion Y (e i)))

theorem union_volume_ne_top {n : ℕ} {r : ℝ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hball : ∀ i, tube r (x i) (v i) ⊆ Metric.ball 0 1)
    (hYT : ∀ i, Y i ⊆ tube r (x i) (v i)) :
    volume (⋃ i, Y i) ≠ ⊤ :=
  (measure_mono (iUnion_subset fun i => (hYT i).trans (hball i))).trans_lt
    (measure_ball_lt_top : volume (Metric.ball (0 : Space) 1) < ⊤) |>.ne

theorem ofReal_le_volume_iff {s : Set Space} (hs : volume s ≠ ⊤) {b : ℝ} :
    ENNReal.ofReal b ≤ volume s ↔ b ≤ (volume s).toReal := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hs]
  exact ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg

end Submission.Obl.k4_weighted_convex_tubes
