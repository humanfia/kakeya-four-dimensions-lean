import Submission.Obl.k4_scalar_guarded_tangent_preparation.CurrentFloors
import Submission.Obl.k4_scalar_guarded_tangent_preparation.SubLayer

/-!
# Simultaneous duration-core pruning of finitely many layers

At one stage, consider finitely many layers of one exact problem at one sample, and a
current incidence law `ρ g` in each world. Every piece (packet) of every layer gets the
fixed cost `ν(A) / (K₁ 2^T)` of its full assigned prior. One measurable mask per world
(`exists_current_floor_mask`) leaves every packet either with zero current mass or with at
least its cost. The weighted total cost is at most `count / K₁` by the assignment budget:
within a world and a block the assignments are disjoint, so the priors of the pieces of one
layer sum to at most `2^T`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Within one world, the full priors of the pieces of one layer sum to at most `2^T`. -/
theorem layer_world_prior_sum_le {W : ℕ} (ν : Measure Coeff) [IsProbabilityMeasure ν]
    (f : Layer W) (hmeas : ∀ i, MeasurableSet (f.assignment i))
    (hdisj : ∀ i i', i ≠ i' → f.world i = f.world i' → f.block i = f.block i' →
      Disjoint (f.assignment i) (f.assignment i'))
    (g : Fin W) :
    ∑ i ∈ Finset.univ.filter (fun i => f.world i = g), ν (f.assignment i) ≤
      (2 ^ f.T : ℝ≥0∞) := by
  classical
  set s := Finset.univ.filter (fun i => f.world i = g) with hs
  rw [← Finset.sum_fiberwise s f.block]
  calc ∑ j : Fin (2 ^ f.T), ∑ i ∈ s with f.block i = j, ν (f.assignment i)
      ≤ ∑ _j : Fin (2 ^ f.T), (1 : ℝ≥0∞) := by
        gcongr with j
        rw [← measure_biUnion_finset]
        · exact prob_le_one
        · intro i hi i' hi' hii'
          simp only [Finset.coe_filter, hs, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hi hi'
          exact hdisj i i' hii' (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm)
        · intro i _; exact hmeas i
    _ = (2 ^ f.T : ℝ≥0∞) := by simp

/-- The pieces of finitely many layers, as one finite index type. -/
abbrev Packet {W count : ℕ} (layers : Fin count → Layer W) : Type :=
  Σ ℓ : Fin count, Fin (layers ℓ).n

namespace Packet

variable {W count : ℕ} {layers : Fin count → Layer W}

/-- The world of a packet. -/
abbrev world (x : Packet layers) : Fin W := (layers x.1).world x.2

/-- The time-block rectangle of a packet. -/
abbrev rect (x : Packet layers) : Set Incidence :=
  (layers x.1).assignment x.2 ×ˢ Split.I (layers x.1).T ((layers x.1).block x.2)

end Packet

/-- The pruning data at one stage. -/
structure PruneInput where
  W : ℕ
  count : ℕ
  layers : Fin count → Layer W
  ν : Fin W → Measure Coeff
  ρ : Fin W → Measure Incidence
  K₁ : ℝ

namespace PruneInput

variable (I : PruneInput)

/-- The fixed cost of a packet: its full assigned prior over `K₁ 2^T`. -/
def cost (x : Packet I.layers) : ℝ≥0∞ :=
  I.ν x.world ((I.layers x.1).assignment x.2) *
    ENNReal.ofReal ((I.K₁ * 2 ^ (I.layers x.1).T)⁻¹)

/-- The packets of one world. -/
def packetsOf (g : Fin I.W) : Finset (Packet I.layers) :=
  Finset.univ.filter (fun x => x.world = g)

theorem rect_measurable (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    (x : Packet I.layers) : MeasurableSet x.rect :=
  (hmeas x.1 x.2).prod measurableSet_Icc

variable {I}

/-- The mask chosen in one world. -/
def mask (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i)) (g : Fin I.W) :
    Set Incidence :=
  Classical.choose (exists_current_floor_mask (fun x : Packet I.layers => x.rect)
    (I.rect_measurable hmeas) I.cost (I.packetsOf g) (I.ρ g))

theorem mask_spec (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i)) (g : Fin I.W) :
    MeasurableSet (mask hmeas g) ∧
      I.ρ g Set.univ ≤ ((I.ρ g).restrict (mask hmeas g)) Set.univ +
        ∑ x ∈ I.packetsOf g, I.cost x ∧
      ∀ x ∈ I.packetsOf g, ((I.ρ g).restrict (mask hmeas g)) x.rect = 0 ∨
        I.cost x ≤ ((I.ρ g).restrict (mask hmeas g)) x.rect :=
  Classical.choose_spec (exists_current_floor_mask (fun x : Packet I.layers => x.rect)
    (I.rect_measurable hmeas) I.cost (I.packetsOf g) (I.ρ g))

/-- The pruned incidence law. -/
def pruned (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i)) (g : Fin I.W) :
    Measure Incidence :=
  (I.ρ g).restrict (mask hmeas g)

theorem pruned_le (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i)) (g : Fin I.W) :
    pruned hmeas g ≤ I.ρ g :=
  Measure.restrict_le_self

/-- A packet is kept when its current rectangle mass is positive. -/
def keep (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i)) (ℓ : Fin I.count)
    (i : Fin (I.layers ℓ).n) : Prop :=
  pruned hmeas ((I.layers ℓ).world i)
    ((I.layers ℓ).assignment i ×ˢ Split.I (I.layers ℓ).T ((I.layers ℓ).block i)) ≠ 0

theorem cost_le_of_keep (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    {ℓ : Fin I.count} {i : Fin (I.layers ℓ).n} (hk : keep hmeas ℓ i) :
    I.cost ⟨ℓ, i⟩ ≤ pruned hmeas ((I.layers ℓ).world i)
      ((I.layers ℓ).assignment i ×ˢ Split.I (I.layers ℓ).T ((I.layers ℓ).block i)) := by
  have hx : (⟨ℓ, i⟩ : Packet I.layers) ∈ I.packetsOf ((I.layers ℓ).world i) := by
    simp [packetsOf]
  rcases (mask_spec hmeas ((I.layers ℓ).world i)).2.2 ⟨ℓ, i⟩ hx with h | h
  · exact absurd h hk
  · exact h

theorem pruned_rect_eq_zero (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    {ℓ : Fin I.count} {i : Fin (I.layers ℓ).n} (hk : ¬keep hmeas ℓ i) :
    pruned hmeas ((I.layers ℓ).world i)
      ((I.layers ℓ).assignment i ×ˢ Split.I (I.layers ℓ).T ((I.layers ℓ).block i)) = 0 := by
  unfold keep at hk
  push Not at hk
  exact hk

/-- The weighted total cost is at most `count / K₁`. -/
theorem weighted_cost_le (ω : Fin I.W → ℝ) (hω : ∀ g, 0 ≤ ω g) (hω1 : ∑ g, ω g = 1)
    (hν : ∀ g, IsProbabilityMeasure (I.ν g)) (hK₁ : 0 < I.K₁)
    (hmeas : ∀ ℓ i, MeasurableSet ((I.layers ℓ).assignment i))
    (hdisj : ∀ ℓ i i', i ≠ i' → (I.layers ℓ).world i = (I.layers ℓ).world i' →
      (I.layers ℓ).block i = (I.layers ℓ).block i' →
      Disjoint ((I.layers ℓ).assignment i) ((I.layers ℓ).assignment i')) :
    ∑ g, ENNReal.ofReal (ω g) * ∑ x ∈ I.packetsOf g, I.cost x ≤
      ENNReal.ofReal (I.count / I.K₁) := by
  classical
  -- regroup the packets of a world by layer
  have hregroup : ∀ g, ∑ x ∈ I.packetsOf g, I.cost x =
      ∑ ℓ : Fin I.count, ∑ i ∈ Finset.univ.filter (fun i => (I.layers ℓ).world i = g),
        I.cost ⟨ℓ, i⟩ := by
    intro g
    rw [packetsOf, Finset.sum_filter, Fintype.sum_sigma]
    congr 1; ext ℓ
    rw [Finset.sum_filter]
  have hlayer : ∀ g (ℓ : Fin I.count),
      ∑ i ∈ Finset.univ.filter (fun i => (I.layers ℓ).world i = g), I.cost ⟨ℓ, i⟩ ≤
        ENNReal.ofReal (I.K₁⁻¹) := by
    intro g ℓ
    have hsum := layer_world_prior_sum_le (I.ν g) (I.layers ℓ) (hmeas ℓ) (hdisj ℓ) g
    have h2T : (0 : ℝ) < 2 ^ (I.layers ℓ).T := by positivity
    calc ∑ i ∈ Finset.univ.filter (fun i => (I.layers ℓ).world i = g), I.cost ⟨ℓ, i⟩
        = (∑ i ∈ Finset.univ.filter (fun i => (I.layers ℓ).world i = g),
            I.ν g ((I.layers ℓ).assignment i)) *
            ENNReal.ofReal ((I.K₁ * 2 ^ (I.layers ℓ).T)⁻¹) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [cost, Packet.world, hi]
      _ ≤ (2 ^ (I.layers ℓ).T : ℝ≥0∞) * ENNReal.ofReal ((I.K₁ * 2 ^ (I.layers ℓ).T)⁻¹) := by
          gcongr
      _ = ENNReal.ofReal (I.K₁⁻¹) := by
          rw [show (2 ^ (I.layers ℓ).T : ℝ≥0∞) = ENNReal.ofReal (2 ^ (I.layers ℓ).T) by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp]
          rw [← ENNReal.ofReal_mul h2T.le]
          congr 1
          field_simp
  calc ∑ g, ENNReal.ofReal (ω g) * ∑ x ∈ I.packetsOf g, I.cost x
      ≤ ∑ g, ENNReal.ofReal (ω g) * (I.count * ENNReal.ofReal (I.K₁⁻¹)) := by
        gcongr with g
        rw [hregroup g]
        calc ∑ ℓ : Fin I.count, ∑ i ∈ Finset.univ.filter (fun i => (I.layers ℓ).world i = g),
              I.cost ⟨ℓ, i⟩
            ≤ ∑ _ℓ : Fin I.count, ENNReal.ofReal (I.K₁⁻¹) := by
              gcongr with ℓ; exact hlayer g ℓ
          _ = I.count * ENNReal.ofReal (I.K₁⁻¹) := by simp
    _ = (∑ g, ENNReal.ofReal (ω g)) * (I.count * ENNReal.ofReal (I.K₁⁻¹)) := by
        rw [Finset.sum_mul]
    _ = ENNReal.ofReal (I.count / I.K₁) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hω g), hω1, ENNReal.ofReal_one, one_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv]

end PruneInput

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
