-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.AtScale; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Core
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.CommonField
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Numerics

/-!
# The common affine field on one consensus law, at one scale

`CommonFieldAt` is the body of the frozen statement of o273 (`CommonFieldPrinciple`) at one
scale `N` and one trajectory type. `Parent.fieldReady_at` applies it, at one fixed `k`, to the
normalized law of a consensus law restricted to the half-states of the two native-signal groups
of its block, under explicit numerical hypotheses, and returns a field-ready law.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers (parentFilling)

noncomputable section

/-- The frozen statement of o273 at one scale `N` and one trajectory type `α`. -/
def CommonFieldAt (S C₀ A θ ε η N : ℝ) (α : Type) [MeasurableSpace α] : Prop :=
  ∀ (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (b v : α → ℝ) (v₀ χb χv : ℝ) (f : α × ℝ → Fin 2 → ℝ) (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ)), (fun (δ e : ℝ) => (fun (z : α × ℝ → Fin 2 → ℝ) => (fun (state : α × ℝ → Fin 4 → ℤ) => Measurable b → Measurable v → Measurable f → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → N ^ (-A) ≤ χb → χb ≤ 1 → N ^ (-A) ≤ χv → χv ≤ 1 → (∀ l, |b l| + |v l| + |v₀| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ᵐ p ∂μ, ∀ i, |f p i| ≤ N ^ η) → (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊z p i / δ⌋) = q} ≤ ENNReal.ofReal (N ^ η * δ ^ 2)) → (∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q : Fin 4 → ℤ) (j : ℤ), μ {p | state p = q ∧ ⌊v p.1 / δ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * μ {p | state p = q} * π (Set.Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ))) → (∀ q, ((L q).card : ℝ) ≤ N ^ η) → (∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ N ^ η) → (∀ᵐ p ∂μ, ∃ a ∈ L (⌊b p.1 / χb⌋, ⌊v p.1 / χv⌋), |f p 0 - a 0 - a 1 * p.2| ≤ N ^ η * e ∧ |f p 1 - a 2| ≤ N ^ η * e) → ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |f p 0 - C 0 - C 1 * z p 0 - C 2 * z p 1| ≤ N ^ ε * e ∧ |f p 1 - C 3| ≤ N ^ ε * e}) (fun p => ![⌊z p 0 / δ⌋, ⌊z p 1 / δ⌋, ⌊f p 0 / e⌋, ⌊f p 1 / e⌋])) (fun p => ![p.2, b p.1 + p.2 * (v p.1 - v₀)])) (N ^ (-(C₀ * (A + θ)))) (N ^ (-θ))

/-- The frozen statement of o273, scale by scale. -/
theorem CommonFieldPrinciple.at (hfield : CommonFieldPrinciple) {S : ℝ} (hS : 0 < S) :
    ∃ C₀ : ℝ, 100 < C₀ ∧ ∀ A θ : ℝ, 0 < A → 0 < θ → ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
        ∀ (α : Type) [MeasurableSpace α], CommonFieldAt S C₀ A θ ε η N α :=
  hfield S hS

namespace FieldCommon

/-- The oscillation bound of the two groups of a block on one transverse slab of a normalized
base cell. -/
theorem osc_bound_numeric {N K q g δ δU s r βb ρU ℓ : ℝ} {C : ℕ} (hN : 0 < N) (hK : 1 ≤ K)
    (hq : 0 < q) (hg : g = N ^ (-ℓ * r)) (hδ : δ = N ^ (-βb)) (hδU : δU = N ^ (-ρU))
    (ha : 3 * 2 ^ 15 * K ^ 14 * N ^ (-r) < N ^ (-s))
    (hb : 144 * 3000000 ^ C * K ^ (20 * C + 4) * N ^ (((C : ℝ) + ℓ) * r - βb) < N ^ (-s))
    (hc : 36 * 3000000 ^ C * K ^ (20 * C + 2) * N ^ ((C : ℝ) * r - ρU) < N ^ (-s)) :
    2 * (2 * K) ^ 14 * N ^ (-r) + parentFilling K (N ^ (-r)) ^ C *
      (12 * K ^ 2 * ((K + 1) ^ 2 * q * δ + q * g * δU) / (q * g)) ≤ N ^ (-s) := by
  have hK0 : 0 < K := by linarith
  have hg0 : 0 < g := by rw [hg]; exact Real.rpow_pos_of_pos hN _
  have hpf := parentFilling_rpow_eq hN C (K := K) (s := r)
  have hδg : δ / g = N ^ (ℓ * r - βb) := by
    rw [hδ, hg, ← Real.rpow_sub hN]
    congr 1
    ring
  have h1 : 12 * K ^ 2 * ((K + 1) ^ 2 * q * δ + q * g * δU) / (q * g) =
      12 * K ^ 2 * (K + 1) ^ 2 * (δ / g) + 12 * K ^ 2 * δU := by
    field_simp
  have hNC : N ^ ((C : ℝ) * r) * N ^ (ℓ * r - βb) = N ^ (((C : ℝ) + ℓ) * r - βb) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hNC2 : N ^ ((C : ℝ) * r) * δU = N ^ ((C : ℝ) * r - ρU) := by
    rw [hδU, ← Real.rpow_add hN, sub_eq_add_neg]
  have hK1 : (K + 1) ^ 2 ≤ 4 * K ^ 2 := by nlinarith
  have hA0 : 0 ≤ (3000000 : ℝ) ^ C * K ^ (20 * C) := by positivity
  have hNCr : 0 < N ^ ((C : ℝ) * r) := Real.rpow_pos_of_pos hN _
  have hNl : 0 < N ^ (ℓ * r - βb) := Real.rpow_pos_of_pos hN _
  have hterm2 : parentFilling K (N ^ (-r)) ^ C *
      (12 * K ^ 2 * ((K + 1) ^ 2 * q * δ + q * g * δU) / (q * g)) ≤
      48 * 3000000 ^ C * K ^ (20 * C + 4) * N ^ (((C : ℝ) + ℓ) * r - βb) +
        12 * 3000000 ^ C * K ^ (20 * C + 2) * N ^ ((C : ℝ) * r - ρU) := by
    rw [hpf, h1, hδg, ← hNC, ← hNC2]
    have e1 : (3000000 : ℝ) ^ C * K ^ (20 * C) * N ^ ((C : ℝ) * r) *
        (12 * K ^ 2 * (K + 1) ^ 2 * N ^ (ℓ * r - βb) + 12 * K ^ 2 * δU) =
        12 * ((3000000 : ℝ) ^ C * K ^ (20 * C) * K ^ 2) * (K + 1) ^ 2 *
          (N ^ ((C : ℝ) * r) * N ^ (ℓ * r - βb)) +
        12 * (3000000 ^ C * K ^ (20 * C) * K ^ 2) * (N ^ ((C : ℝ) * r) * δU) := by ring
    have e2 : 48 * 3000000 ^ C * K ^ (20 * C + 4) * (N ^ ((C : ℝ) * r) * N ^ (ℓ * r - βb)) +
        12 * 3000000 ^ C * K ^ (20 * C + 2) * (N ^ ((C : ℝ) * r) * δU) =
        12 * ((3000000 : ℝ) ^ C * K ^ (20 * C) * K ^ 2) * (4 * K ^ 2) *
          (N ^ ((C : ℝ) * r) * N ^ (ℓ * r - βb)) +
        12 * (3000000 ^ C * K ^ (20 * C) * K ^ 2) * (N ^ ((C : ℝ) * r) * δU) := by ring
    rw [e1, e2]
    gcongr
  have hterm1 : 2 * (2 * K) ^ 14 * N ^ (-r) = 2 ^ 15 * K ^ 14 * N ^ (-r) := by ring
  have hpos1 : 0 ≤ 3000000 ^ C * K ^ (20 * C + 4) * N ^ (((C : ℝ) + ℓ) * r - βb) := by
    positivity
  have hpos2 : 0 ≤ 3000000 ^ C * K ^ (20 * C + 2) * N ^ ((C : ℝ) * r - ρU) := by positivity
  have hpos3 : 0 ≤ K ^ 14 * N ^ (-r) := by positivity
  rw [hterm1]
  nlinarith

end FieldCommon

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The parent geometry of a prepared depth. -/
theorem AtDepth.commonParentGeometry {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) :
    ParentGeometry p k r where
  prior_lower i := by simpa only [zpow_neg, zpow_natCast] using (hat.2.2.2.2.1 i).1
  fitted_subset i := (hat.2.2.1 i).2.2
  coefficient_bound i e := (hat.2.2.2.2.1 i).2.2.2.1 e
  transverse i l hl t ht := by
    simpa only [zpow_neg, zpow_natCast] using ((hat.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht).2.1

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
