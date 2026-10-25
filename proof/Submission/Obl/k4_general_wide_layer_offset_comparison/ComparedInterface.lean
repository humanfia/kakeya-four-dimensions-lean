import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSlices
import Submission.Obl.k4_general_wide_layer_offset_comparison.BasicFacts
import Submission.Obl.k4_general_wide_layer_offset_comparison.Lists.Interface
import Submission.Obl.k4_general_wide_layer_offset_comparison.Bridge
import Submission.Obl.k4_general_wide_layer_offset_comparison.Reindex

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparedInterface.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The entire true fiber box over a recorded original major bin. -/
def trueFiberBox (k : ℕ) (r m H : ℝ) (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) : Set (Fin 3 → ℝ) :=
  {z | z 0 ∈ block (p.T k r) (p.j k r Q) ∧
    |z 1 - ((tag 1 : ℝ) * p.N k ^ (-m) + z 0 * ((tag 0 : ℝ) * p.N k ^ (-m)))| ≤
      H * p.N k ^ (-m) ∧
    |z 2 - p.c k r Q 2 - z 0 * p.c k r Q 3 - p.c k r Q 4 * z 1| ≤
      H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))}

def ComparedExponents (r u v m : ℝ) : Prop :=
  p.ListExponents r v m ∧ 0 < u ∧ u < r ∧ v < (1 - p.d) * u / 4 ∧
    10000 * (1 + p.ℓ) * r < m ∧ (10 / (1 - p.d) + 4 + p.ℓ) * u < p.κ * r

/-- The output of the raw layer comparison, before coefficient consensus
and transverse-field interpolation. All events and reference weights are in
the original parent measure. Fine colors have gains `u` and `v`. -/
structure ComparedSample (k : ℕ) (r u v m H : ℝ) where
  loss_one : 2 ≤ H
  layers : Fin 3 → ProjectedLayer α
  layer_valid : ∀ a, (layers a).Valid p k (![r, r + u, r + v] a) m H
  coefficient_bound : ∀ a i e, |((layers a).G i).coeff e| ≤ p.N k ^ (m / 1000)
  law : Measure (α × ℝ)
  le_rho : law ≤ p.ρ k
  mass_lower : ENNReal.ofReal H⁻¹ ≤ law univ
  count : Fin 2 → ℕ
  parent : ∀ a, Fin (count a) → Fin (p.n k r)
  coarse : ∀ a, Fin (count a) → Fin (layers 0).count
  fine : ∀ a, Fin (count a) → Fin (layers a.succ).count
  domain : ∀ a, Fin (count a) → ℤ × ℤ × ℤ
  event : ∀ a, Fin (count a) → Set (α × ℝ)
  event_measurable : ∀ a e, MeasurableSet (event a e)
  event_disjoint : ∀ a, Pairwise (fun e f => Disjoint (event a e) (event a f))
  event_cover : ∀ a, ∀ᵐ ω ∂law, ∃ e, ω ∈ event a e
  entry_injective : ∀ a, Function.Injective
    (fun e => (parent a e, coarse a e, fine a e, domain a e))
  event_data : ∀ a e ω, ω ∈ event a e →
    ω ∈ p.baseGood k ∧ ω.1 ∈ p.B k r (parent a e) ∧
      ω.2 ∈ block (p.T k r) (p.j k r (parent a e)) ∧
      ω.1 ∈ (layers 0).C (coarse a e) ∧ ω.1 ∈ (layers a.succ).C (fine a e) ∧
      p.domainCode k ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) ω = domain a e
  palette_positive : ∀ a e,
    0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0}
  event_floor : ∀ a e,
    ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d / H) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0} ≤ law (event a e)
  reference_budget : ∀ a,
    (∑ e, ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0}) ≤ ENNReal.ofReal H
  coarseChoices : Fin (p.n k r) → (Fin 2 → ℤ) → Finset (Fin (layers 0).count)
  coarse_card : ∀ Q tag, ((coarseChoices Q tag).card : ℝ) ≤ H ^ 4
  coarse_mem : ∀ a e,
    coarse a e ∈ coarseChoices (parent a e) ((layers 0).tag (coarse a e))
  fineChoices : ∀ a : Fin 2, Fin (p.n k r) → Fin (layers 0).count →
    Finset (Fin (layers a.succ).count)
  fine_card : ∀ a Q i,
    ((fineChoices a Q i).card : ℝ) ≤ H ^ 4 * p.N k ^ (p.d * ![u, v] a)
  fine_mem : ∀ a e, fine a e ∈ fineChoices a (parent a e) (coarse a e)
  offset : ∀ a : Fin 2, Fin (p.n k r) → Fin (layers 0).count → Fin (layers a.succ).count → ℝ
  offset_bound : ∀ a Q i j, j ∈ fineChoices a Q i → |offset a Q i j| ≤ H * p.N k ^ (-r)
  offset_fit : ∀ a Q i j, j ∈ fineChoices a Q i → ∀ z ∈ p.trueFiberBox k r m H Q ((layers 0).tag i),
    |MvPolynomial.eval ![z 0, z 2] ((layers a.succ).G j) -
      MvPolynomial.eval ![z 0, z 2] ((layers 0).G i) - offset a Q i j| ≤
        H * p.N k ^ (-r - ![u, v] a)
  offset_count : ∀ a Q i x δ, p.N k ^ (-r - ![u, v] a) ≤ δ →
    (((fineChoices a Q i).filter (fun j => |offset a Q i j - x| ≤ δ)).card : ℝ) ≤
      H ^ 10 * (δ / p.N k ^ (-r - ![u, v] a)) ^ p.d
  reverse_count : ∀ a tag D j,
    ((Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e,
      parent a e = Q ∧ (layers 0).tag (coarse a e) = tag ∧ domain a e = D ∧ fine a e = j)).card : ℝ) ≤ H ^ 4

end Parent

/-- Raw geometry and matching prepare the original compared slices at a
chosen small exponent cap. The subsequence is allowed to depend on that cap. -/
def ComparedLayerCore : Prop :=
  Matching → ∀ (α : Type) [MeasurableSpace α] (p : Parent α), p.Valid → p.WideLayers →
    ∀ U' : ℝ, 0 < U' → ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ r u v m : ℝ,
      p.ComparedExponents r u v m ∧ m ≤ U' ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∃ H : ℝ,
        2 ≤ H ∧ p.K (τ k) ≤ H ∧ H ≤ p.N (τ k) ^ ε ∧
          Nonempty ((p.reindex τ).ComparedSample k r u v m H)

/-- Fine-state coefficient agreement, transverse-field interpolation, and
residual support counting. A fixed depth-room multiplier is chosen first;
the uniform per-sample implication can then be pulled to any cofinal sequence. -/
def ComparedListCore : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (p : Parent α), p.Valid →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ r u v m : ℝ, p.ComparedExponents r u v m → Λ * m ≤ p.U →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
        ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
          Nonempty (p.ComparedSample k r u v m H) →
            Nonempty (p.ListFrame k r v m ε)

/-- A reindexed compared sample keeps the exact original source events,
polynomial menus, reference floors and laws. -/
def Parent.ComparedSample.fromReindex {α : Type} [MeasurableSpace α] (p : Parent α)
    {τ : ℕ → ℕ} {k : ℕ} {r u v m H : ℝ}
    (s : (p.reindex τ).ComparedSample k r u v m H) :
    p.ComparedSample (τ k) r u v m H := { s with }

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
