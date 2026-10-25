import Submission.Obl.k4_general_parent_wide_layer_candidates.ComparedInterface
import Submission.Obl.k4_general_parent_wide_layer_candidates.Split.Unpacked

namespace Submission.Obl.k4_general_parent_wide_layer_candidates.Split
open MeasureTheory Set Filter
open Parent (block)
noncomputable section

namespace Unpacked
variable {α : Type} [MeasurableSpace α] (p : Parent α)

def ComparedConditions (k : ℕ) (r u v m H : ℝ)
    (layers : Fin 3 → ProjectedLayer α) (law : Measure (α × ℝ)) (count : Fin 2 → ℕ) (parent : ∀ a, Fin (count a) → Fin (p.n k r)) (coarse : ∀ a, Fin (count a) → Fin (layers 0).count) (fine : ∀ a, Fin (count a) → Fin (layers a.succ).count) (domain : ∀ a, Fin (count a) → ℤ × ℤ × ℤ) (event : ∀ a, Fin (count a) → Set (α × ℝ)) (coarseChoices : Fin (p.n k r) → (Fin 2 → ℤ) → Finset (Fin (layers 0).count)) (fineChoices : ∀ a : Fin 2, Fin (p.n k r) → Fin (layers 0).count →
    Finset (Fin (layers a.succ).count)) (offset : ∀ a : Fin 2, Fin (p.n k r) → Fin (layers 0).count → Fin (layers a.succ).count → ℝ) : Prop :=
  (2 ≤ H) ∧
  (∀ a, (layers a).Valid p k (![r, r + u, r + v] a) m H) ∧
  (∀ a i e, |((layers a).G i).coeff e| ≤ p.N k ^ (m / 1000)) ∧
  (law ≤ p.ρ k) ∧
  (ENNReal.ofReal H⁻¹ ≤ law univ) ∧
  (∀ a e, MeasurableSet (event a e)) ∧
  (∀ a, Pairwise (fun e f => Disjoint (event a e) (event a f))) ∧
  (∀ a, ∀ᵐ ω ∂law, ∃ e, ω ∈ event a e) ∧
  (∀ a, Function.Injective
    (fun e => (parent a e, coarse a e, fine a e, domain a e))) ∧
  (∀ a e ω, ω ∈ event a e →
    ω ∈ p.baseGood k ∧ ω.1 ∈ p.B k r (parent a e) ∧
      ω.2 ∈ block (p.T k r) (p.j k r (parent a e)) ∧
      ω.1 ∈ (layers 0).C (coarse a e) ∧ ω.1 ∈ (layers a.succ).C (fine a e) ∧
      p.domainCode k ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) ω = domain a e) ∧
  (∀ a e,
    0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0}) ∧
  (∀ a e,
    ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d / H) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0} ≤ law (event a e)) ∧
  (∀ a,
    (∑ e, ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0}) ≤ ENNReal.ofReal H) ∧
  (∀ Q tag, ((coarseChoices Q tag).card : ℝ) ≤ H ^ 4) ∧
  (∀ a e,
    coarse a e ∈ coarseChoices (parent a e) ((layers 0).tag (coarse a e))) ∧
  (∀ a Q i,
    ((fineChoices a Q i).card : ℝ) ≤ H ^ 4 * p.N k ^ (p.d * ![u, v] a)) ∧
  (∀ a e, fine a e ∈ fineChoices a (parent a e) (coarse a e)) ∧
  (∀ a Q i j, j ∈ fineChoices a Q i → |offset a Q i j| ≤ H * p.N k ^ (-r)) ∧
  (∀ a Q i j, j ∈ fineChoices a Q i → ∀ z ∈ p.trueFiberBox k r m H Q ((layers 0).tag i),
    |MvPolynomial.eval ![z 0, z 2] ((layers a.succ).G j) -
      MvPolynomial.eval ![z 0, z 2] ((layers 0).G i) - offset a Q i j| ≤
        H * p.N k ^ (-r - ![u, v] a)) ∧
  (∀ a Q i x δ, p.N k ^ (-r - ![u, v] a) ≤ δ →
    (((fineChoices a Q i).filter (fun j => |offset a Q i j - x| ≤ δ)).card : ℝ) ≤
      H ^ 10 * (δ / p.N k ^ (-r - ![u, v] a)) ^ p.d) ∧
  (∀ a tag D j,
    ((Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e,
      parent a e = Q ∧ (layers 0).tag (coarse a e) = tag ∧ domain a e = D ∧ fine a e = j)).card : ℝ) ≤ H ^ 4)

def Samples (k : ℕ) (r u v m H : ℝ) : Prop :=
  ∃ (beta : Fin 3 → ℝ)
    (projectedCount : Fin 3 → ℕ)
    (projectedSets : (a : Fin 3) → Fin (projectedCount a) → Set α)
    (projectedTag : (a : Fin 3) → Fin (projectedCount a) → Fin 2 → ℤ)
    (projectedU : (a : Fin 3) → Fin (projectedCount a) → ℝ)
    (projectedV : (a : Fin 3) → Fin (projectedCount a) → ℝ)
    (projectedG : (a : Fin 3) → Fin (projectedCount a) → MvPolynomial (Fin 2) ℝ)
    (law : Measure (α × ℝ))
    (count : Fin 2 → ℕ)
    (parent : ∀ a, Fin (count a) → Fin (p.n k r))
    (coarse : ∀ a, Fin (count a) → Fin (projectedCount 0))
    (fine : ∀ a, Fin (count a) → Fin (projectedCount a.succ))
    (domain : ∀ a, Fin (count a) → ℤ × ℤ × ℤ)
    (event : ∀ a, Fin (count a) → Set (α × ℝ))
    (coarseChoices : Fin (p.n k r) → (Fin 2 → ℤ) → Finset (Fin (projectedCount 0)))
    (fineChoices : ∀ a : Fin 2, Fin (p.n k r) → Fin (projectedCount 0) →
    Finset (Fin (projectedCount a.succ)))
    (offset : ∀ a : Fin 2, Fin (p.n k r) → Fin (projectedCount 0) → Fin (projectedCount a.succ) → ℝ),
    ComparedConditions p k r u v m H (fun a => (⟨beta a, projectedCount a, projectedSets a, projectedTag a, projectedU a, projectedV a, projectedG a⟩ : ProjectedLayer α)) law count parent coarse fine domain event coarseChoices fineChoices offset

theorem samples_of_sample {k : ℕ} {r u v m H : ℝ}
    (f : p.ComparedSample k r u v m H) : Samples p k r u v m H := by
  exact ⟨(fun a => (f.layers a).β), (fun a => (f.layers a).count), (fun a => (f.layers a).C), (fun a => (f.layers a).tag), (fun a => (f.layers a).u), (fun a => (f.layers a).v), (fun a => (f.layers a).G), f.law, f.count, f.parent, f.coarse, f.fine, f.domain, f.event, f.coarseChoices, f.fineChoices, f.offset, f.loss_one, f.layer_valid, f.coefficient_bound, f.le_rho, f.mass_lower, f.event_measurable, f.event_disjoint, f.event_cover, f.entry_injective, f.event_data, f.palette_positive, f.event_floor, f.reference_budget, f.coarse_card, f.coarse_mem, f.fine_card, f.fine_mem, f.offset_bound, f.offset_fit, f.offset_count, f.reverse_count⟩

theorem sample_of_samples {k : ℕ} {r u v m H : ℝ}
    (h : Samples p k r u v m H) : Nonempty (p.ComparedSample k r u v m H) := by
  rcases h with ⟨beta, projectedCount, projectedSets, projectedTag, projectedU, projectedV, projectedG, law, count, parent, coarse, fine, domain, event, coarseChoices, fineChoices, offset, h⟩
  rcases h with ⟨h_loss_one, h_layer_valid, h_coefficient_bound, h_le_rho, h_mass_lower, h_event_measurable, h_event_disjoint, h_event_cover, h_entry_injective, h_event_data, h_palette_positive, h_event_floor, h_reference_budget, h_coarse_card, h_coarse_mem, h_fine_card, h_fine_mem, h_offset_bound, h_offset_fit, h_offset_count, h_reverse_count⟩
  exact ⟨{
    layers := fun a => (⟨beta a, projectedCount a, projectedSets a, projectedTag a, projectedU a, projectedV a, projectedG a⟩ : ProjectedLayer α)
    law := law
    count := count
    parent := parent
    coarse := coarse
    fine := fine
    domain := domain
    event := event
    coarseChoices := coarseChoices
    fineChoices := fineChoices
    offset := offset
    loss_one := h_loss_one
    layer_valid := h_layer_valid
    coefficient_bound := h_coefficient_bound
    le_rho := h_le_rho
    mass_lower := h_mass_lower
    event_measurable := h_event_measurable
    event_disjoint := h_event_disjoint
    event_cover := h_event_cover
    entry_injective := h_entry_injective
    event_data := h_event_data
    palette_positive := h_palette_positive
    event_floor := h_event_floor
    reference_budget := h_reference_budget
    coarse_card := h_coarse_card
    coarse_mem := h_coarse_mem
    fine_card := h_fine_card
    fine_mem := h_fine_mem
    offset_bound := h_offset_bound
    offset_fit := h_offset_fit
    offset_count := h_offset_count
    reverse_count := h_reverse_count }⟩

end Unpacked
end
end Submission.Obl.k4_general_parent_wide_layer_candidates.Split
