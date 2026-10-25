import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparedInterface
import Submission.Obl.k4_general_wide_layer_offset_comparison.FinalFloors

/-! The comparison table fields are adapted from this LOT tree, obligation o254,
session x0912, `ComparedInterface.lean`. They retain the same original witnesses;
only the current event floors are deferred to simultaneous final-law renewal. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Compared original entries with geometric and counting certificates, before
renewing their mass floors under one final common law. -/
structure ComparisonTable (k : ℕ) (r u v m H R : ℝ) where
  loss_one : 2 ≤ H
  layers : Fin 3 → ProjectedLayer α
  layer_valid : ∀ a, (layers a).Valid p k (![r, r + u, r + v] a) m H
  coefficient_bound : ∀ a i e, |((layers a).G i).coeff e| ≤ p.N k ^ (m / 1000)
  law : Measure (α × ℝ)
  le_rho : law ≤ p.ρ k
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
  reference_budget : ∀ a,
    (∑ e, ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers 0).tag (coarse a e) 0}) ≤ ENNReal.ofReal R
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


namespace ComparisonTable

variable {p} {k : ℕ} {r u v m H R : ℝ}

/-- Simultaneous renewal followed by injective reindexing turns a compared
table into the exact compared sample, including all original references. -/
theorem renew (t : p.ComparisonTable k r u v m H R)
    [IsFiniteMeasure t.law]
    {h : ℝ} (hh : 1 ≤ h) (hR : 1 ≤ R) (hH : 4 * h * R ≤ H)
    (hmass : ENNReal.ofReal h⁻¹ ≤ t.law univ) :
    Nonempty (p.ComparedSample k r u v m H) := by
  classical
  have hhp : 0 < h := zero_lt_one.trans_le hh
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hHp : 0 < H := by linarith [t.loss_one]
  have h2h : 2 * h ≤ H := by nlinarith
  have hRH : R ≤ H := by nlinarith
  let ref : ∀ a, Fin (t.count a) → ℝ≥0∞ := fun a e =>
    ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - ![u, v] a)) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers 0).tag (t.coarse a e) 0}
  obtain ⟨lam, keep, hlam, hlammass, hfloor, hbudget, hcover⟩ :=
    two_color_final_floors t.law t.count t.event t.event_measurable ref
      t.event_cover hhp hRp hmass t.reference_budget
  let Good (a : Fin 2) := {i : Fin (t.count a) // i ∈ keep a}
  let cnt : Fin 2 → ℕ := fun a => Fintype.card (Good a)
  let equiv (a : Fin 2) : Good a ≃ Fin (cnt a) := Fintype.equivFin (Good a)
  let idx (a : Fin 2) (i : Fin (cnt a)) : Fin (t.count a) := ((equiv a).symm i).val
  have hidx (a : Fin 2) : Function.Injective (idx a) := by
    intro i j hij
    exact (equiv a).symm.injective (Subtype.ext hij)
  have hmem (a : Fin 2) (i : Fin (cnt a)) : idx a i ∈ keep a :=
    ((equiv a).symm i).property
  refine ⟨{
    loss_one := t.loss_one
    layers := t.layers
    layer_valid := t.layer_valid
    coefficient_bound := t.coefficient_bound
    law := lam
    le_rho := hlam.trans t.le_rho
    mass_lower := (ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) h2h)).trans hlammass
    count := cnt
    parent := fun a e => t.parent a (idx a e)
    coarse := fun a e => t.coarse a (idx a e)
    fine := fun a e => t.fine a (idx a e)
    domain := fun a e => t.domain a (idx a e)
    event := fun a e => t.event a (idx a e)
    event_measurable := fun a e => t.event_measurable a (idx a e)
    event_disjoint := fun a e f hne => t.event_disjoint a ((hidx a).ne hne)
    event_cover := ?_
    entry_injective := fun a e f heq => hidx a (t.entry_injective a heq)
    event_data := fun a e => t.event_data a (idx a e)
    palette_positive := fun a e => t.palette_positive a (idx a e)
    event_floor := ?_
    reference_budget := ?_
    coarseChoices := t.coarseChoices
    coarse_card := t.coarse_card
    coarse_mem := fun a e => t.coarse_mem a (idx a e)
    fineChoices := t.fineChoices
    fine_card := t.fine_card
    fine_mem := fun a e => t.fine_mem a (idx a e)
    offset := t.offset
    offset_bound := t.offset_bound
    offset_fit := t.offset_fit
    offset_count := t.offset_count
    reverse_count := ?_ }⟩
  · intro a
    filter_upwards [hcover a] with ω hω
    obtain ⟨i, hi, hωi⟩ := hω
    refine ⟨equiv a ⟨i, hi⟩, ?_⟩
    simpa only [idx, Equiv.symm_apply_apply] using hωi
  · intro a e
    have hf := (hfloor a (idx a e) (hmem a e)).2
    have hδ : H⁻¹ ≤ (4 * h * R)⁻¹ := inv_anti₀ (by positivity) hH
    calc
      _ = ENNReal.ofReal H⁻¹ * ref a (idx a e) := by
        dsimp [ref]
        conv_rhs => rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hHp.le)]
        congr 2
        ring
      _ ≤ ENNReal.ofReal ((4 * h * R)⁻¹) * ref a (idx a e) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hδ) le_rfl
      _ ≤ _ := hf
  · intro a
    have heq : (∑ e, ref a (idx a e)) = ∑ i ∈ keep a, ref a i := by
      calc
        _ = ∑ i : Good a, ref a i.val :=
          Fintype.sum_equiv (equiv a).symm _ _ (fun _ => rfl)
        _ = _ := Finset.sum_coe_sort _ _
    change (∑ e, ref a (idx a e)) ≤ ENNReal.ofReal H
    rw [heq]
    exact (hbudget a).trans (ENNReal.ofReal_le_ofReal hRH)
  · intro a tag D j
    have hsub : (Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e : Fin (cnt a),
        t.parent a (idx a e) = Q ∧ (t.layers 0).tag (t.coarse a (idx a e)) = tag ∧
          t.domain a (idx a e) = D ∧ t.fine a (idx a e) = j)) ⊆
      Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e,
        t.parent a e = Q ∧ (t.layers 0).tag (t.coarse a e) = tag ∧
          t.domain a e = D ∧ t.fine a e = j) := by
      intro Q hQ
      obtain ⟨-, e, he⟩ := Finset.mem_filter.mp hQ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, idx a e, he⟩
    have hcard : ((Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e : Fin (cnt a),
        t.parent a (idx a e) = Q ∧ (t.layers 0).tag (t.coarse a (idx a e)) = tag ∧
          t.domain a (idx a e) = D ∧ t.fine a (idx a e) = j)).card : ℝ) ≤
      ((Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e,
        t.parent a e = Q ∧ (t.layers 0).tag (t.coarse a e) = tag ∧
          t.domain a e = D ∧ t.fine a e = j)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (t.reverse_count a tag D j)

end ComparisonTable
end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
