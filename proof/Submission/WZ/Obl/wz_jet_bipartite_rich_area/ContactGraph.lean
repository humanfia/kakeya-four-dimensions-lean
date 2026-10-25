-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGraph.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGrid

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open scoped Classical

open Classical in
/-- The simple graph obtained from the chosen witnesses of contact cells. -/
def cellRelation {α β : Type*} (S : Finset (ℤ × ℤ × ℤ))
    (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β) (a : α) (b : β) : Prop :=
  (a, b) ∈ S.image (fun t => (red t, blue t))

/-- One cell is retained for every edge. The value off the graph is immaterial. -/
def cellRepresentative {α β : Type*} (S : Finset (ℤ × ℤ × ℤ))
    (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β) (a : α) (b : β) : ℤ × ℤ × ℤ := by
  classical
  exact if h : cellRelation S red blue a b then
    Classical.choose (Finset.mem_image.mp h) else (0, 0, 0)

theorem cellRepresentative_spec {α β : Type*} (S : Finset (ℤ × ℤ × ℤ))
    (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β) {a : α} {b : β}
    (hab : cellRelation S red blue a b) :
    cellRepresentative S red blue a b ∈ S ∧
      red (cellRepresentative S red blue a b) = a ∧
      blue (cellRepresentative S red blue a b) = b := by
  classical
  simp only [cellRepresentative, dite_eq_left hab]
  have h := Classical.choose_spec (Finset.mem_image.mp hab)
  exact ⟨h.1, congrArg Prod.fst h.2, congrArg Prod.snd h.2⟩

/-- The incidence sum is the cardinality of the image of the cell-pair map. -/
theorem card_cell_edges {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β) :
    (S.image (fun t => (red t, blue t))).card =
      ∑ a, Fintype.card {b // cellRelation S red blue a b} := by
  classical
  let E := S.image (fun t => (red t, blue t))
  let e : {p : α × β // p ∈ E} ≃ Σ a : α, {b // cellRelation S red blue a b} :=
    { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
      invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ => rfl
      right_inv := fun ⟨a, ⟨b, h⟩⟩ => rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_coe, Fintype.card_sigma] using he

/-- A bound on the number of cells per pair transfers area counting to the
simple contact graph. -/
theorem card_cells_le_mul_incidence {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (M : ℕ) (hfiber : ∀ a b, (S.filter (fun t => red t = a ∧ blue t = b)).card ≤ M) :
    S.card ≤ M * ∑ a, Fintype.card {b // cellRelation S red blue a b} := by
  classical
  rw [← card_cell_edges S red blue]
  apply Finset.card_le_mul_card_image S M
  intro p hp
  rcases p with ⟨a, b⟩
  simpa only [Prod.mk.injEq] using hfiber a b

/-- Crowding of cells along a red curve bounds the nearby neighbors of the
selected simple graph. -/
theorem card_cell_red_neighbors_le {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) {sep : ℝ} (H : ℕ)
    (hlocal : ∀ t ∈ S,
      (S.filter (fun u => red u = red t ∧ |tag t - tag u| ≤ sep)).card ≤ H)
    {a : α} {b : β} (hab : cellRelation S red blue a b) :
    Fintype.card {b' // cellRelation S red blue a b' ∧
      |tag (cellRepresentative S red blue a b) - tag (cellRepresentative S red blue a b')| ≤ sep}
      ≤ H := by
  classical
  let t := cellRepresentative S red blue a b
  let T := S.filter (fun u => red u = red t ∧ |tag t - tag u| ≤ sep)
  have ht := cellRepresentative_spec S red blue hab
  let f : {b' // cellRelation S red blue a b' ∧
      |tag t - tag (cellRepresentative S red blue a b')| ≤ sep} → {u // u ∈ T} :=
    fun b' => ⟨cellRepresentative S red blue a b', by
      have hu := cellRepresentative_spec S red blue b'.2.1
      exact Finset.mem_filter.mpr ⟨hu.1, hu.2.1.trans ht.2.1.symm, b'.2.2⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have heq := congrArg Subtype.val huv
    have hu := cellRepresentative_spec S red blue u.2.1
    have hv := cellRepresentative_spec S red blue v.2.1
    exact hu.2.2.symm.trans ((congrArg blue heq).trans hv.2.2)
  have hc := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card {u // u ∈ T} = T.card := Fintype.card_coe _
  rw [hcard] at hc
  exact hc.trans (hlocal t ht.1)

/-- The concrete quantized-jet crowding bound supplies the red-neighbor budget. -/
theorem card_cell_red_neighbors_of_jetCells {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) (g : α → ℝ → ℝ) (f₀ : ℝ → ℝ)
    {δ s ℓ w sep : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (C L : ℕ)
    (hcell : ∀ t ∈ S, JetCell (g (red t)) f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (hscale : sep + ℓ ≤ L * ℓ) {a : α} {b : β} (hab : cellRelation S red blue a b) :
    Fintype.card {b' // cellRelation S red blue a b' ∧
      |tag (cellRepresentative S red blue a b) - tag (cellRepresentative S red blue a b')| ≤ sep}
      ≤ (4 * C + 1) ^ 2 * (4 * L + 1) := by
  apply card_cell_red_neighbors_le S red blue tag _ ?_ hab
  intro t ht
  apply card_jetCell_tag_window _ tag hδ hs hℓ C L (f := g (red t)) (f₀ := f₀)
    (w := w) (z := tag t) (R := sep) ?_ ?_ ?_ hscale
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    simpa only [hu'.2.1] using hcell u hu'.1
  · intro u hu
    exact hnear u (Finset.mem_filter.mp hu).1
  · intro u hu
    simpa only [abs_sub_comm] using (Finset.mem_filter.mp hu).2.2

/-- The analogous nearby-neighbor bound along a blue curve. -/
theorem card_cell_blue_neighbors_le {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) {sep : ℝ} (H : ℕ)
    (hlocal : ∀ t ∈ S,
      (S.filter (fun u => blue u = blue t ∧ |tag t - tag u| ≤ sep)).card ≤ H)
    {a : α} {b : β} (hab : cellRelation S red blue a b) :
    Fintype.card {a' // cellRelation S red blue a' b ∧
      |tag (cellRepresentative S red blue a b) - tag (cellRepresentative S red blue a' b)| ≤ sep}
      ≤ H := by
  classical
  let t := cellRepresentative S red blue a b
  let T := S.filter (fun u => blue u = blue t ∧ |tag t - tag u| ≤ sep)
  have ht := cellRepresentative_spec S red blue hab
  let f : {a' // cellRelation S red blue a' b ∧
      |tag t - tag (cellRepresentative S red blue a' b)| ≤ sep} → {u // u ∈ T} :=
    fun a' => ⟨cellRepresentative S red blue a' b, by
      have hu := cellRepresentative_spec S red blue a'.2.1
      exact Finset.mem_filter.mpr ⟨hu.1, hu.2.2.trans ht.2.2.symm, a'.2.2⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have heq := congrArg Subtype.val huv
    have hu := cellRepresentative_spec S red blue u.2.1
    have hv := cellRepresentative_spec S red blue v.2.1
    exact hu.2.1.symm.trans ((congrArg red heq).trans hv.2.1)
  have hc := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card {u // u ∈ T} = T.card := Fintype.card_coe _
  rw [hcard] at hc
  exact hc.trans (hlocal t ht.1)

/-- The concrete quantized-jet crowding bound supplies the blue-neighbor budget. -/
theorem card_cell_blue_neighbors_of_jetCells {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset (ℤ × ℤ × ℤ)) (red : ℤ × ℤ × ℤ → α) (blue : ℤ × ℤ × ℤ → β)
    (tag : ℤ × ℤ × ℤ → ℝ) (g : β → ℝ → ℝ) (f₀ : ℝ → ℝ)
    {δ s ℓ w sep : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hℓ : 0 < ℓ) (C L : ℕ)
    (hcell : ∀ t ∈ S, JetCell (g (blue t)) f₀ δ s ℓ w C t)
    (hnear : ∀ t ∈ S, |tag t - (w + t.1 * ℓ)| ≤ ℓ)
    (hscale : sep + ℓ ≤ L * ℓ) {a : α} {b : β} (hab : cellRelation S red blue a b) :
    Fintype.card {a' // cellRelation S red blue a' b ∧
      |tag (cellRepresentative S red blue a b) - tag (cellRepresentative S red blue a' b)| ≤ sep}
      ≤ (4 * C + 1) ^ 2 * (4 * L + 1) := by
  apply card_cell_blue_neighbors_le S red blue tag _ ?_ hab
  intro t ht
  apply card_jetCell_tag_window _ tag hδ hs hℓ C L (f := g (blue t)) (f₀ := f₀)
    (w := w) (z := tag t) (R := sep) ?_ ?_ ?_ hscale
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    simpa only [hu'.2.1] using hcell u hu'.1
  · intro u hu
    exact hnear u (Finset.mem_filter.mp hu).1
  · intro u hu
    simpa only [abs_sub_comm] using (Finset.mem_filter.mp hu).2.2

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
