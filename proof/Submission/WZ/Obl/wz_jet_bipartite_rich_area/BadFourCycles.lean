-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.BadFourCycles.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Counting four-cycles that contain a bad wedge

An abstract bipartite relation `R : α → β → Prop` carries, at every vertex, a
"bad wedge" relation between two of its neighbours (in the application: two
contacts along one curve whose contact times are too close). If every edge lies
in at most `H` bad wedges at each of its endpoints, and the degrees are at most
`ΔA` and `ΔB`, then the ordered four-cycles (in the format of `FourCycleCount`)
having a bad wedge at one of their four vertices number at most
`2 * H * E * (ΔA + ΔB)`, where `E` is the number of edges.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Finset
open scoped Classical

/-- The two elements of `Fin 2` are `s` and `s.rev`. -/
private theorem fin_two_eq_or_eq_rev (s i : Fin 2) : i = s ∨ i = s.rev := by
  fin_cases s <;> fin_cases i <;> simp [Fin.rev]

private theorem embedding_fin_two_ext {γ : Type*} (s : Fin 2) {f g : Fin 2 ↪ γ}
    (h1 : f s = g s) (h2 : f s.rev = g s.rev) : f = g := by
  ext i
  rcases fin_two_eq_or_eq_rev s i with rfl | rfl
  · exact h1
  · exact h2

/-- The codomain of the charging map for wedges at a red vertex: an edge `(a, b)`,
a second neighbour `b'` of `a` forming a bad wedge with `b`, and a second
neighbour `a'` of `b`. -/
private abbrev RedCharge {α β : Type*} (R : α → β → Prop) (W : α → β → β → Prop) :=
  Σ x : {x : α × β // R x.1 x.2},
    {b' : β // R x.1.1 b' ∧ W x.1.1 x.1.2 b'} × {a' : α // R a' x.1.2}

private theorem card_redCharge_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (W : α → β → β → Prop) {H Δ : ℕ}
    (hW : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ W a b b'} ≤ H)
    (hΔ : ∀ b, Fintype.card {a // R a b} ≤ Δ) :
    Fintype.card (RedCharge R W) ≤
      Fintype.card {x : α × β // R x.1 x.2} * (H * Δ) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _x : {x : α × β // R x.1 x.2}, H * Δ := by
      apply Finset.sum_le_sum
      intro x _
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul (hW _ _ x.2) (hΔ _)
    _ = _ := by simp

/-- Ordered four-cycles with a bad wedge at one of their two red vertices. -/
theorem card_four_cycles_red_bad_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (W : α → β → β → Prop) {H Δ : ℕ}
    (hW : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ W a b b'} ≤ H)
    (hΔ : ∀ b, Fintype.card {a // R a b} ≤ Δ) :
    Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ s, W (p.2 s) (p.1 0) (p.1 1)} ≤
      2 * (Fintype.card {x : α × β // R x.1 x.2} * (H * Δ)) := by
  let P := {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
    (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ s, W (p.2 s) (p.1 0) (p.1 1)}
  let σ : P → Fin 2 := fun p => p.2.2.choose
  have hσ : ∀ p : P, W (p.1.2 (σ p)) (p.1.1 0) (p.1.1 1) := fun p => p.2.2.choose_spec
  let φ : P → Fin 2 × RedCharge R W := fun p =>
    (σ p, ⟨⟨(p.1.2 (σ p), p.1.1 0), p.2.1 _ _⟩,
      (⟨p.1.1 1, p.2.1 _ _, hσ p⟩, ⟨p.1.2 (σ p).rev, p.2.1 _ _⟩)⟩)
  let ψ : Fin 2 × RedCharge R W → Fin 2 × α × β × β × α := fun z =>
    (z.1, z.2.1.1.1, z.2.1.1.2, z.2.2.1.1, z.2.2.2.1)
  have hψφ : Function.Injective (ψ ∘ φ) := by
    intro p q hpq
    simp only [Function.comp, ψ, φ, Prod.mk.injEq] at hpq
    obtain ⟨hs, ha, hb0, hb1, ha'⟩ := hpq
    rw [hs] at ha ha'
    apply Subtype.ext
    apply Prod.ext
    · exact embedding_fin_two_ext 0 hb0 (by simpa [Fin.rev] using hb1)
    · exact embedding_fin_two_ext (σ q) ha ha'
  have hφ : Function.Injective φ := Function.Injective.of_comp hψφ
  calc
    Fintype.card P ≤ Fintype.card (Fin 2 × RedCharge R W) :=
      Fintype.card_le_of_injective φ hφ
    _ = 2 * Fintype.card (RedCharge R W) := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (card_redCharge_le R W hW hΔ)

/-- The codomain of the charging map for wedges at a blue vertex. -/
private abbrev BlueCharge {α β : Type*} (R : α → β → Prop) (W : β → α → α → Prop) :=
  Σ x : {x : α × β // R x.1 x.2},
    {a' : α // R a' x.1.2 ∧ W x.1.2 x.1.1 a'} × {b' : β // R x.1.1 b'}

private theorem card_blueCharge_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (W : β → α → α → Prop) {H Δ : ℕ}
    (hW : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ W b a a'} ≤ H)
    (hΔ : ∀ a, Fintype.card {b // R a b} ≤ Δ) :
    Fintype.card (BlueCharge R W) ≤
      Fintype.card {x : α × β // R x.1 x.2} * (H * Δ) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _x : {x : α × β // R x.1 x.2}, H * Δ := by
      apply Finset.sum_le_sum
      intro x _
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul (hW _ _ x.2) (hΔ _)
    _ = _ := by simp

/-- Ordered four-cycles with a bad wedge at one of their two blue vertices. -/
theorem card_four_cycles_blue_bad_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (W : β → α → α → Prop) {H Δ : ℕ}
    (hW : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ W b a a'} ≤ H)
    (hΔ : ∀ a, Fintype.card {b // R a b} ≤ Δ) :
    Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ t, W (p.1 t) (p.2 0) (p.2 1)} ≤
      2 * (Fintype.card {x : α × β // R x.1 x.2} * (H * Δ)) := by
  let P := {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
    (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ t, W (p.1 t) (p.2 0) (p.2 1)}
  let σ : P → Fin 2 := fun p => p.2.2.choose
  have hσ : ∀ p : P, W (p.1.1 (σ p)) (p.1.2 0) (p.1.2 1) := fun p => p.2.2.choose_spec
  let φ : P → Fin 2 × BlueCharge R W := fun p =>
    (σ p, ⟨⟨(p.1.2 0, p.1.1 (σ p)), p.2.1 _ _⟩,
      (⟨p.1.2 1, p.2.1 _ _, hσ p⟩, ⟨p.1.1 (σ p).rev, p.2.1 _ _⟩)⟩)
  let ψ : Fin 2 × BlueCharge R W → Fin 2 × α × β × α × β := fun z =>
    (z.1, z.2.1.1.1, z.2.1.1.2, z.2.2.1.1, z.2.2.2.1)
  have hψφ : Function.Injective (ψ ∘ φ) := by
    intro p q hpq
    simp only [Function.comp, ψ, φ, Prod.mk.injEq] at hpq
    obtain ⟨hs, ha0, hb, ha1, hb'⟩ := hpq
    rw [hs] at hb hb'
    apply Subtype.ext
    apply Prod.ext
    · exact embedding_fin_two_ext (σ q) hb hb'
    · exact embedding_fin_two_ext 0 ha0 (by simpa [Fin.rev] using ha1)
  have hφ : Function.Injective φ := Function.Injective.of_comp hψφ
  calc
    Fintype.card P ≤ Fintype.card (Fin 2 × BlueCharge R W) :=
      Fintype.card_le_of_injective φ hφ
    _ = 2 * Fintype.card (BlueCharge R W) := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (card_blueCharge_le R W hW hΔ)

/-- **Bad four-cycles.** Ordered four-cycles (two distinct blue vertices `p.1 0, p.1 1`,
two distinct red vertices `p.2 0, p.2 1`, all four edges present) that have a bad wedge
at one of their four vertices number at most `2 E H (ΔA + ΔB)`, where `E` is the number
of edges, every edge lies in at most `H` bad wedges at each endpoint, and the red and
blue degrees are at most `ΔA` and `ΔB`. -/
theorem card_four_cycles_bad_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (WA : α → β → β → Prop) (WB : β → α → α → Prop) {H ΔA ΔB : ℕ}
    (hWA : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ WA a b b'} ≤ H)
    (hWB : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ WB b a a'} ≤ H)
    (hΔA : ∀ a, Fintype.card {b // R a b} ≤ ΔA)
    (hΔB : ∀ b, Fintype.card {a // R a b} ≤ ΔB) :
    Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      (∀ s t, R (p.2 s) (p.1 t)) ∧
        ((∃ s, WA (p.2 s) (p.1 0) (p.1 1)) ∨ ∃ t, WB (p.1 t) (p.2 0) (p.2 1))} ≤
      2 * H * Fintype.card {x : α × β // R x.1 x.2} * (ΔA + ΔB) := by
  have hsplit := Fintype.card_subtype_or
    (fun p : (Fin 2 ↪ β) × (Fin 2 ↪ α) =>
      (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ s, WA (p.2 s) (p.1 0) (p.1 1))
    (fun p : (Fin 2 ↪ β) × (Fin 2 ↪ α) =>
      (∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ t, WB (p.1 t) (p.2 0) (p.2 1))
  have hcongr : Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      (∀ s t, R (p.2 s) (p.1 t)) ∧
        ((∃ s, WA (p.2 s) (p.1 0) (p.1 1)) ∨ ∃ t, WB (p.1 t) (p.2 0) (p.2 1))} =
      Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
        ((∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ s, WA (p.2 s) (p.1 0) (p.1 1)) ∨
          ((∀ s t, R (p.2 s) (p.1 t)) ∧ ∃ t, WB (p.1 t) (p.2 0) (p.2 1))} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_or_left))
  rw [hcongr]
  refine hsplit.trans ?_
  have h1 := card_four_cycles_red_bad_le R WA hWA hΔB
  have h2 := card_four_cycles_blue_bad_le R WB hWB hΔA
  calc
    _ ≤ 2 * (Fintype.card {x : α × β // R x.1 x.2} * (H * ΔB)) +
        2 * (Fintype.card {x : α × β // R x.1 x.2} * (H * ΔA)) := Nat.add_le_add h1 h2
    _ = _ := by ring

/-- The bad-cycle count with contact times: a wedge is bad when the contact times of
its two edges differ by at most `s`. -/
theorem card_four_cycles_close_times_le {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) (t : α → β → ℝ) (s : ℝ) {H ΔA ΔB : ℕ}
    (hHA : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ |t a b - t a b'| ≤ s} ≤ H)
    (hHB : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ |t a b - t a' b| ≤ s} ≤ H)
    (hΔA : ∀ a, Fintype.card {b // R a b} ≤ ΔA)
    (hΔB : ∀ b, Fintype.card {a // R a b} ≤ ΔB) :
    Fintype.card {p : (Fin 2 ↪ β) × (Fin 2 ↪ α) //
      (∀ i j, R (p.2 i) (p.1 j)) ∧
        ((∃ i, |t (p.2 i) (p.1 0) - t (p.2 i) (p.1 1)| ≤ s) ∨
          ∃ j, |t (p.2 0) (p.1 j) - t (p.2 1) (p.1 j)| ≤ s)} ≤
      2 * H * Fintype.card {x : α × β // R x.1 x.2} * (ΔA + ΔB) :=
  card_four_cycles_bad_le R (fun a b b' => |t a b - t a b'| ≤ s)
    (fun b a a' => |t a b - t a' b| ≤ s) hHA hHB hΔA hΔB

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
