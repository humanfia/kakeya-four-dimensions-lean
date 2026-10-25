-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactGraphBound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactIncidence
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.DegreeRegular

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set
open scoped Classical
open WangZahlLot.Obl.wz_jet_close_pair_moment
set_option backward.isDefEq.respectTransparency false

/-- The near-contact graph bound after dyadic degree regularization. Only
local time crowding is required of the graph; the logarithmic factor pays
for restriction to a regular subgraph. -/
theorem incidence_le_of_crowded_near_contacts {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (hsep : ∀ i j, i ≠ j → 0 < dist (q i) (q j))
    (aIdx : α ↪ Fin n) (bIdx : β ↪ Fin n)
    (R : α → β → Prop) (tag : α → β → ℝ)
    {l u γ M δ η B s : ℝ} {H : ℕ}
    (hl : -1 ≤ l) (hu : u ≤ 1) (hlu : l ≤ u) (hshort : u - l ≤ 1 / 10000)
    (hγ : 0 < γ) (hB : 1 < B) (hs : 0 < s)
    (hratio : 2 * M * B ≤ γ) (hslope : 4 * η ≤ γ * s) (hvalue : 8 * δ < γ * s ^ 2)
    (hwithinA : ∀ a a' t, t ∈ Icc l u →
      |deriv (deriv (g (aIdx a))) t - deriv (deriv (g (aIdx a'))) t| ≤ M)
    (hwithinB : ∀ b b' t, t ∈ Icc l u →
      |deriv (deriv (g (bIdx b))) t - deriv (deriv (g (bIdx b'))) t| ≤ M)
    (hcross : (∀ a b t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (aIdx a))) t - deriv (deriv (g (bIdx b))) t) ∨
      (∀ a b t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (bIdx b))) t - deriv (deriv (g (aIdx a))) t))
    (htag : ∀ a b, R a b → tag a b ∈ Icc l u)
    (hcontact : ∀ a b, R a b → NearContact δ η (g (aIdx a)) (g (bIdx b)) (tag a b))
    (hH : 1 ≤ H)
    (hHA : ∀ a b, R a b → Fintype.card {b' // R a b' ∧ |tag a b - tag a b'| ≤ s} ≤ H)
    (hHB : ∀ a b, R a b → Fintype.card {a' // R a' b ∧ |tag a b - tag a' b| ≤ s} ≤ H) :
    (∑ a, (Fintype.card {b // R a b} : ℝ)) ≤
      16 * ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) *
        (((Nat.log 2 (Fintype.card α + Fintype.card β) + 1 : ℕ) : ℝ) ^ 3) * Real.sqrt (2 * H) *
        ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) *
        Real.sqrt ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) := by
  classical
  let L : ℝ := (Nat.log 2 (Fintype.card α + Fintype.card β) + 1 : ℕ)
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast Nat.le_add_left 1 _
  obtain ⟨A, B', ΔA, ΔB, hkeep, hdegA, hdegB, hregA, hregB⟩ := exists_regular_subrelation R
  let aIdx' : A ↪ Fin n := ⟨fun a => aIdx a, fun a b h => Subtype.ext (aIdx.injective h)⟩
  let bIdx' : B' ↪ Fin n := ⟨fun b => bIdx b, fun a b h => Subtype.ext (bIdx.injective h)⟩
  let R' : A → B' → Prop := fun a b => R a b
  let tag' : A → B' → ℝ := fun a b => tag a b
  have hHA' : ∀ a b, R' a b →
      Fintype.card {b' // R' a b' ∧ |tag' a b - tag' a b'| ≤ s} ≤ H := by
    intro a b hab
    let f : {b' : B' // R' a b' ∧ |tag' a b - tag' a b'| ≤ s} →
        {b' : β // R a b' ∧ |tag a b - tag a b'| ≤ s} := fun z => ⟨z.1.1, z.2⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {b' : β // R a b' ∧ |tag a b - tag a b'| ≤ s} => z.1) h
    exact (Fintype.card_le_of_injective f hf).trans (hHA a b hab)
  have hHB' : ∀ a b, R' a b →
      Fintype.card {a' // R' a' b ∧ |tag' a b - tag' a' b| ≤ s} ≤ H := by
    intro a b hab
    let f : {a' : A // R' a' b ∧ |tag' a b - tag' a' b| ≤ s} →
        {a' : α // R a' b ∧ |tag a b - tag a' b| ≤ s} := fun z => ⟨z.1.1, z.2⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {a' : α // R a' b ∧ |tag a b - tag a' b| ≤ s} => z.1) h
    exact (Fintype.card_le_of_injective f hf).trans (hHB a b hab)
  have hcross' : (∀ (a : A) (b : B') t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (aIdx' a))) t - deriv (deriv (g (bIdx' b))) t) ∨
      (∀ (a : A) (b : B') t, t ∈ Icc l u →
        γ ≤ deriv (deriv (g (bIdx' b))) t - deriv (deriv (g (aIdx' a))) t) := by
    rcases hcross with h | h
    · exact Or.inl (fun a b t ht => h a b t ht)
    · exact Or.inr (fun a b t ht => h a b t ht)
  have hbound := incidence_le_of_near_contacts hg hjet hsep aIdx' bIdx' R' tag'
    hl hu hlu hshort hγ hB hs hratio hslope hvalue
    (fun a a' t ht => hwithinA a a' t ht) (fun b b' t ht => hwithinB b b' t ht)
    hcross' (fun a b hab => htag a b hab) (fun a b hab => hcontact a b hab)
    hH (show 1 ≤ 2 * L by linarith) hHA' hHB' hdegA hdegB hregA hregB
  have hmass : (Fintype.card A : ℝ) + (Fintype.card B' : ℝ) ≤
      (Fintype.card α : ℝ) + (Fintype.card β : ℝ) := by
    apply add_le_add
    · exact_mod_cast Fintype.card_le_of_injective (fun a : A => (a : α)) Subtype.val_injective
    · exact_mod_cast Fintype.card_le_of_injective (fun b : B' => (b : β)) Subtype.val_injective
  calc
    _ ≤ L ^ 2 * (∑ a : A, (Fintype.card {b : B' // R a b} : ℝ)) := hkeep
    _ ≤ L ^ 2 * (8 * ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) * (2 * L) *
        Real.sqrt (2 * H) * ((Fintype.card A : ℝ) + (Fintype.card B' : ℝ)) *
        Real.sqrt ((Fintype.card A : ℝ) + (Fintype.card B' : ℝ))) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg L)
    _ ≤ L ^ 2 * (8 * ((4 : ℝ) ^ (windowLensHeight B s l u + 1) + 1) * (2 * L) *
        Real.sqrt (2 * H) * ((Fintype.card α : ℝ) + (Fintype.card β : ℝ)) *
        Real.sqrt ((Fintype.card α : ℝ) + (Fintype.card β : ℝ))) := by
      gcongr
    _ = _ := by dsimp [L]; ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
