import Submission.Obl.k4_matching_cofinal_palette_selection.Data
import Submission.Obl.k4_matching_cofinal_palette_selection.PaletteBox

/-!
# The reference palette on a reference fiber (o069)

In the vocabulary of `Data.lean`: on an admissible step the accuracy of the
active order at the reference time is `β v` (`accuracy_at_reference_of_admissible`),
so on each `F_z` fiber of the support the reference palette lies in a box of
`(⌊N^(6/q)⌋₊ + 2)^2` points (`referencePalette_fiber_subset_box`).  Hence its
image on a fiber is finite with at most that many values, and its image on the
whole support is finite (`referencePalette_image_finite`).
-/

open MeasureTheory

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- `l_v(z_v/q) = β_v` at an admissible step `k` with active order `v = m k`. -/
theorem accuracy_at_reference_of_admissible {J : ℕ} {β : ℕ → ℝ} {q : ℕ} {A : Finset ℕ}
    {m z : ℕ → ℕ} {γ : ℝ}
    (hadm : Admissible J β (radius J β) (accuracy (radius J β)) q A m z γ)
    {k : ℕ} (hk : k ∈ A) :
    accuracy (radius J β) (m k) ((z (m k) : ℝ) / (q : ℝ)) = β (m k) := by
  obtain ⟨-, hm1, hmJ, -, hzk, -, hr⟩ := hadm.2 k hk
  exact accuracy_at_reference J β q k (m k) (z (m k)) hm1 hmJ hzk
    (fun x hx => (hr x hx).1)

/-- On the `F_z` fiber of `x`, the reference palette of order `v` lies in the
palette box of `x`, when the accuracy of order `v` at time `z/q` is `β v`. -/
theorem referencePalette_fiber_subset_box {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S)
    (hN : 0 < N) {v zv : ℕ} (hzq : zv ≤ q) (hvJ : v ≤ J)
    (hl : l v ((zv : ℝ) / (q : ℝ)) = β v)
    {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) :
    referencePalette q v zv β N h f₁ f₂ '' {y | y ∈ S ∧ F zv y = F zv x} ⊆
      ↑(paletteBox (N ^ (6 / (q : ℝ)))
        ⌊N ^ β v * iteratedDeriv v (f₁ x.1.1) (center h zv x.2)⌋
        ⌊N ^ β v * iteratedDeriv v (f₂ x.1.2) (center h zv x.2)⌋) := by
  rcases hrec with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hF, -, -⟩
  rintro _ ⟨y, ⟨hy, hxy⟩, rfl⟩
  exact reference_palette_mem_box J q zv v hzq hvJ N (β v) hN f₁ f₂ h
    (fun v t => ((Int.floor (t * (2 : ℝ) ^ h v) : ℝ) + 1 / 2) / (2 : ℝ) ^ h v) l hl F S hF
    hx hy hxy.symm

/-- The reference palette takes finitely many values on a reference fiber. -/
theorem referencePalette_fiber_finite {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S)
    (hN : 0 < N) {v zv : ℕ} (hzq : zv ≤ q) (hvJ : v ≤ J)
    (hl : l v ((zv : ℝ) / (q : ℝ)) = β v)
    {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) :
    (referencePalette q v zv β N h f₁ f₂ '' {y | y ∈ S ∧ F zv y = F zv x}).Finite :=
  (Finset.finite_toSet _).subset
    (referencePalette_fiber_subset_box hrec hN hzq hvJ hl hx)

/-- At most `(⌊N^(6/q)⌋₊ + 2)^2` reference palette values on a reference fiber. -/
theorem referencePalette_fiber_ncard_le {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S)
    (hN : 0 < N) {v zv : ℕ} (hzq : zv ≤ q) (hvJ : v ≤ J)
    (hl : l v ((zv : ℝ) / (q : ℝ)) = β v)
    {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) :
    (referencePalette q v zv β N h f₁ f₂ '' {y | y ∈ S ∧ F zv y = F zv x}).ncard ≤
      (⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 := by
  rw [← card_paletteBox (N ^ (6 / (q : ℝ)))
    ⌊N ^ β v * iteratedDeriv v (f₁ x.1.1) (center h zv x.2)⌋
    ⌊N ^ β v * iteratedDeriv v (f₂ x.1.2) (center h zv x.2)⌋, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (referencePalette_fiber_subset_box hrec hN hzq hvJ hl hx)
    (Finset.finite_toSet _)

/-- The reference palette takes finitely many values on the whole support:
the support is a finite union of reference fibers. -/
theorem referencePalette_image_finite {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S)
    (hN : 0 < N) {v zv : ℕ} (hzq : zv ≤ q) (hvJ : v ≤ J)
    (hl : l v ((zv : ℝ) / (q : ℝ)) = β v) :
    (referencePalette q v zv β N h f₁ f₂ '' S).Finite := by
  classical
  have hfinF : (F zv '' S).Finite := by
    rcases hrec with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmeas, -, -, -⟩
    exact (hmeas zv hzq).2
  refine (hfinF.biUnion (t := fun t =>
      referencePalette q v zv β N h f₁ f₂ '' {y | y ∈ S ∧ F zv y = t}) ?_).subset ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact referencePalette_fiber_finite hrec hN hzq hvJ hl hx
  · rintro _ ⟨y, hy, rfl⟩
    exact Set.mem_biUnion ⟨y, hy, rfl⟩ ⟨y, ⟨hy, rfl⟩, rfl⟩

end Submission.Obl.k4_matching_cofinal_palette_selection
