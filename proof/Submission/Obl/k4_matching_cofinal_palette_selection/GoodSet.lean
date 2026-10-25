import Submission.Obl.k4_matching_cofinal_palette_selection.Continuous
import Submission.Obl.k4_matching_cofinal_palette_selection.PaletteFiber
import Submission.Obl.k4_matching_cofinal_palette_selection.Arith
import Submission.Obl.k4_matching_cofinal_palette_selection.RecordMeasurability

/-!
# The good set of one record tuple (o069)

For one record tuple at scale `N` (large enough for the count of
`bad_count_arith`), the steps of `A` whose reference palette is good form a
set `G` with `|A \ G| ≤ δ q`: the bad steps of each active order `v ∈ [1, J]`
are counted by the shifted finite palette bound (`continuous_pair_bad_steps_bound`)
with the palette count of `PaletteFiber.lean`, and the counts are summed by
`bad_count_arith`.
-/

open MeasureTheory

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- The reference palette is measurable (its arguments take countably many values). -/
theorem referencePalette_measurable {n₁ n₂ : ℕ} (q v zv : ℕ) (β : ℕ → ℝ) (N : ℝ)
    (h : ℕ → ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) :
    Measurable (referencePalette q v zv β N h f₁ f₂) :=
  measurable_two_arm_jet_bins n₁ n₂ (h zv) v f₁ f₂ (N ^ (β v + 6 / (q : ℝ)))

/-- The records are nested on the support up to level `q`. -/
theorem records_nested_on_support {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {q : ℕ} {u : ℕ → ℝ} {ε N : ℝ}
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β r l q u ε N n₁ n₂ f₁ f₂ π₁ π₂ μ h F S) :
    ∀ a b, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S, F b x = F b y → F a x = F a y := by
  rcases hrec with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hF, -, -⟩
  intro a b hab hbq x hx y hy hxy
  exact (hF a (hab.trans hbq) x hx y hy).2
    (fun v hv => (hF b hbq x hx y hy).1 hxy v (hv.trans hab))

/-- The good set of one record tuple: all but `δ q` steps of `A` have a good
reference palette. -/
theorem exists_good_set (hpal : PaletteEstimate)
    {J : ℕ} {d : ℝ} {β : ℕ → ℝ} {q : ℕ} (hq : 1 ≤ q)
    {A : Finset ℕ} {m z : ℕ → ℕ} {γ : ℝ}
    (hadm : Admissible J β (radius J β) (accuracy (radius J β)) q A m z γ)
    {u : ℕ → ℝ} {ε N δ : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ)
    (hcount : ∀ L : ℕ, L ≤ q → ∀ b : ℕ → ℕ,
      (∀ v : ℕ, 1 ≤ v → v ≤ J →
        (b v : ℝ) * (δ / (4 * ((J : ℝ) + 1) * (q : ℝ)) * Real.log N *
          (1 / (2 : ℝ) ^ (J + 10))) ≤
        ((6 * (J + 1) : ℕ) : ℝ) * Real.log (((⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 : ℕ) : ℝ) +
          (L : ℝ)) →
      (∑ v ∈ Finset.Icc 1 J, (b v : ℝ)) ≤ δ * (q : ℝ))
    {n₁ n₂ : ℕ} {f₁ : Fin n₁ → ℝ → ℝ} {f₂ : Fin n₂ → ℝ → ℝ}
    {π₁ : Fin n₁ → ℝ} {π₂ : Fin n₂ → ℝ}
    {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {h : ℕ → ℕ}
    {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (hrec : Records J d β (radius J β) (accuracy (radius J β)) q u ε N
      n₁ n₂ f₁ f₂ π₁ π₂ μ h F S) :
    ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
      ∀ k ∈ G, PaletteGood J q (m k) (z (m k)) k β N (δ / (4 * ((J : ℝ) + 1) * (q : ℝ)))
        f₁ f₂ μ h F S := by
  classical
  set θ : ℝ := δ / (4 * ((J : ℝ) + 1) * (q : ℝ)) with hθ
  set α : ℝ := 1 / (2 : ℝ) ^ (J + 10) with hα
  set M : ℕ := (⌊N ^ (6 / (q : ℝ))⌋₊ + 2) ^ 2 with hMdef
  have hrec' := hrec
  rcases hrec' with ⟨-, -, -, -, -, -, -, -, -, -, hprob, -, -, hS, hμS, -, -, -, hmeas, -, -, -⟩
  have := hprob
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ0 : 0 ≤ θ := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  let G := A.filter (fun k => PaletteGood J q (m k) (z (m k)) k β N θ f₁ f₂ μ h F S)
  refine ⟨G, Finset.filter_subset _ _, ?_, fun k hk => (Finset.mem_filter.mp hk).2⟩
  -- the bad steps of each active order
  let Av : ℕ → Finset ℕ := fun v => A.filter (fun k => m k = v)
  let bad : ℕ → Finset ℕ := fun v => (Av v).filter (fun k => ENNReal.ofReal α <
    badMass μ S F (referencePalette q v (z v) β N h f₁ f₂) (6 * (J + 1)) k (N ^ θ))
  have hsub : A \ G ⊆ (Finset.Icc 1 J).biUnion bad := by
    intro k hk
    obtain ⟨hkA, hkG⟩ := Finset.mem_sdiff.mp hk
    have hnot : ¬ PaletteGood J q (m k) (z (m k)) k β N θ f₁ f₂ μ h F S :=
      fun hg => hkG (Finset.mem_filter.mpr ⟨hkA, hg⟩)
    obtain ⟨-, hm1, hmJ, -⟩ := hadm.2 k hkA
    refine Finset.mem_biUnion.mpr ⟨m k, Finset.mem_Icc.mpr ⟨hm1, hmJ⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hkA, rfl⟩, not_le.mp hnot⟩
  have hbad : ∀ v : ℕ, 1 ≤ v → v ≤ J → ((bad v).card : ℝ) * (θ * Real.log N * α) ≤
      ((6 * (J + 1) : ℕ) : ℝ) * Real.log (M : ℝ) + (q : ℝ) := by
    intro v hv1 hvJ
    by_cases hne : (Av v).Nonempty
    · obtain ⟨k₀, hk₀⟩ := hne
      obtain ⟨hk₀A, hmk₀⟩ := Finset.mem_filter.mp hk₀
      obtain ⟨hk₀C, -, -, -, hzk₀, -⟩ := hadm.2 k₀ hk₀A
      rw [hmk₀] at hzk₀
      have hzq : z v ≤ q := by omega
      have hl : accuracy (radius J β) v ((z v : ℝ) / (q : ℝ)) = β v := by
        have := accuracy_at_reference_of_admissible hadm hk₀A
        rwa [hmk₀] at this
      have hN0 : 0 < N := by linarith
      refine continuous_pair_bad_steps_bound hpal μ S hS hμS F
        (referencePalette q v (z v) β N h f₁ f₂) q (z v) (6 * (J + 1)) M hzq (by omega) hM1
        (fun k hk => (hmeas k hk).1) (fun k hk => (hmeas k hk).2)
        (records_nested_on_support hrec)
        (referencePalette_measurable q v (z v) β N h f₁ f₂)
        (fun x hx => ⟨referencePalette_fiber_finite hrec hN0 hzq hvJ hl hx,
          referencePalette_fiber_ncard_le hrec hN0 hzq hvJ hl hx⟩)
        (Av v) ?_ N θ α hN hθ0 hα0
      intro k hk
      obtain ⟨hkA, hmk⟩ := Finset.mem_filter.mp hk
      obtain ⟨hkC, -, -, -, hzk, -⟩ := hadm.2 k hkA
      rw [hmk] at hzk
      exact ⟨Finset.mem_range.mp (hadm.1 hkA), hzk, hkC⟩
    · have hempty : bad v = ∅ := by
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        simp only [bad, hne, Finset.filter_empty]
      rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
      have : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
      positivity
  have hsum := hcount q le_rfl (fun v => (bad v).card) hbad
  have hcard : ((A \ G).card : ℝ) ≤ ∑ v ∈ Finset.Icc 1 J, ((bad v).card : ℝ) := by
    have := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast this
  rw [div_le_iff₀ hqpos]
  linarith

end Submission.Obl.k4_matching_cofinal_palette_selection
