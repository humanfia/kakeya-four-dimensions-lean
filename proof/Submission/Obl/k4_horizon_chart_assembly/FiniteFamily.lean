import Submission.Obl.k4_horizon_chart_assembly.Aggregation

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Literal finite quantitative atlas data, before the asymptotic choice of powers. -/
def BudgetAtlas (W T D : ℕ) (H κ a n0 : ℝ) (lower : ENNReal)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (E : Fin W → Set Incidence) (B : Fin W → ℝ) : Prop :=
  ∃ C : ℕ, ∃ (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (c u : Fin C → Plane) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence),
    (C : ℝ) ≤ H ∧
    (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
    (∀ b, RawChart H D κ T ((j b : ℕ) : ℝ) a (B (γ b)) (E (γ b))
      (c b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (n0 * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ b)).prod volume) (F b))) ∧
    lower ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)

/-- Assemble already constructed per-group charts into the literal finite family.
All counts use the original group prior, while the selected mass is arbitrary. -/
theorem aggregate_budget_charts {I : Type*} [Fintype I]
    (W T D : ℕ) (Hgroup Hout κ a n0 : ℝ) (lower : ENNReal)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) [∀ g, IsProbabilityMeasure (ν g)]
    (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (γ : I → Fin W) (j : I → Fin (2 ^ T)) (U : I → Set Trajectory) (m : I → ℕ)
    (c u : (g : I) → Fin (m g) → Plane)
    (Q : (g : I) → Fin (m g) → Matrix (Fin 2) (Fin 2) ℝ)
    (R : (g : I) → Fin (m g) → MvPolynomial (Fin 4) ℝ)
    (A : (g : I) → Fin (m g) → Set Trajectory)
    (F : (g : I) → Fin (m g) → Set Incidence)
    (hU : ∀ g, MeasurableSet (U g))
    (hgroups : ∀ g g', g ≠ g' → γ g = γ g' → j g = j g' → Disjoint (U g) (U g'))
    (hsub : ∀ g b, A g b ⊆ U g)
    (hinside : ∀ g, Pairwise (fun b b' => Disjoint (A g b) (A g b')))
    {Ccount : ℝ} (hC : 0 ≤ Ccount)
    (hcount : ∀ g, (m g : ℝ) ≤ Ccount * (ν (γ g)).real (U g))
    (hbudget : Ccount * (W : ℝ) * (2 : ℝ) ^ T ≤ Hout)
    (hsize : Hgroup ≤ Hout)
    (hchart : ∀ g b, RawChart Hgroup D κ T ((j g : ℕ) : ℝ) a (B (γ g)) (E (γ g))
      (c g b) (u g b) (Q g b) (R g b) (A g b) (F g b)
      (ENNReal.ofReal (n0 * |(Q g b).det| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ g)).prod volume) (F g b)))
    (hmass : lower ≤ ∑ g, ∑ b, ENNReal.ofReal (ω (γ g)) * ((ν (γ g)).prod volume) (F g b)) :
    BudgetAtlas W T D Hout κ a n0 lower ω ν E B := by
  classical
  have htotal : (Fintype.card (Σ g : I, Fin (m g)) : ℝ) ≤ Hout := by
    have h := sigma_packet_count_bound ν γ j U m hU hgroups hC hcount
    have h' : (Fintype.card (Σ g : I, Fin (m g)) : ℝ) ≤ Ccount * (W : ℝ) * (2 : ℝ) ^ T := by
      simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h
    exact h'.trans hbudget
  have hdisj := sigma_packet_disjoint γ j U m A hgroups hsub hinside
  apply reindex_budget_charts (I := Σ g : I, Fin (m g)) W T D Hout κ a n0 lower ω ν E B
    (fun b => γ b.1) (fun b => j b.1) (fun b => c b.1 b.2) (fun b => u b.1 b.2)
    (fun b => Q b.1 b.2) (fun b => R b.1 b.2) (fun b => A b.1 b.2) (fun b => F b.1 b.2)
    htotal hdisj
  · rintro ⟨g, b⟩
    exact rawChart_mono hsize le_rfl (hchart g b) id
  · simpa only [Fintype.sum_sigma] using hmass

abbrev NativeGroupIndex (W T : ℕ) (S : Finset ((Fin 2 → ℤ) × ℤ)) :=
  Fin W × Fin (2 ^ T) × ↥S

def nativeGroupAt {W T : ℕ} {S : Finset ((Fin 2 → ℤ) × ℤ)}
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (K H q a : ℝ) (mid : Fin (2 ^ T) → ℝ) (g : NativeGroupIndex W T S) : Set Trajectory :=
  nativeGroup (P g.1) (B g.1) K H (mid g.2.1) q a g.2.2.val

/-- The native midpoint groups are disjoint within their world and time block,
for any finite universe of labels. -/
theorem native_groups_fiber_disjoint {W T : ℕ} (S : Finset ((Fin 2 → ℤ) × ℤ))
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (K H q a : ℝ) (mid : Fin (2 ^ T) → ℝ) :
    ∀ g g' : NativeGroupIndex W T S, g ≠ g' → g.1 = g'.1 → g.2.1 = g'.2.1 →
      Disjoint (nativeGroupAt P B K H q a mid g) (nativeGroupAt P B K H q a mid g') := by
  rintro ⟨γ, j, Γ⟩ ⟨γ', j', Γ'⟩ hne hγ hj
  dsimp at hγ hj
  subst γ'
  subst j'
  have hΓ : Γ.val ≠ Γ'.val := by
    intro he
    apply hne
    exact congrArg (fun Λ : ↥S => (γ, j, Λ)) (Subtype.ext he)
  exact nativeGroup_disjoint (P γ) (B γ) K H (mid j) q a hΓ

end
end Submission.Obl.k4_horizon_chart_assembly
