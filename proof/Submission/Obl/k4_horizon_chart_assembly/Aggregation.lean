import Submission.Obl.k4_horizon_chart_assembly.ChartCore

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Disjoint groups in each world and block have one original probability budget
per world and block. No global number of native labels enters this bound. -/
theorem sum_original_group_budget {X I Γ J : Type*} [MeasurableSpace X]
    [Fintype I] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) [∀ g, IsProbabilityMeasure (ν g)]
    (γ : I → Γ) (j : I → J) (U : I → Set X)
    (hU : ∀ i, MeasurableSet (U i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (U i) (U i')) :
    ∑ i, (ν (γ i)).real (U i) ≤ (Fintype.card Γ : ℝ) * (Fintype.card J : ℝ) := by
  classical
  let g : I → Γ × J := fun i => (γ i, j i)
  have hf (c : Γ × J) :
      ∑ i ∈ Finset.univ.filter (fun i => g i = c), (ν (γ i)).real (U i) ≤ 1 := by
    let F := Finset.univ.filter (fun i => g i = c)
    have hd : (↑F : Set I).PairwiseDisjoint U := by
      intro i hi i' hi' hne
      have hc := (Finset.mem_filter.mp hi).2
      have hc' := (Finset.mem_filter.mp hi').2
      exact hdisj i i' hne (congrArg Prod.fst (hc.trans hc'.symm))
        (congrArg Prod.snd (hc.trans hc'.symm))
    calc
      _ = ∑ i ∈ F, (ν c.1).real (U i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hγ : γ i = c.1 := congrArg Prod.fst (Finset.mem_filter.mp hi).2
        rw [hγ]
      _ = (ν c.1).real (⋃ i ∈ F, U i) :=
        (measureReal_biUnion_finset hd (fun i _ => hU i)).symm
      _ ≤ 1 := measureReal_le_one
  calc
    _ = ∑ c : Γ × J,
        ∑ i ∈ Finset.univ.filter (fun i => g i = c), (ν (γ i)).real (U i) :=
      (Finset.sum_fiberwise Finset.univ g (fun i => (ν (γ i)).real (U i))).symm
    _ ≤ ∑ c : Γ × J, (1 : ℝ) := Finset.sum_le_sum (fun c _ => hf c)
    _ = _ := by simp [Fintype.card_prod]

/-- Original-prior count bounds sum over the full finite packet type. -/
theorem sigma_packet_count_bound {X I Γ J : Type*} [MeasurableSpace X]
    [Fintype I] [Fintype Γ] [Fintype J]
    (ν : Γ → Measure X) [∀ g, IsProbabilityMeasure (ν g)]
    (γ : I → Γ) (j : I → J) (U : I → Set X) (m : I → ℕ)
    (hU : ∀ i, MeasurableSet (U i))
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (U i) (U i'))
    {A : ℝ} (hA : 0 ≤ A) (hm : ∀ i, (m i : ℝ) ≤ A * (ν (γ i)).real (U i)) :
    (Fintype.card (Σ i : I, Fin (m i)) : ℝ) ≤
      A * ((Fintype.card Γ : ℝ) * (Fintype.card J : ℝ)) := by
  classical
  simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  calc
    _ ≤ ∑ i, A * (ν (γ i)).real (U i) := Finset.sum_le_sum (fun i _ => hm i)
    _ = A * ∑ i, (ν (γ i)).real (U i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_original_group_budget ν γ j U hU hdisj) hA

/-- First-fit disjointness within a group and label disjointness between groups
combine on the dependent finite packet type. -/
theorem sigma_packet_disjoint {X I Γ J : Type*} (γ : I → Γ) (j : I → J)
    (U : I → Set X) (m : I → ℕ) (A : (i : I) → Fin (m i) → Set X)
    (hgroups : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (U i) (U i'))
    (hsub : ∀ i b, A i b ⊆ U i) (hinside : ∀ i, Pairwise (fun b b' => Disjoint (A i b) (A i b'))) :
    ∀ a b : (Σ i : I, Fin (m i)), a ≠ b → γ a.1 = γ b.1 → j a.1 = j b.1 →
      Disjoint (A a.1 a.2) (A b.1 b.2) := by
  rintro ⟨i, a⟩ ⟨i', b⟩ hne hγ hj
  by_cases hi : i = i'
  · subst i'
    have hab : a ≠ b := by intro h; apply hne; cases h; rfl
    exact hinside i hab
  · exact (hgroups i i' hi hγ hj).mono (hsub i a) (hsub i' b)

/-- Reindex a quantitative atlas on any finite type by the literal `Fin C'`
family of the frozen conclusions. -/
theorem reindex_budget_charts {I : Type*} [Fintype I]
    (W T D : ℕ) (H κ a n0 : ℝ) (lower : ENNReal)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence)
    (B : Fin W → ℝ) (γ : I → Fin W) (j : I → Fin (2 ^ T))
    (c u : I → Plane) (Q : I → Matrix (Fin 2) (Fin 2) ℝ)
    (R : I → MvPolynomial (Fin 4) ℝ) (A : I → Set Trajectory) (F : I → Set Incidence)
    (hcount : (Fintype.card I : ℝ) ≤ H)
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hchart : ∀ b, RawChart H D κ T ((j b : ℕ) : ℝ) a (B (γ b)) (E (γ b))
      (c b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (n0 * |(Q b).det| / ((2 : ℝ) ^ T * κ)) ≤
        ((ν (γ b)).prod volume) (F b)))
    (hmass : lower ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)) :
    ∃ C : ℕ, ∃ (γ' : Fin C → Fin W) (j' : Fin C → Fin (2 ^ T))
      (c' u' : Fin C → Plane) (Q' : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R' : Fin C → MvPolynomial (Fin 4) ℝ) (A' : Fin C → Set Trajectory) (F' : Fin C → Set Incidence),
      (C : ℝ) ≤ H ∧
      (∀ b b', b ≠ b' → γ' b = γ' b' → j' b = j' b' → Disjoint (A' b) (A' b')) ∧
      (∀ b, RawChart H D κ T ((j' b : ℕ) : ℝ) a (B (γ' b)) (E (γ' b))
        (c' b) (u' b) (Q' b) (R' b) (A' b) (F' b)
        (ENNReal.ofReal (n0 * |(Q' b).det| / ((2 : ℝ) ^ T * κ)) ≤
          ((ν (γ' b)).prod volume) (F' b))) ∧
      lower ≤ ∑ b, ENNReal.ofReal (ω (γ' b)) * ((ν (γ' b)).prod volume) (F' b) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, γ ∘ e, j ∘ e, c ∘ e, u ∘ e, Q ∘ e, R ∘ e, A ∘ e, F ∘ e,
    hcount, ?_, fun b => hchart (e b), ?_⟩
  · intro b b' hne hγ hj
    exact hdisj (e b) (e b') (fun h => hne (e.injective h)) hγ hj
  · exact hmass.trans_eq (Equiv.sum_comp e (fun b : I =>
      ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b))).symm

end
end Submission.Obl.k4_horizon_chart_assembly
