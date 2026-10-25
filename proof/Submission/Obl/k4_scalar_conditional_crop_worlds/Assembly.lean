import Submission.Obl.k4_scalar_conditional_crop_worlds.Selection
import Submission.Obl.k4_scalar_conditional_crop_worlds.Bounds
import Submission.Obl.k4_scalar_conditional_crop_worlds.Formats
import Submission.Obl.k4_scalar_conditional_crop_worlds.Mass

open MeasureTheory Set Filter Finset

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

abbrev conditionalPrior (N u : ℝ) (ν₀ : Measure Line) (q : Label) (p : ℝ) : Measure Line :=
  (ENNReal.ofReal p)⁻¹ • Measure.map (scalarCropLine N u q) (ν₀.restrict (scalarCell N u q))

abbrev conditionalEvent (N u : ℝ) (E₀ : Set State) (q : Label) : Set State :=
  scalarCropPoint N u q '' (E₀ ∩ (scalarCell N u q ×ˢ univ))

/-- The frozen conclusion, with the source prior and event named. -/
def CropConclusion (N : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set State) (u : ℝ) : Prop :=
  ∃ (ψ : ℕ → ℕ) (K' : ℕ → ℝ) (α : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set State) (p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Label) (ρ : ℕ → ℝ),
    StrictMono ψ ∧ Subpower (N ∘ ψ) K' ∧
    ScalarCrops (N ∘ ψ) K' (ν₀ ∘ ψ) (E₀ ∘ ψ) u α W ω ν E p z ρ ∧
    WorldFormat (N ∘ ψ) K' W ω ν E

/-- Assemble the scalar worlds from the finite one-crop format and exact lifting interfaces. -/
theorem construct_from_interfaces (N K : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set State)
    (u : ℝ) (B U : ℕ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hprob : ∀ k, IsProbabilityMeasure (ν₀ k))
    (hE : ∀ k, MeasurableSet (E₀ k) ∧ E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcoeff : ∀ k, ∀ᵐ l ∂ν₀ k, ∀ e, |l.2 e| ≤ K k + 1)
    (hB : ∀ k, K k + 1 ≤ N k ^ B)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ (ν₀ k).prod volume (E₀ k))
    (hLift : ∀ (ψ : ℕ → ℕ) (W : ℕ → ℕ) (z : (k : ℕ) → Fin (W k) → Label)
      (p : (k : ℕ) → Fin (W k) → ℝ),
      (∀ k, Function.Injective (z k)) →
      (∀ k γ, 0 < p k γ ∧ p k γ = priorMass (N (ψ k)) u (ν₀ (ψ k)) (z k γ)) →
      LiftFacts (N ∘ ψ) u W (ν₀ ∘ ψ) (E₀ ∘ ψ)
        (fun k γ => conditionalPrior (N (ψ k)) u (ν₀ (ψ k)) (z k γ) (p k γ))
        (fun k γ => conditionalEvent (N (ψ k)) u (E₀ (ψ k)) (z k γ)) p z)
    (hFormat : ∃ C D : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ k q p,
      p = priorMass (N k) u (ν₀ k) q → N k ^ (-((2 * (B + U + 3) : ℕ) : ℝ) - 1) ≤ p →
      WorldData (N k ^ C) D (K k + 1)
        (conditionalPrior (N k) u (ν₀ k) q p) (conditionalEvent (N k) u (E₀ k) q)) :
    CropConclusion N ν₀ E₀ u := by
  classical
  let A := 2 * (B + U + 3)
  have hbound : ∀ k, ∀ᵐ l ∂ν₀ k, ∀ e, |l.2 e| ≤ N k ^ B :=
    fun k => (hcoeff k).mono fun l hl e => (hl e).trans (hB k)
  obtain ⟨ψ, T, α, W, z, p, ω, ρ, hψ, hT, hcount, hz, hp, hρ, hρsub, hα, hTmass⟩ :=
    select_cells N K ν₀ E₀ u B U hN hNt hK huU hprob hbound (fun k => (hE k).2) hmass
  let ν : (k : ℕ) → Fin (W k) → Measure Line :=
    fun k γ => conditionalPrior (N (ψ k)) u (ν₀ (ψ k)) (z k γ) (p k γ)
  let E : (k : ℕ) → Fin (W k) → Set State :=
    fun k γ => conditionalEvent (N (ψ k)) u (E₀ (ψ k)) (z k γ)
  let K' : ℕ → ℝ := fun k => 8 * T k * K (ψ k)
  have hNpos : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hKψ : Subpower (N ∘ ψ) (K ∘ ψ) :=
    ⟨fun k => hK.1 (ψ k), fun ε hε => hψ.tendsto_atTop.eventually (hK.2 ε hε)⟩
  have hK' : Subpower (N ∘ ψ) K' :=
    subpower_eight_mul (hNt.comp hψ.tendsto_atTop) (fun k => hNpos (ψ k)) hT hKψ
  have hKT : ∀ k, T k ≤ K' k := by
    intro k
    dsimp [K']
    have hprod : T k ≤ T k * K (ψ k) :=
      le_mul_of_one_le_right (by linarith [hT.1 k]) (hK.1 (ψ k))
    nlinarith [hT.1 k, hK.1 (ψ k)]
  have hKK : ∀ k, K (ψ k) + 1 ≤ K' k := by
    intro k
    dsimp [K']
    have hprod : K (ψ k) ≤ T k * K (ψ k) :=
      le_mul_of_one_le_left (by linarith [hK.1 (ψ k)]) (hT.1 k)
    nlinarith [hK.1 (ψ k)]
  have hLf : LiftFacts (N ∘ ψ) u W (ν₀ ∘ ψ) (E₀ ∘ ψ) ν E p z :=
    hLift ψ W z p hz (fun k γ => ⟨(hp k γ).2.2, (hp k γ).1⟩)
  have hcenter : ∀ k γ,
      |N (ψ k) ^ (-u) * (z k γ 0 : ℝ)| + |N (ψ k) ^ (-u) * (z k γ 1 : ℝ)| ≤ K' k := by
    intro k γ
    have hcell : ν₀ (ψ k) (scalarCell (N (ψ k)) u (z k γ)) ≠ 0 := by
      intro heq
      have hpos := (hp k γ).2.2
      rw [(hp k γ).1] at hpos
      simp only [priorMass, heq, ENNReal.toReal_zero] at hpos
      exact (lt_irrefl 0 hpos)
    have hc := cell_center_bound (hNpos (ψ k)) (ν₀ (ψ k)) (hcoeff (ψ k)) (z k γ) hcell
    have ha1 : N (ψ k) ^ (-u) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hN (ψ k)]) (by linarith)
    have hprod : K (ψ k) ≤ T k * K (ψ k) :=
      le_mul_of_one_le_left (by linarith [hK.1 (ψ k)]) (hT.1 k)
    dsimp [K']
    nlinarith [hK.1 (ψ k)]
  obtain ⟨C, D, hC, hD, hF⟩ := hFormat
  let M := max C A
  have hM : 1 ≤ M := hC.trans (le_max_left _ _)
  have hworld : ∀ k γ, WorldData ((N ∘ ψ) k ^ (M : ℝ)) D (K' k) (ν k γ) (E k γ) := by
    intro k γ
    have h := hF (ψ k) (z k γ) (p k γ) (hp k γ).1 (hp k γ).2.1
    apply h.mono _ le_rfl (hKK k)
    simpa only [Function.comp_apply, Real.rpow_natCast] using
      pow_le_pow_right₀ (show (1 : ℝ) ≤ N (ψ k) by linarith [hN (ψ k)]) (le_max_left C A)
  have hweighted : ∀ k, ENNReal.ofReal ((K' k)⁻¹) ≤
      ∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ) univ := by
    intro k
    have hID : ∀ γ, ENNReal.ofReal (p k γ) * selected (ν k γ) (E k γ) univ =
        ENNReal.ofReal (activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) (z k γ)) := by
      intro γ
      have h := hLf.2.2.2.1 k γ univ MeasurableSet.univ
      simp only [Function.comp_apply] at h
      have hset : {a : State | a.1 ∈ scalarCell (N (ψ k)) u (z k γ) ∧
          (scalarCropLine (N (ψ k)) u (z k γ) a.1, a.2) ∈ (univ : Set State)} =
          scalarCell (N (ψ k)) u (z k γ) ×ˢ (univ : Set ℝ) := by ext a; simp
      rw [hset] at h
      haveI := hprob (ψ k)
      have hfin : (ν₀ (ψ k)).prod volume
          (E₀ (ψ k) ∩ (scalarCell (N (ψ k)) u (z k γ) ×ˢ univ)) ≠ ⊤ :=
        ((selected_le_cell (hE (ψ k)).2 _ _ _).trans_lt (measure_lt_top _ _)).ne
      simp only [selected] at h
      have hmeas : MeasurableSet (scalarCell (N (ψ k)) u (z k γ) ×ˢ (univ : Set ℝ)) :=
        (hLf.1 k γ).prod MeasurableSet.univ
      rw [Measure.restrict_apply hmeas, Set.inter_comm] at h
      simpa only [activeMass, ENNReal.ofReal_toReal hfin] using h
    exact (ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [hT.1 k]) (hKT k))).trans
      (weighted_mass_ge (p k) (fun γ => activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) (z k γ))
        (ω k) (fun γ => selected (ν k γ) (E k γ) univ) (fun γ => (hp k γ).2.2)
        (fun γ => ENNReal.toReal_nonneg) (hρ k).1 (hρ k).2.1 (hρ k).2.2.2 hID (hTmass k))
  refine ⟨ψ, K', α, W, ω, ν, E, p, z, ρ, hψ, hK', ?_, ?_⟩
  · exact ⟨fun k => ⟨hprob (ψ k), (hE (ψ k)).1, (hE (ψ k)).2⟩, hz,
      fun k γ => ⟨(hp k γ).2.2, (hp k γ).1, rfl, rfl, hcenter k γ⟩,
      hρ, hρsub, hα, hLf⟩
  · apply worldFormat_of_data (N ∘ ψ) K' W ω ν E M D hM hD _ _ _ hworld hweighted
    · intro k
      simpa only [Function.comp_apply, Real.rpow_natCast] using (hcount k).trans
        (pow_le_pow_right₀ (show (1 : ℝ) ≤ N (ψ k) by linarith [hN (ψ k)]) (le_max_right C A))
    · intro k γ
      rw [(hρ k).2.2.2 γ]
      exact div_nonneg (hp k γ).2.2.le (hρ k).1.le
    · intro k
      simp_rw [(hρ k).2.2.2]
      rw [← Finset.sum_div, (hρ k).2.2.1, div_self (hρ k).1.ne']

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
