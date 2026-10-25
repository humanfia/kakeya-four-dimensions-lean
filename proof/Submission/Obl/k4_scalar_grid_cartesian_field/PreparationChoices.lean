import Submission.Obl.k4_scalar_grid_cartesian_field.SourceOracle
import Submission.Obl.k4_scalar_grid_cartesian_field.RefinementGrowth
import Submission.Obl.k4_scalar_grid_cartesian_field.AngularBreadth
import Submission.Obl.k4_scalar_grid_cartesian_field.PhysicalPalette
import Submission.Obl.k4_scalar_grid_cartesian_field.PreparationEnvelope

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter

/-- All global choices are made before the requested compact range and the individual packet. -/
structure PreparationChoices (data : Data) (H₀ : ℕ → ℝ)
    (E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence) where
  M : ℕ
  H : ℕ → ℝ
  B : ℝ
  G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ
  E : (k : ℕ) → Fin (data.W k) → Set Incidence
  ε : ℕ → ℝ
  L : ℕ → ℝ
  β : ℕ → ℝ
  Λ : ℕ → ℝ
  hM : 2 ≤ M
  hκM : 2 ≤ data.κ * (M : ℝ)
  hB : 50 ≤ B
  graph : graphData data E₀ 40 H B G E
  subpower_Λ : subpower data Λ
  positive_β : ∀ k, 0 < β k
  budget : ∀ k, PreparationBudgetBounds (data.K k) (L k) (H₀ k) (H k) (Λ k)
  qualification_budget : ∀ k, data.N k ^ ε k ≤ Λ k
  separation_budget : ∀ k, data.N k ^ β k ≤ Λ k
  geometry : ∀ k, 2 * data.K k ≤ L k ∧ 3000 * data.K k ^ 3 ≤ L k
  sources : ∀ᶠ k in atTop, Nonempty (SourcePacket data k M G E B (ε k) (L k) (H k))
  separation : ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (c : ℤ),
    ENNReal.ofReal (16 * sourcePaletteBudget (data.K k) (L k) (H₀ k) (H k)) *
      data.π k g (vel data k (β k) c) ≤ 1
  separation_cap : ∀ᶠ k in atTop, ∀ (g : Fin (data.W k)) (q : Fin 3 → ℤ) (c : ℤ),
    data.ρ k g {x | physCube (data.N k) B x = q ∧ x.1.2 1 ∈ vel data k (β k) c} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * data.π k g (vel data k (β k) c)

/-- Original qualification, cap and packet hypotheses supply the complete global choice record. -/
theorem exists_preparation_choices (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (hpacket : packetHyp data)
    (H₀ : ℕ → ℝ) (hH₀ : subpower data H₀)
    (E₀ : (k : ℕ) → Fin (data.W k) → Set Incidence) (hqual : qualOracle data E₀) :
    Nonempty (PreparationChoices data H₀ E₀) := by
  obtain ⟨M, H, B, G, E, ε, L, hM, hκM, hB, hgraph, hε, hεsub, hLsub, hgeom, hsource⟩ :=
    exists_source_packets data hs hb hcap hpacket E₀ hqual
  have hN : ∀ k, 1 ≤ data.N k := fun k => by linarith [hs.1 k]
  have hA := sourcePaletteBudget_subpower hN hs.2.1 hs.2.2.1 hLsub hH₀ hgraph.1
  let Q : ℝ → ℕ → Prop := fun b k => ∀ (g : Fin (data.W k)) (q : Fin 3 → ℤ) (c : ℤ),
    data.ρ k g {x | physCube (data.N k) B x = q ∧ x.1.2 1 ∈ vel data k b c} ≤
      ENNReal.ofReal (data.K k * (data.N k ^ (-B)) ^ (2 + data.d)) * data.π k g (vel data k b c)
  obtain ⟨β, hβ, _, hβsub, hsep⟩ := exists_original_angular_mesh data hs hcap
    (fun k => sourcePaletteBudget (data.K k) (L k) (H₀ k) (H k)) hA Q
    (fun b hb => original_physical_palette_fixed data hs hcap (by linarith : 1 ≤ B) hb)
  obtain ⟨Λ, hΛ, hbound⟩ := exists_preparation_envelope hN hs.2.1 hs.2.2.1 hH₀ hgraph.1 hLsub hεsub hβsub
  exact ⟨⟨M, H, B, G, E, ε, L, β, Λ, hM, hκM, hB, hgraph, hΛ, hβ,
    fun k => (hbound k).1, fun k => (hbound k).2.1, fun k => (hbound k).2.2,
    hgeom, hsource, hsep.mono (fun _ h => h.1), hsep.mono (fun _ h => h.2)⟩⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
