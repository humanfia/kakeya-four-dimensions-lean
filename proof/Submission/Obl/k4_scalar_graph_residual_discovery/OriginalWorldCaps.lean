/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalWorldCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRawSpatialCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldOriginalCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace ScalarData

/-- The literal prepared prior and finite original mesh pieces construct
the complete cap certificate used by the world builder. Only pointwise
original positive entries and prior-intersection floors are required. -/
theorem prepData.original_world_caps {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop, ∀ (g : Fin (D.W k)) (a : ℝ),
      T⁻¹ ≤ a → a ≤ T → (∃ m : ℕ, a = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      ∀ (R : Set ScalarIncidence), R ⊆ E₀ k g →
      ∀ ζ A η : ℝ, 0 < ζ → ζ ≤ 1 → 1 ≤ A → 0 < η →
      ∀ f : ℝ → ℝ,
      (∀ r, ζ ≤ r → r ≤ 1 → T⁻¹ ≤ f r ∧ f r ≤ T ∧
        ∃ m : ℕ, f r = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      (∀ r, ζ ≤ r → r ≤ 1 → D.N k ^ (-f r) ≤ D.N k ^ (-a) * r ∧
        D.N k ^ (-a) * r ≤ A * D.N k ^ (-f r)) →
      (∀ r, ζ ≤ r → r ≤ 1 → ∀ p ∈ R,
        (D.ρ k g).restrict (E₀ k g)
          {p' | cell (D.N k ^ (-f r)) p'.1.2 = cell (D.N k ^ (-f r)) p.1.2} ≠ 0) →
      (∀ r, ζ ≤ r → r ≤ 1 → ∀ p ∈ R,
        ENNReal.ofReal η * θ k g {l | cell (D.N k ^ (-f r)) l.2 = cell (D.N k ^ (-f r)) p.1.2} ≤
          θ k g {l | cell (D.N k ^ (-a)) l.2 = cell (D.N k ^ (-a)) p.1.2 ∧
            cell (D.N k ^ (-f r)) l.2 = cell (D.N k ^ (-f r)) p.1.2}) →
      ∀ q : Fin 5 → ℤ,
      (D.ρ k g).restrict (E₀ k g) {p | cell (D.N k ^ (-a)) p.1.2 = q} ≠ 0 →
      ∃ caps : Zoom.OriginalWorldCaps (θ k g) R (D.N k ^ (-a)) ζ D.d q,
        caps.H = H k ∧ caps.A = A ∧ caps.η = η ∧ caps.β = (fun r => D.N k ^ (-f r)) := by
  intro T hT
  filter_upwards [hprep.original_raw_spatial_caps hN T hT] with k hk
  intro g a halo hahi hamesh R hRE ζ A η hζ hζ₁ hA hη f hf hwidth hpositive hinter q hq
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hH : 0 < H k := by linarith [hprep.1.1 k]
  have hcoarse := hk g a a halo hahi halo hahi hamesh hamesh
  have hcoarsefloor := (hcoarse.1 q hq).1
  have hfine (r : ℝ) (hr : ζ ≤ r) (hr₁ : r ≤ 1) :=
    hk g (f r) (f r) (hf r hr hr₁).1 (hf r hr hr₁).2.1
      (hf r hr hr₁).1 (hf r hr hr₁).2.1 (hf r hr hr₁).2.2 (hf r hr hr₁).2.2
  refine ⟨{
    H := H k
    A := A
    η := η
    H_pos := hH
    one_le_A := hA
    eta_pos := hη
    β := fun r => D.N k ^ (-f r)
    beta_bounds := fun r hr hr₁ => ⟨Real.rpow_pos_of_pos hN₀ _, hwidth r hr hr₁⟩
    π₀ := D.π k g (scalarVelocityBin (D.N k ^ (-a)) (q 1))
    coarse_floor := hcoarsefloor
    coarse_cap := ?_
    π := fun r b => D.π k g (scalarVelocityBin (D.N k ^ (-f r)) (b 1))
    fine_floor := ?_
    intersection_floor := ?_
    fine_cap := ?_
  }, rfl, rfl, rfl, rfl⟩
  · intro t r hr hr₁ z
    exact (hk g a (f r) halo hahi (hf r hr hr₁).1 (hf r hr hr₁).2.1
      hamesh (hf r hr hr₁).2.2).2 R hRE t q z
  · intro r hr hr₁ b hactive
    obtain ⟨p, hp, _, hbin⟩ := hactive
    have hpos := hpositive r hr hr₁ p hp
    rw [hbin] at hpos
    exact ((hfine r hr hr₁).1 b hpos).1
  · intro r hr hr₁ b hactive
    obtain ⟨p, hp, hcoarse, hbin⟩ := hactive
    have hh := hinter r hr hr₁ p hp
    rw [hcoarse, hbin] at hh
    have heq : {l : ScalarLine | cell (D.N k ^ (-a)) l.2 = q ∧ cell (D.N k ^ (-f r)) l.2 = b} =
        {l | cell (D.N k ^ (-f r)) l.2 = b ∧ cell (D.N k ^ (-a)) l.2 = q} := by
      ext l
      exact and_comm
    exact hh.trans_eq (congrArg (θ k g) heq)
  · intro r hr hr₁ b _ t s hs hsr z
    have hs₁ : s ≤ 1 := hsr.trans hr₁
    exact (hk g (f r) (f s) (hf r hr hr₁).1 (hf r hr hr₁).2.1
      (hf s hs hs₁).1 (hf s hs hs₁).2.1 (hf r hr hr₁).2.2 (hf s hs hs₁).2.2).2 R hRE t b z

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
