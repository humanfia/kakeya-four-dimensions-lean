-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PhysicalBroadnessBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PhysicalBroadnessBudget.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/PhysicalBroadnessBudget.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RenormScalars
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinementBroadness
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketCore

set_option autoImplicit false
noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)

/-- A uniform bound for the ratio of the physical prism scale to the
packet scale makes the broadness transfer cost only a fixed constant. -/
theorem physical_packet_broadness_budget {β h₀ h' B C₀ K : ℝ}
    (hβ : 0 ≤ β) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hgap : h₀ < h') :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ δ h θ ρ' : ℝ, 0 < δ → δ ≤ d₀ → h ≤ h₀ →
        0 < θ → 0 ≤ ρ' → ρ' ≤ K*θ →
        2*δ^(-h)*B*(5*(C₀+21))^β*(ρ'/θ)^β ≤ δ^(-h') := by
  let D := 2*B*(5*(C₀+21))^β*K^β
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨d₀, hd₀, hd₀1, hsmall⟩ :=
    const_absorption (C := D) hD (show -h' < -h₀ by linarith)
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ h θ ρ' hδ hδd hh hθ hρ' hratio
  have hδ1 : δ ≤ 1 := hδd.trans hd₀1
  have hpow : δ^(-h) ≤ δ^(-h₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hscale : (ρ'/θ)^β ≤ K^β :=
    Real.rpow_le_rpow (div_nonneg hρ' hθ.le) ((div_le_iff₀ hθ).mpr hratio) hβ
  calc
    _ ≤ 2*δ^(-h₀)*B*(5*(C₀+21))^β*K^β := by gcongr
    _ = D*δ^(-h₀) := by dsimp [D]; ring
    _ ≤ _ := hsmall δ hδ hδd

/-- The middle-width bound for the clipped inverse survives the factor
128 window enlargement and a further factor two in width rounding. -/
theorem rounded_clipped_packet_scale {B b' c θ : ℝ}
    (hc : 0 < c) (hB : B ≤ 83886080*θ*c) (hb' : b' ≤ 256*B) :
    b'/c ≤ 21474836480*θ := by
  apply (div_le_iff₀ hc).mpr
  have hh := mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 256)
  nlinarith only [hh, hb']

/-- The actual clipped packet constants pay the broadness budget of the
variable-width incidence assembly, including its width-rounding factor. -/
theorem clipped_window_broadness_budget {β h₀ h' : ℝ}
    (hβ : 0 ≤ β) (hgap : h₀ < h') :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ δ h θ c B b' : ℝ, 0 < δ → δ ≤ d₀ → h ≤ h₀ →
        0 < θ → 0 < c → 0 ≤ b' →
        B ≤ 83886080*θ*c → b' ≤ 128*B →
        2*δ^(-h)*8*(5*(2+21))^β*(2*b'/(c*θ))^β ≤ δ^(-h') := by
  obtain ⟨d₀, hd₀, hd₀1, hbudget⟩ :=
    physical_packet_broadness_budget hβ (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 21474836480) hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ h θ c B b' hδ hδd hh hθ hc hb' hB hwindow
  have hratio : (2*b')/c ≤ 21474836480*θ :=
    rounded_clipped_packet_scale hc hB (by linarith)
  simpa only [div_div] using
    hbudget δ h θ (2*b'/c) hδ hδd hh hθ (by positivity) hratio

/-- A bounded physical-to-packet scale ratio yields the fine broadness
clause below a cutoff chosen before the family and packet are known. -/
theorem physical_grain_broadness_uniform {ω ζ h₀ h' B C₀ K : ℝ}
    (hβ : 0 ≤ ω*ζ/100) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hgap : h₀ < h') :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ {δ h ρ ρ' θ a c b g m : ℝ} {n N L : ℕ}
        {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
        {y w : Fin N → V} {f : Fin n → Fin N}
        {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
        {Hs W : Fin L → Set V} {γ : Fin L → Fin N} {ν : Fin L → V},
      0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ h₀ → δ ≤ ρ →
      0 < θ → 0 < ρ' → ρ' ≤ K*θ → 0 ≤ m →
      (∀ i, ‖v i‖ = 1) →
      C δ h n x v Y S Z ρ N y w f True →
      Broad ω ζ δ h ρ n N v S Z f →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m →
      (∀ j, W j ⊆ Hs j) →
      ∀ R : V ≃ₗᵢ[ℝ] V,
        (∀ j, (W j).Nonempty → pd (ν j) (R (boxAxis (e j) 2)) ≤ C₀*ρ) →
        (∀ p u r, ‖u‖ = 1 → 2*ρ ≤ r →
          q L {j | p ∈ W j ∧ pd (ν j) u ≤ r} ≤
            B*(r/θ)^(ω*ζ/100)*q L {j | p ∈ W j}) →
        ∀ p u r, ‖u‖ = 1 → δ ≤ r →
          q n {i | p ∈ grainFineRefinement S Z f W γ i ∧ pd (v i) u ≤ r} ≤
            δ^(-h')*(r/ρ')^(ω*ζ/100)*
              q n {i | p ∈ grainFineRefinement S Z f W γ i} := by
  obtain ⟨d₀, hd₀, hd₀1, hbudget⟩ :=
    physical_packet_broadness_budget hβ hB hC₀ hK hgap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ h ρ ρ' θ a c b g m n N L x v Y Z S y w f z e Hs W γ ν
    hδ hδd hh hh₀ hδρ hθ hρ' hratio hm hv hC hbr hHB hW R hclose haxis p u r hu hr
  have hbudget' := hbudget δ h θ ρ' hδ hδd hh₀ hθ hρ'.le hratio
  have H := grain_refinement_fine_broad_in_frame R hδ (hδd.trans hd₀1) hh hδρ
    hθ hβ hB hm hC₀ hv hC hbr hHB hW hclose haxis p u r hu hr
  exact WangZahlLot.Obl.wz_move_two_dense_broad_prisms.broad_scale_change
    (hδ.trans_le hr) hθ hρ' hbudget' H

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
