/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldNormal.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Jets.Interface
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldDensity
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomIncidenceCaps
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomScalar
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualZoom

set_option autoImplicit false

/-! The coefficient-world estimates use the original trajectory labels and the
full original coefficient-bin prior. This file converts those estimates to the
scalar-normal interface of x0801's `Jets/Interface.lean`; no pushforward or new
conditioning of the retained incidences is needed. -/

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice
open WangZahlLot.Obl.wz_slab_local_linearity

namespace Zoom

theorem jets_x (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) :
    Jets.zx (coeff ρ q l) t = x ρ q l t := by
  dsimp only [Jets.zx, x]
  ring

theorem jets_y (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) :
    Jets.zy (coeff ρ q l) t = y ρ q l t := by
  dsimp only [Jets.zy, y]
  ring

theorem jets_scalar (ρ : ℝ) (q : Fin 5 → ℤ) (F : ℝ → ℝ)
    (l : ScalarLine) (t : ℝ) :
    Jets.zS F (coeff ρ q l) t = scalar ρ q F l t := by
  simp only [Jets.zS, jets_x, jets_y, scalar]

theorem jets_residual (ρ : ℝ) (q : Fin 5 → ℤ) (F : ℝ → ℝ)
    (l : ScalarLine) (t : ℝ) :
    Jets.zR F (coeff ρ q l) t = residual ρ q F l t := by
  dsimp only [Jets.zR, residual]
  ring

/-- The jet interface orders the spatial coordinates as `(x,y)` whereas
the original physical bookkeeping uses `(y,x)`. Their supremum distances
are equal, so the residual comparison loses no geometric factor. -/
theorem jets_position_distance (ρ : ℝ) (q : Fin 5 → ℤ)
    (p p' : ScalarIncidence) :
    ‖Jets.zpos (coeff ρ q p.1) p.2 - Jets.zpos (coeff ρ q p'.1) p'.2‖ =
      ‖position ρ q p - position ρ q p'‖ := by
  simp only [Jets.zpos, jets_x, jets_y]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro e
    fin_cases e
    · simpa [position] using
        norm_le_pi_norm (position ρ q p - position ρ q p') (0 : Fin 3)
    · simpa [position] using
        norm_le_pi_norm (position ρ q p - position ρ q p') (2 : Fin 3)
    · simpa [position] using
        norm_le_pi_norm (position ρ q p - position ρ q p') (1 : Fin 3)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro e
    fin_cases e
    · simpa [position] using
        norm_le_pi_norm
          ((![p.2, x ρ q p.1 p.2, y ρ q p.1 p.2] : Fin 3 → ℝ) -
            ![p'.2, x ρ q p'.1 p'.2, y ρ q p'.1 p'.2]) (0 : Fin 3)
    · simpa [position] using
        norm_le_pi_norm
          ((![p.2, x ρ q p.1 p.2, y ρ q p.1 p.2] : Fin 3 → ℝ) -
            ![p'.2, x ρ q p'.1 p'.2, y ρ q p'.1 p'.2]) (2 : Fin 3)
    · simpa [position] using
        norm_le_pi_norm
          ((![p.2, x ρ q p.1 p.2, y ρ q p.1 p.2] : Fin 3 → ℝ) -
            ![p'.2, x ρ q p'.1 p'.2, y ρ q p'.1 p'.2]) (1 : Fin 3)

/-- Original coefficient-world estimates give the complete higher-jet input.
The probability law is the full coefficient-bin prior, fixed before later
incidence restrictions. The density assumption still uses the original
unnormalized incidence measure and its original prior reference. -/
theorem scalarNormal_of_world_estimates
    (θ : Measure ScalarLine) [IsFiniteMeasure θ] (μ : Measure ScalarIncidence)
    {ρ ζ d K H δ : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1)
    (hK : 1 ≤ K) (hH : 0 < H) (hδ : 0 < δ) (hbudget : H / δ ≤ K)
    (hμ : μ ≤ ENNReal.ofReal H • θ.prod volume)
    (q : Fin 5 → ℤ) (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    (E : Set ScalarIncidence) (hE : MeasurableSet E)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ E)
    (F : ℝ → ℝ) (hF : Measurable F) (hbound : ∀ p ∈ E, |F p.2| ≤ K)
    (β : ℝ → ℝ)
    (hβ : ∀ r, ζ ≤ r → r ≤ 1 → 0 < β r ∧ β r ≤ ρ * r)
    (hsupport : ∀ t, IntervalAD ζ d K
      {s | ∃ l : ScalarLine, (l, t) ∈ E ∧ scalar ρ q F l t = s})
    (hcap : ∀ (t : ℝ) (v : Fin 2 → ℝ) (a : ℝ), ζ ≤ a → a ≤ 1 →
      prior θ ρ q {l | (l, t) ∈ E ∧
        ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
          ENNReal.ofReal (K * a ^ (1 + d)))
    (hrow : ∀ p ∈ E, ∀ p' ∈ E,
      |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ))
    (hresidual : ∀ p ∈ E, ∀ p' ∈ E,
      |residual ρ q F p.1 p.2 - residual ρ q F p'.1 p'.2| ≤
        K * (‖position ρ q p - position ρ q p'‖ + ζ))
    (hconditional : ∀ r, ζ ≤ r → r ≤ 1 →
      ∀ (b : Fin 5 → ℤ) (t : ℝ) (v : Fin 2 → ℝ) (a : ℝ), ζ ≤ a → a ≤ r →
      prior θ ρ q {l | cell (β r) l.2 = b ∧ (l, t) ∈ E ∧
        ∀ e, zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
          ENNReal.ofReal (K * (a / r) ^ (1 + d)) *
            prior θ ρ q {l | cell (β r) l.2 = b}) :
    Jets.ScalarNormal (prior θ ρ q) (coeff ρ q) E F
      (fun r l => cell (β r) l.2) K ζ d := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hdense : ENNReal.ofReal K⁻¹ ≤ ((prior θ ρ q).prod volume) E := by
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      (prior_product_dense θ μ hH hμ q hpositive hE hworld hmass)
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hKpos hH).mpr
    simpa only [one_mul, mul_one, mul_comm] using (div_le_iff₀ hδ).mp hbudget
  refine
    { prob := prior_probability θ ρ q hpositive
      one_le_K := hK
      zeta_pos := hζ
      zeta_le_one := hζ₁
      measurable_c := measurable_coeff ρ q
      measurableSet_E := hE
      measurable_F := hF
      measurable_piece := fun r => measurable_cell (β r) measurable_snd
      time_mem := htime
      coeff_le := fun p hp e => (coeff_abs_le_one hρ (hworld p hp) e).trans hK
      row_le := hbound
      dense := hdense
      support := ?_
      abs_cap := ?_
      row_cmp := hrow
      resid_cmp := ?_
      piece_diam := ?_
      bin_cap := ?_ }
  · intro t
    simpa only [jets_scalar] using hsupport t
  · intro t a b s hs hs₁
    apply (measure_mono ?_).trans (hcap t ![b, a] s hs hs₁)
    intro l hl
    refine ⟨hl.1, ?_⟩
    intro e
    fin_cases e
    · simpa [zoomSpatial, jets_y] using hl.2.2
    · simpa [zoomSpatial, jets_x] using hl.2.1
  · intro p hp p' hp'
    simpa only [jets_residual, jets_position_distance] using hresidual p hp p' hp'
  · intro r hr hr₁ l l' hbin
    have hrpos : 0 < r := hζ.trans_le hr
    apply (pi_norm_le_iff_of_nonneg hrpos.le).mpr
    intro e
    exact coeff_piece_diameter hρ (hβ r hr hr₁).1 (hβ r hr hr₁).2 q hbin e
  · intro r hr hr₁ b t a a' s hs hsr
    apply (measure_mono ?_).trans (hconditional r hr hr₁ b t ![a', a] s hs hsr)
    intro l hl
    refine ⟨hl.1, hl.2.1, ?_⟩
    intro e
    fin_cases e
    · simpa [zoomSpatial, jets_y] using hl.2.2.2
    · simpa [zoomSpatial, jets_x] using hl.2.2.1

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
