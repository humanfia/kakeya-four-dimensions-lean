/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalParameterCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice

namespace ScalarData

/-- Literal frozen fixed-time caps and coefficient floors yield the
conditional zoom cap on every later restriction of the labels. Coarse and
fine coefficient boxes need not be nested. -/
theorem prepData.original_zoom_spatial_caps {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) (hN : ∀ k, 2 ≤ D.N k) :
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
      M = D.prepMesh hprep ∧
      ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ g : Fin (D.W k), ∀ r s : ℝ,
        R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R →
        (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) →
        (∃ m : ℕ, s = (m : ℝ) / (M k : ℝ)) →
        ∀ ρ a : ℝ, 0 < ρ → 0 ≤ a → ∀ (q b : Fin 5 → ℤ) (t : ℝ)
          (E' : Set ScalarIncidence), E' ⊆ E₀ k g →
        ∀ η : ENNReal, η ≠ 0 → η ≠ ⊤ →
        (D.ρ k g).restrict (E₀ k g) {p | D.coeff k r p.1 = b} ≠ 0 →
        η * θ k g {l | cell (D.N k ^ (-r)) l.2 = b} ≤
          θ k g {l | cell (D.N k ^ (-r)) l.2 = b ∧ cell ρ l.2 = q} →
        ∀ v : Fin 2 → ℝ,
          Zoom.prior (θ k g) ρ q {l | cell (D.N k ^ (-r)) l.2 = b ∧ (l, t) ∈ E' ∧
            ∀ e, Zoom.zoomSpatial ρ q l t e ∈ Ico (v e) (v e + a)} ≤
          ((ENNReal.ofReal ((ρ * a / D.N k ^ (-s) + 2) ^ 2) *
              ENNReal.ofReal (H k * D.N k ^ (-s - D.d * s))) /
            (η * ENNReal.ofReal (D.N k ^ (-(1 + D.d) * r) / H k))) *
            Zoom.prior (θ k g) ρ q {l | cell (D.N k ^ (-r)) l.2 = b} := by
  let M := D.prepMesh hprep
  obtain ⟨hM, hdata⟩ := Classical.choose_spec hprep.2
  refine ⟨M, hM, rfl, ?_⟩
  intro R hR
  filter_upwards [hdata R hR] with k hk
  intro g r s hrlo hrhi hslo hshi hrgrid hsgrid ρ a hρ ha q b t E' hEsub η hη0 hηtop hpart hinter v
  obtain ⟨hθν, hθone, hEmeas, hbound, hθbound, hdenslow, hdensup, hgrid, hfixed⟩ := hk.2 g
  obtain ⟨hphysfin, hphyscard, hhereditary, hcoeff, hparamlist⟩ := hgrid r hrlo hrhi hrgrid
  have hfloor := (hcoeff b hpart).1
  have hcoeff_eq (l : ScalarLine) : D.coeff k r l = cell (D.N k ^ (-r)) l.2 := by
    funext e
    rfl
  have hfloor' : ENNReal.ofReal (D.N k ^ (-(1 + D.d) * r) / H k) *
      D.π k g (D.vel k r (b 1)) ≤ θ k g {l | cell (D.N k ^ (-r)) l.2 = b} := by
    simpa only [hcoeff_eq] using hfloor
  obtain ⟨mr, hmr⟩ := hrgrid
  obtain ⟨ms, hms⟩ := hsgrid
  have hraw := hfixed s s r t hslo hshi hslo hshi hrlo hrhi ⟨ms, ms, mr, hms, hms, hmr⟩
  have hcap (z : Fin 2 → ℤ) :
      θ k g {l | (l, t) ∈ E' ∧ cell (D.N k ^ (-r)) l.2 = b ∧
        cell (D.N k ^ (-s)) (Zoom.spatial l t) = z} ≤
      ENNReal.ofReal (H k * D.N k ^ (-s - D.d * s)) * D.π k g (D.vel k r (b 1)) := by
    apply (measure_mono (t := {l | (l, t) ∈ E₀ k g ∧
      (⌊scalarY l t / D.N k ^ (-s)⌋ : ℤ) = z 0 ∧
      (⌊scalarX l t / D.N k ^ (-s)⌋ : ℤ) = z 1 ∧ l.2 1 ∈ D.vel k r (b 1)}) ?_).trans
      (hraw (z 0) (z 1) (b 1))
    intro l hl
    have hvel : l.2 1 ∈ D.vel k r (b 1) := congr_fun hl.2.1 1
    have hy := congr_fun hl.2.2 0
    have hx := congr_fun hl.2.2 1
    exact ⟨hEsub hl.1, hy, hx, hvel⟩
  have hN0 : 0 < D.N k := by linarith [hN k]
  have hH0 : 0 < H k := by linarith [hprep.1.1 k]
  exact Zoom.prior_piece_spatial_cap (θ k g) E' t hρ (Real.rpow_pos_of_pos hN0 _) ha q b
    (ENNReal.ofReal (H k * D.N k ^ (-s - D.d * s)))
    (ENNReal.ofReal (D.N k ^ (-(1 + D.d) * r) / H k)) η (D.π k g (D.vel k r (b 1)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top hη0 hηtop
    hcap hfloor' hinter v

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
