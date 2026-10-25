/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalResidualScale.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldResidualScale
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation

namespace ScalarData

/-- Primitive residual-scale data come directly from the frozen original
graph and preparation. The raw cell-cover cost is `(H+2)^2`, using only
the original mesh rounding. The incidence law is the ORIGINAL graph law. -/
theorem prepData.original_residual_scale {D : ScalarData}
    {H Hg : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ Eg : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hprep : D.prepData H θ E₀) (hgraph : D.graphData E₀ L Hg B G Eg)
    (hN : ∀ k, 2 ≤ D.N k) :
    ∀ T : ℝ, 1 < T → ∀ᶠ k in atTop, ∀ (g : Fin (D.W k)) (u : ℝ),
      T⁻¹ ≤ u → u ≤ T → (∃ m : ℕ, u = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
      let β := D.N k ^ (-u)
      let b := D.N k ^ (-B)
      let μ := (D.ρ k g).restrict (Eg k g)
      ∀ (R : Set ScalarIncidence), R ⊆ Eg k g →
      ∀ ρ r Ac η ηp : ℝ, 0 < ρ → 0 < r → β ≤ ρ * r → ρ * r ≤ H k * β →
      0 < Ac → 0 < η → 0 < ηp →
      ∀ q : Fin 5 → ℤ, D.π k g (scalarVelocityBin ρ (q 1)) ≠ 0 →
      (∀ p ∈ R, (D.ρ k g).restrict (E₀ k g)
        {p' | D.coeff k u p'.1 = D.coeff k u p.1} ≠ 0) →
      (∀ p ∈ R, ENNReal.ofReal η * θ k g {l | cell β l.2 = cell β p.1.2} ≤
        θ k g {l | cell ρ l.2 = cell ρ p.1.2 ∧ cell β l.2 = cell β p.1.2}) →
      (∀ a : Zoom.OriginalPosteriorRecord,
        R ∩ Zoom.posteriorEntryRecord ρ b r ⁻¹' {a} = ∅ ∨
          ENNReal.ofReal ηp * μ ((fun p => cell b (scalarPosition p)) ⁻¹' {a.2.1}) *
            D.π k g (scalarVelocityBin ρ a.2.2) <
              μ (R ∩ Zoom.posteriorEntryRecord ρ b r ⁻¹' {a})) →
      (∀ z b',
        R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ β q b') r z = ∅ ∨
          ENNReal.ofReal (r / Ac) * θ k g (Zoom.parameterPiece ρ β q b') <
            μ (R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ β q b') r z)) →
      ∃ raw : Zoom.OriginalResidualScale μ (θ k g) (D.π k g) R (Eg k g) ρ b r (H k) q,
        ∀ Hrow Lrow : ℝ, raw.listBound Hrow Lrow =
          (Hg k / ηp + 2) *
            ((Ac * H k ^ 3 * (H k + 2) ^ 2 / η) * (2 * (7 + Hrow + 2 * Lrow) + 2)) := by
  classical
  obtain ⟨M, _, hmesh, hcell⟩ := hprep.original_zoom_cell_incidence_cap hN
  subst M
  have hdata := (Classical.choose_spec hprep.2).2
  intro T hT
  filter_upwards [hcell T hT, hdata T hT, hgraph.2.2 T hT] with k hc hp hg
  intro g u hulo huhi humesh
  dsimp only
  intro R hRE ρ r Ac η ηp hρ hr hscale hscale' hAc hη hηp q hpalette
    hpositive hinter hposter hcoef
  let β := D.N k ^ (-u)
  let b := D.N k ^ (-B)
  let μ := (D.ρ k g).restrict (Eg k g)
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hβ : 0 < β := Real.rpow_pos_of_pos hN₀ _
  have hH : 0 < H k := by linarith [hprep.1.1 k]
  have hH₀ : 0 ≤ H k := hH.le
  have hEgsub : Eg k g ⊆ E₀ k g := (hg.2 g).2.1
  have hμ : μ ≤ (D.ρ k g).restrict (E₀ k g) := Measure.restrict_mono_set _ hEgsub
  have hvel (j : ℤ) : D.vel k u j = scalarVelocityBin β j := rfl
  have hcoeff (l : ScalarLine) : D.coeff k u l = cell β l.2 := by
    funext e
    rfl
  have hpow : D.N k ^ (-u - D.d * u) = β ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hpow' : D.N k ^ (-(1 + D.d) * u) = β ^ (1 + D.d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hgraphcap : ∀ (w : Fin 3 → ℤ) (j : ℤ),
      μ {p | cell b (scalarPosition p) = w ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j} ≤
        ENNReal.ofReal (Hg k) * μ ((fun p => cell b (scalarPosition p)) ⁻¹' {w}) *
          D.π k g (scalarVelocityBin β j) := by
    intro w j
    exact (hg.2 g).2.2.2.2 u hulo huhi w j
  have hprior : ∀ (z : Fin 3 → ℤ) (j : ℤ) (b' : Fin 5 → ℤ),
      μ (R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ β q b') r z) ≠ 0 →
      b' 1 = j → ENNReal.ofReal (η * β ^ (1 + D.d) / H k) *
        D.π k g (scalarVelocityBin β j) ≤ θ k g (Zoom.parameterPiece ρ β q b') := by
    intro z j b' hcur hb'j
    obtain ⟨p, hpR⟩ := nonempty_of_measure_ne_zero hcur
    have hpos := hpositive p hpR.1
    have hbin : D.coeff k u p.1 = b' := hpR.2.1.2
    rw [hbin] at hpos
    have hfull := ((hp.2 g).2.2.2.2.2.2.2.1 u hulo huhi humesh).2.2.2.1 b' hpos |>.1
    have hfull' : ENNReal.ofReal (β ^ (1 + D.d) / H k) *
        D.π k g (scalarVelocityBin β j) ≤ θ k g {l | cell β l.2 = b'} := by
      simpa only [hpow', hb'j, hvel, hcoeff] using hfull
    have hint := hinter p hpR.1
    have hbin' : cell β p.1.2 = b' := hpR.2.1.2
    have hcoarse : cell ρ p.1.2 = q := hpR.2.1.1
    rw [hbin', hcoarse] at hint
    calc
      _ = ENNReal.ofReal η * (ENNReal.ofReal (β ^ (1 + D.d) / H k) *
          D.π k g (scalarVelocityBin β j)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hη.le]
        congr 2
        ring
      _ ≤ ENNReal.ofReal η * θ k g {l | cell β l.2 = b'} :=
        mul_le_mul_of_nonneg_left hfull' zero_le
      _ ≤ _ := hint
  have hcover : (ρ * r / β + 2) ^ 2 ≤ (H k + 2) ^ 2 := by
    have hh := (div_le_iff₀ hβ).mpr hscale'
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hcap : ∀ (z : Fin 3 → ℤ) (j : ℤ),
      μ {p | p ∈ Eg k g ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j ∧ cell r (Zoom.position ρ q p) = z} ≤
        ENNReal.ofReal (H k ^ 2 * r * (H k + 2) ^ 2 * β ^ (1 + D.d)) *
          D.π k g (scalarVelocityBin β j) := by
    intro z j
    have hh := hc g u hulo huhi humesh μ hμ ρ r hρ hr q z j
    rw [hpow, hvel] at hh
    have hsubset :
        {p : ScalarIncidence | p ∈ Eg k g ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j ∧ cell r (Zoom.position ρ q p) = z} ⊆
          {p | p ∈ E₀ k g ∧ (⌊p.1.2 1 / β⌋ : ℤ) = j ∧ cell r (Zoom.position ρ q p) = z} :=
      fun _ hp => ⟨hEgsub hp.1, hp.2⟩
    apply (measure_mono hsubset).trans (hh.trans ?_)
    calc
      _ ≤ ENNReal.ofReal (H k) * ENNReal.ofReal r * ENNReal.ofReal ((H k + 2) ^ 2) *
          ENNReal.ofReal (H k * β ^ (1 + D.d)) * D.π k g (scalarVelocityBin β j) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hH₀, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  refine ⟨{
    β := β, A := Ac, η := η, C := (H k + 2) ^ 2, s := β ^ (1 + D.d), ηp := ηp, Cg := Hg k
    beta_pos := hβ, scale := hscale, A_pos := hAc, eta_pos := hη
    C_nonneg := sq_nonneg _, s_pos := Real.rpow_pos_of_pos hβ _, etap_pos := hηp
    Cg_nonneg := by linarith [hgraph.1.1 k]
    palette := hpalette
    old := fun w => μ ((fun p => cell b (scalarPosition p)) ⁻¹' {w})
    graph_cap := hgraphcap
    posterior_floor := hposter
    coefficient_floor := hcoef
    prior_floor := hprior
    cell_cap := hcap
  }, ?_⟩
  intro Hrow Lrow
  rfl

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
