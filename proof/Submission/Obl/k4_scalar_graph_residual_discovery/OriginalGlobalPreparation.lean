/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalGlobalPreparation.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.GlobalPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalGlobalPosteriorLists
import Submission.Obl.k4_scalar_graph_residual_discovery.CoarseRows
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalDensity

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_grid_parameter_preparation
open Submission.Obl.k4_initial_horizon_bound

noncomputable section

def scalarPaletteMeasure (π : Measure ℝ) (ρ : ℝ) : Measure ℤ :=
  π.map (fun v => ⌊v / ρ⌋)

theorem scalarPaletteMeasure_singleton (π : Measure ℝ) (ρ : ℝ) (c : ℤ) :
    scalarPaletteMeasure π ρ {c} = π {v | (⌊v / ρ⌋ : ℤ) = c} := by
  exact Measure.map_apply (measurable_id.div_const ρ).floor (measurableSet_singleton c)

theorem scalarPaletteMeasure_univ (π : Measure ℝ) (ρ : ℝ) :
    scalarPaletteMeasure π ρ univ = π univ := by
  exact Measure.map_apply (measurable_id.div_const ρ).floor MeasurableSet.univ

namespace ScalarData

/-- The original preparation and graph certificates construct the global
cuts and ALL current entry floors on an actual first-row source. Neither
a posterior-list oracle nor a supplied coarse-row field is assumed. -/
theorem prepData.prepare_original_global_law {D : ScalarData}
    {H₀ Hg : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ Eg : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hprep : D.prepData H₀ θ E₀) (hgraph : D.graphData E₀ L Hg B G Eg)
    (hbase : D.base) (hN : ∀ k, 2 ≤ D.N k) :
    ∀ U : ℝ, 1 < U → ∀ᶠ k in atTop, ∀ (g : Fin (D.W k)) (a : ℝ),
      U⁻¹ ≤ a → a ≤ U → (∃ m : ℕ, a = (m : ℝ) / (D.prepMesh hprep k : ℝ)) → a ≤ B →
      ∀ {σ : Type*} [Fintype σ] (β s Ac ηdur : σ → ℝ)
        (ηint ηstrip ηpost : σ → ℝ≥0∞) (ηstate : ℝ≥0∞),
      (∀ i, 0 < β i) → (∀ i, β i ≤ D.N k ^ (-a) * s i) →
      (∀ i, 0 < s i) → (∀ i, s i ≤ 1) → (∀ i, 0 < Ac i) → (∀ i, 0 ≤ ηdur i) →
      (∀ i, (1 + 3 * (H₀ k + 1)) * D.N k ^ (-B) ≤ D.N k ^ (-a) * s i) →
      ∀ (E : Set ScalarIncidence), MeasurableSet E → E ⊆ Eg k g →
      (∀ p ∈ E, (D.ρ k g).restrict (E₀ k g)
        {p' | D.phys k a p' = D.phys k a p ∧ D.coeff k a p'.1 = D.coeff k a p.1} ≠ 0) →
      ∀ K ζ : ℝ, 0 ≤ K → 0 ≤ ζ →
      (∀ p ∈ E, ∀ p' ∈ E, ‖G k g (D.phys k B p) - G k g (D.phys k B p')‖ ≤
        K * (‖scalarPosition p - scalarPosition p'‖ + ζ)) →
      let ρ := D.N k ^ (-a)
      let b := D.N k ^ (-B)
      let Dnormal := Hg k * D.N k ^ (-L) + K * (ρ + 2 * b + ζ) * (1 + H₀ k)
      (∀ i, Dnormal * (ρ + 2 * b) + 2 * (1 + 2 * Hg k) * b ≤ ρ * s i) →
      let μ := (D.ρ k g).restrict (E₀ k g)
      let old := (D.ρ k g).restrict (Eg k g)
      ∃ (row : (Fin 3 → ℤ) → Fin 2 → ℝ) (P R : Set ScalarIncidence),
        (∀ q e, |row q e| ≤ Hg k) ∧
        (∀ p ∈ E, ∀ e, |G k g (D.phys k B p) e -
          row (cell ρ (leftCorner b (cell b (scalarPosition p)))) e| ≤ K * (ρ + 2 * b + ζ)) ∧
        MeasurableSet P ∧ P ⊆ E ∧ MeasurableSet R ∧ R ⊆ P ∧
        μ (E \ R) ≤ ENNReal.ofReal (H₀ k) * (32 * ∑ i, ηint i) * θ k g univ +
          (ENNReal.ofReal (H₀ k) * (∑ i, ENNReal.ofReal (6860 * H₀ k * ηdur i)) * θ k g univ +
            ((ηstate * old univ +
              ((∑ i, ηstrip i * μ E) +
                ∑ i, ηpost i * (ENNReal.ofReal (512 * H₀ k) * (old univ * D.π k g univ)))) +
                  (∑ i, ENNReal.ofReal ((5000 * 111 ^ 3) / Ac i)) * θ k g univ)) ∧
        (∀ p ∈ R, ∀ i, ηint i * θ k g {l | cell (β i) l.2 = cell (β i) p.1.2} ≤
          θ k g {l | cell ρ l.2 = cell ρ p.1.2 ∧ cell (β i) l.2 = cell (β i) p.1.2}) ∧
        (∀ p ∈ R, ∀ i, ENNReal.ofReal (ηdur i * ρ) ≤
          incidenceDuration (P ∩ stripRecord b ρ (ρ * s i) row ⁻¹' {stripRecord b ρ (ρ * s i) row p}) p.1) ∧
        (∀ w, R ∩ (fun p => cell b (scalarPosition p)) ⁻¹' {w} = ∅ ∨
          ηstate * old ((fun p => cell b (scalarPosition p)) ⁻¹' {w}) <
            μ (R ∩ (fun p => cell b (scalarPosition p)) ⁻¹' {w})) ∧
        (∀ i q, R ∩ stripRecord b ρ (ρ * s i) row ⁻¹' {q} = ∅ ∨
          ηstrip i * μ (P ∩ stripRecord b ρ (ρ * s i) row ⁻¹' {q}) <
            μ (R ∩ stripRecord b ρ (ρ * s i) row ⁻¹' {q})) ∧
        (∀ i e, R ∩ Zoom.posteriorEntryRecord ρ b (s i) ⁻¹' {e} = ∅ ∨
          ηpost i * old ((fun p => cell b (scalarPosition p)) ⁻¹' {e.2.1}) *
            D.π k g {v | (⌊v / ρ⌋ : ℤ) = e.2.2} <
              μ (R ∩ Zoom.posteriorEntryRecord ρ b (s i) ⁻¹' {e})) ∧
        ∀ i q b' z,
          R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ (β i) q b') (s i) z = ∅ ∨
          ENNReal.ofReal (s i / Ac i) * θ k g (Zoom.parameterPiece ρ (β i) q b') <
            μ (R ∩ coefficientPhysicalEntry (Zoom.normalizedCoeff ρ) (Zoom.parameterPiece ρ (β i) q b') (s i) z) := by
  classical
  have hpoints := (Classical.choose_spec hprep.2).2 2 (by norm_num)
  intro U hU
  filter_upwards [hprep.original_global_posterior_lists hN U hU,
    hprep.original_density_caps, hpoints, hgraph.2.2 2 (by norm_num)] with k hpost hdom hpoint hgr
  intro g a halo hahi hagrid haB σ _ β s Ac ηdur ηint ηstrip ηpost ηstate
    hβ hscale hs hs₁ hAc hηdur hsmall E hE hEE hpositive K ζ hK hζ hcompare
  dsimp only
  intro hvariation
  let ρ := D.N k ^ (-a)
  let b := D.N k ^ (-B)
  let μ := (D.ρ k g).restrict (E₀ k g)
  let old := (D.ρ k g).restrict (Eg k g)
  haveI : IsFiniteMeasure (D.ρ k g) := ⟨lt_top_iff_ne_top.mpr (rho_finite hbase k g)⟩
  haveI := (hbase k).2.2.1 g |>.1
  haveI : IsFiniteMeasure (θ k g) := isFiniteMeasure_of_le (D.ν k g) (hpoint.2 g).1
  have hEgsub : Eg k g ⊆ E₀ k g := (hgr.2 g).2.1
  have hEprep : E ⊆ E₀ k g := hEE.trans hEgsub
  have hN₀ : 0 < D.N k := by linarith [hN k]
  have hHg₀ : 0 ≤ Hg k := by linarith [hgraph.1.1 k]
  have hH₀ : 0 ≤ H₀ k := by linarith [hprep.1.1 k]
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by linarith [hN k]) _
  have hb : 0 < b := Real.rpow_pos_of_pos (by linarith [hN k]) _
  have ha : 0 < a := (inv_pos.mpr (by linarith : 0 < U)).trans_le halo
  have hρ₁ : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hN k]) (by linarith)
  have hbρ : b ≤ ρ := Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) (by linarith)
  have hcoeff : ∀ p ∈ E, ∀ e, |p.1.2 e| ≤ H₀ k :=
    fun p hp => ((hpoint.2 g).2.2.2.1 p (hEprep hp)).2
  have htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1 :=
    fun p hp => ((hpoint.2 g).2.2.2.1 p (hEprep hp)).1
  have hrow : ∀ p ∈ E, ∀ e, |G k g (D.phys k B p) e| ≤ Hg k :=
    fun p hp => ((hgr.2 g).2.2.1 p (hEE hp)).1
  have hgraph' : ∀ p ∈ E,
      |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (D.phys k B p) 0 -
        G k g (D.phys k B p) 1 * p.1.2 1| ≤ Hg k * D.N k ^ (-L) :=
    fun p hp => ((hgr.2 g).2.2.1 p (hEE hp)).2
  obtain ⟨row, hrowbound, hrowclose, hderiv⟩ := exists_assigned_normal_rows
    E (fun p => G k g (D.phys k B p)) hb hρ (by linarith [hgraph.1.1 k]) hK
      hrow hcompare (fun p hp => hcoeff p hp 1) hgraph'
  obtain ⟨lists, hlistcard, hlisted⟩ := hpost g a halo hahi hagrid B haB E hEprep hpositive s hs hsmall
  have hcard : ∀ i w, ((lists i w).card : ℝ≥0∞) ≤ ENNReal.ofReal (512 * H₀ k) := by
    intro i w
    exact_mod_cast ENNReal.ofReal_le_ofReal (hlistcard i w)
  have hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ 1 + 2 * Hg k := by
    intro q
    linarith [hrowbound q 0, hrowbound q 1]
  obtain ⟨P, R, hP, hPE, hR, hRP, hmass, hinter, hlong, hstate, hstrip, hposter, hcoef⟩ :=
    Zoom.prepare_global_original_law (θ k g) μ old (scalarPaletteMeasure (D.π k g) ρ)
      (hdom g).1 hE hρ hρ₁ hb hbρ (hprep.1.1 k) β s Ac hβ hscale hs hs₁ hAc
      ηint ηdur hηdur ηstate ηstrip ηpost (fun _ => ENNReal.ofReal (512 * H₀ k)) row
      hcoeff htime hA (by positivity) hderiv hvariation lists hcard hlisted
  refine ⟨row, P, R, hrowbound, hrowclose, hP, hPE, hR, hRP, ?_, hinter, hlong,
    hstate, hstrip, ?_, hcoef⟩
  · simpa only [scalarPaletteMeasure_univ] using hmass
  · simpa only [scalarPaletteMeasure_singleton] using hposter

end ScalarData

end

end Submission.Obl.k4_scalar_graph_residual_discovery
