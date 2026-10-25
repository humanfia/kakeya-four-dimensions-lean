/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalFailedSource.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.FailureWorldChoice
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalMeshCore
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalDensity
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldJetDiscovery

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal

namespace ScalarData

/-- A dense failure in the literal frozen graph gives an original failed
mixture component and its first common-choice source. Null cuts provide
all mesh-positive records and all original packet interiors at zero cost.
The sole positive loss is the displayed original-state selection factor. -/
theorem graphData.exists_failed_original_row_source {D : ScalarData}
    {H₀ Hg : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    {L B : ℝ} {G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ}
    (hgraph : D.graphData E₀ L Hg B G E)
    (hprep : D.prepData H₀ θ E₀) (hbase : D.base) (hpack : D.packets)
    (hN : ∀ k, 2 ≤ D.N k) (C J : ℕ) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hCL : (C : ℝ) ≤ L) (M : ℕ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, δ ≤ (D.toQualificationTable B G E).rationalFailureRatio M ε k →
      ∃ (g : Fin (D.W k)) (R : Set ScalarIncidence),
        0 < D.ω k g ∧ MeasurableSet R ∧ R ⊆ E k g ∧
        R ⊆ (D.toQualificationTable B G E).rationalFailure M ε k g ∧
        ENNReal.ofReal (δ / (2 * Hg k)) ≤
          ((4 : ENNReal) ^ 3 * (2 ^ 3 * (⌈(2 * Hg k + 2) ^ 2⌉₊ : ENNReal))) ^ (C * J + 1) *
            ((D.ρ k g).restrict (E₀ k g)) R ∧
        (∀ p ∈ R, ∀ p' ∈ R,
          ‖G k g (D.phys k B p) - G k g (D.phys k B p')‖ ≤
            6 * (D.N k ^ ((1 : ℝ) / (J : ℝ)) + (2 * Hg k + 2) ^ 2) *
              (‖scalarPosition p - scalarPosition p'‖ + D.N k ^ (-(C : ℝ)))) ∧
        (∀ r r₀ : ℝ, (∃ m : ℕ, r = (m : ℝ) / (D.prepMesh hprep k : ℝ)) →
          (∃ m : ℕ, r₀ = (m : ℝ) / (D.prepMesh hprep k : ℝ)) → ∀ p ∈ R,
            (D.ρ k g).restrict (E₀ k g)
              {p' | D.phys k r p' = D.phys k r p ∧ D.phys k r₀ p' = D.phys k r₀ p} ≠ 0) ∧
        (∀ r : ℝ, (∃ m : ℕ, r = (m : ℝ) / (D.prepMesh hprep k : ℝ)) → ∀ p ∈ R,
          (D.ρ k g).restrict (E₀ k g)
            {p' | D.phys k r p' = D.phys k r p ∧ D.coeff k r p'.1 = D.coeff k r p.1} ≠ 0) ∧
        ∀ p ∈ R, ∀ i : Fin (D.n k 1), p.2 ∈ timeBlock (D.T k 1) (D.j k 1 i) →
          p.2 ∈ Ioo (((D.j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ D.T k 1)
            ((((D.j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T k 1) := by
  classical
  filter_upwards [hgraph.2.2 2 (by norm_num), hpack 2 (by norm_num),
    hprep.original_density_caps, hgraph.original_row_selection hN C J hC hJ hCL] with k hg hp hd hr
  intro hratio
  let tab := D.toQualificationTable B G E
  have hHg : 0 < Hg k := by linarith [hgraph.1.1 k]
  obtain ⟨g, hω, hbad⟩ := tab.exists_dense_original_failure_world M ε k hδ hHg
    (hbase k).1 (hbase k).2.1
    (fun g => ne_top_of_le_ne_top (rho_finite hbase k g) (Measure.restrict_le_self univ))
    (by
      change ENNReal.ofReal (1 / Hg k) ≤
        ∑ g : Fin (D.W k), ENNReal.ofReal (D.ω k g) * ((D.ρ k g).restrict (E k g)) univ
      rw [one_div]
      exact hg.1) hratio
  let μ := (D.ρ k g).restrict (E₀ k g)
  have hEm (g : Fin (D.W k)) : MeasurableSet (E k g) := (hg.2 g).1
  have hsub : E k g ⊆ E₀ k g := (hg.2 g).2.1
  have hpacket := hp 1 (by norm_num) (by norm_num)
  have hbadm : MeasurableSet (tab.rationalFailure M ε k g) :=
    tab.measurableSet_rationalFailure M ε k g hEm
      (D.measurable_graph_row k B (G k)) hpacket.2.2.1 (fun _ => measurableSet_Icc)
  let bad := E k g ∩ tab.rationalFailure M ε k g
  have hbadm' : MeasurableSet bad := (hEm g).inter hbadm
  have hbadsub : bad ⊆ E₀ k g := fun _ hp => hsub hp.1
  have hbadmass : tab.law k g (tab.rationalFailure M ε k g) = μ bad := by
    rw [QualificationTable.law, Measure.restrict_apply hbadm]
    dsimp only [μ]
    rw [Measure.restrict_apply hbadm', inter_eq_left.mpr hbadsub]
    exact congrArg (D.ρ k g) (inter_comm _ _)
  rw [hbadmass] at hbad
  obtain ⟨Core, hCore, hnull, hpairs, hparams⟩ :=
    D.exists_original_mesh_positive_core k (D.prepMesh hprep k) μ
  let badCore := bad ∩ Core
  have hbadCore : MeasurableSet badCore := hbadm'.inter hCore
  have hcoremass : μ badCore = μ bad := measure_inter_conull hnull
  have hAC : μ ≪ (θ k g).prod volume := Measure.absolutelyContinuous_of_le_smul (hd g).1
  obtain ⟨I, hI, hIsub, hImass, _, hinterior⟩ :=
    exists_packet_interior_restriction (θ k g) μ hAC (D.j k 1) badCore hbadCore
  have hIE : I ⊆ E k g := fun _ hi => (hIsub hi).1.1
  have hIprep : I ⊆ E₀ k g := hIE.trans hsub
  have hcur : μ.restrict I ≤ (D.ρ k g).restrict (E k g) := by
    dsimp only [μ]
    rw [Measure.restrict_restrict_of_subset hIprep]
    exact Measure.restrict_mono_set _ hIE
  obtain ⟨S, hS, hmass, hcmp⟩ := hr g (μ.restrict I) hcur
  let R := I ∩ {p | D.phys k B p ∈ S}
  have hpreS : MeasurableSet {p | D.phys k B p ∈ S} := (D.measurable_phys k B) hS
  have hR : MeasurableSet R := hI.inter hpreS
  have hmass' : μ I ≤
      ((4 : ENNReal) ^ 3 * (2 ^ 3 * (⌈(2 * Hg k + 2) ^ 2⌉₊ : ENNReal))) ^ (C * J + 1) * μ R := by
    simpa only [Measure.restrict_apply_univ, Measure.restrict_apply hpreS,
      R, inter_comm] using hmass
  refine ⟨g, R, hω, hR, (fun _ hr => hIE hr.1),
    (fun _ hr => (hIsub hr.1).1.2), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hbad.trans_eq (hcoremass.symm.trans hImass.symm)).trans hmass'
  · intro p hp p' hp'
    exact hcmp p hp.2 p' hp'.2
  · intro r r₀ hrg hr₀g p hp
    exact hpairs r r₀ hrg hr₀g p (hIsub hp.1).2
  · intro r hrg p hp
    exact hparams r hrg p (hIsub hp.1).2
  · intro p hp
    exact hinterior p hp.1

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
