/- Adapted from this LOT tree, o178, session x0596, branch x0596 (commit 319917af),
   Submission/Obl/k4_unbounded_geometric_packet_reduction/CQ1Compare.lean (that session's own code). -/
import Submission.Obl.k4_raw_localized_native_systems.Pairing.CoarsenObs
import Submission.Obl.k4_raw_localized_native_systems.Pairing.PinningBins

/-!
# Comparison of the full-time charts with the earlier charts

Two families of labelled incidences in one world, each label carrying a unit
normal and a normal speed matched by the velocities of its incidences, and each
known by the original observation (the second at a coarser depth `r₁`).  At an
incidence carrying a label of each family with transverse normals, the velocity is
pinned to a ball around the Cramer point of the two labels, both listed by the
terminal observation.  Angular charging (`angular_listed_le`) bounds the mass of
these incidences by `N^(-S u + 2τ)` times the product of the list lengths.

Applied to the full-time charts (strip width `gC`) and the earlier charts (strip
width of their minor axis), this is the normal comparison of the paper's
Proposition 10.2 (`a08:C-Q1-comparison`), outside a power-small mass.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The velocity bins pinned by a listed pair of transverse labels. -/
def pairBins {C C₁ : ℕ} (nC : Fin C → Plane) (spC : Fin C → ℝ) (n₁ : Fin C₁ → Plane)
    (sp₁ : Fin C₁ → ℝ) (θ w : ℝ) (lstC : Observation → Finset (Fin C))
    (lst₁ : Observation → Finset (Fin C₁)) (co : Observation → Observation) (o : Observation) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact (lstC o).biUnion fun c => (lst₁ (co o)).biUnion fun e =>
    if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
      nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e)))
    else ∅

theorem card_pairBins_le {C C₁ : ℕ} (nC : Fin C → Plane) (spC : Fin C → ℝ)
    (n₁ : Fin C₁ → Plane) (sp₁ : Fin C₁ → ℝ) (θ w : ℝ) (lstC : Observation → Finset (Fin C))
    (lst₁ : Observation → Finset (Fin C₁)) (co : Observation → Observation) {κC κ₁ : ℕ}
    (hC : ∀ o, (lstC o).card ≤ κC) (h₁ : ∀ o, (lst₁ o).card ≤ κ₁) (o : Observation) :
    (pairBins nC spC n₁ sp₁ θ w lstC lst₁ co o).card ≤ 9 * κC * κ₁ := by
  classical
  unfold pairBins
  refine (Finset.card_biUnion_le).trans ?_
  have hinner : ∀ c, ((lst₁ (co o)).biUnion fun e =>
      if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
        nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e))) else ∅).card ≤ 9 * κ₁ := by
    intro c
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ e ∈ lst₁ (co o), (if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
          nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e))) else ∅).card
        ≤ ∑ _e ∈ lst₁ (co o), 9 := by
          apply Finset.sum_le_sum
          intro e _
          split_ifs
          · exact card_nbhd_le _
          · simp
      _ = 9 * (lst₁ (co o)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 9 * κ₁ := by gcongr; exact h₁ _
  calc ∑ c ∈ lstC o, ((lst₁ (co o)).biUnion fun e =>
        if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
          nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e))) else ∅).card
      ≤ ∑ _c ∈ lstC o, 9 * κ₁ := Finset.sum_le_sum fun c _ => hinner c
    _ = 9 * κ₁ * (lstC o).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 9 * κ₁ * κC := by gcongr; exact hC o
    _ = 9 * κC * κ₁ := by ring

theorem measurableSet_pairBins {C C₁ : ℕ} (nC : Fin C → Plane) (spC : Fin C → ℝ)
    (n₁ : Fin C₁ → Plane) (sp₁ : Fin C₁ → ℝ) (θ w : ℝ) (lstC : Observation → Finset (Fin C))
    (lst₁ : Observation → Finset (Fin C₁)) {co : Observation → Observation} (hco : Measurable co)
    (hC : ∀ c, MeasurableSet {o | c ∈ lstC o}) (h₁ : ∀ e, MeasurableSet {o | e ∈ lst₁ o})
    (z : Fin 2 → ℤ) :
    MeasurableSet {o | z ∈ pairBins nC spC n₁ sp₁ θ w lstC lst₁ co o} := by
  classical
  have : {o | z ∈ pairBins nC spC n₁ sp₁ θ w lstC lst₁ co o} =
      ⋃ c, ⋃ e, ({o | c ∈ lstC o} ∩ co ⁻¹' {o' | e ∈ lst₁ o'}) ∩
        {_o | z ∈ (if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
          nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e))) else ∅)} := by
    ext o
    simp only [pairBins, Finset.mem_biUnion, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · rintro ⟨c, hc, e, he, hz⟩; exact ⟨c, e, ⟨hc, he⟩, hz⟩
    · rintro ⟨c, e, ⟨hc, he⟩, hz⟩; exact ⟨c, hc, e, he, hz⟩
  rw [this]
  refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun e => ?_
  refine ((hC c).inter (hco (h₁ e))).inter ?_
  by_cases h : z ∈ (if θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖ then
      nbhd (binOf w (cramer (nC c) (n₁ e) (spC c) (sp₁ e))) else ∅)
  · simp only [h, Set.setOf_true, MeasurableSet.univ]
  · simp only [h, Set.setOf_false, MeasurableSet.empty]

/-- **Transverse pairs of listed labels.** -/
theorem transverse_pair_mass_le {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    {C C₁ : ℕ} (nC : Fin C → Plane) (spC : Fin C → ℝ) (FC : Fin C → Set Point)
    (lstC : Observation → Finset (Fin C)) (κC : ℕ) (hcardC : ∀ o, (lstC o).card ≤ κC)
    (hmeasC : ∀ c, MeasurableSet {o | c ∈ lstC o})
    (n₁ : Fin C₁ → Plane) (sp₁ : Fin C₁ → ℝ) (F₁ : Fin C₁ → Set Point)
    (lst₁ : Observation → Finset (Fin C₁)) (κ₁ : ℕ) (hcard₁ : ∀ o, (lst₁ o).card ≤ κ₁)
    (hmeas₁ : ∀ e, MeasurableSet {o | e ∈ lst₁ o})
    {r₁ : ℝ} (hr₁ : 0 ≤ r₁) (hr₁L : r₁ ≤ p.L)
    (hknownC : ∀ c, ∀ z ∈ FC c, c ∈ lstC (obs (p.B k γ) (δ (p.N k) p.L) z))
    (hknown₁ : ∀ e, ∀ z ∈ F₁ e, e ∈ lst₁ (obs (p.B k γ) (δ (p.N k) r₁) z))
    {ρ σ θ : ℝ} (hθ : 0 < θ) (hpin : 4 * (ρ + σ) / θ ≤ δ (p.N k) u)
    (hnC : ∀ c, ‖nC c‖ = 1) (hn₁ : ∀ e, ‖n₁ e‖ = 1)
    (hspC : ∀ c, ∀ z ∈ FC c, |inner ℝ (nC c) (v z.1) - spC c| ≤ ρ)
    (hsp₁ : ∀ e, ∀ z ∈ F₁ e, |inner ℝ (n₁ e) (v z.1) - sp₁ e| ≤ σ) :
    selected p k γ {z | AngGood p k γ u τ z ∧ ∃ c e, z ∈ FC c ∧ z ∈ F₁ e ∧
        θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κC * κ₁ : ℕ) : ENNReal) := by
  classical
  have hN1 : 1 ≤ p.N k := hp.scale_ge_one k
  have hL : 0 ≤ p.L := hp.length_pos.le
  have hδu : 0 < δ (p.N k) u := by unfold δ; positivity
  set n := Submission.Lib.K4XInterface.depthIdx (p.N k) p.L -
    Submission.Lib.K4XInterface.depthIdx (p.N k) r₁ with hn
  set co := Submission.Lib.K4XInterface.coarsenObs n with hco
  have hcom : Measurable co := measurable_coarsenObs n
  set bins := pairBins nC spC n₁ sp₁ θ (δ (p.N k) u) lstC lst₁ co with hbins
  have hsub : {z | AngGood p k γ u τ z ∧ ∃ c e, z ∈ FC c ∧ z ∈ F₁ e ∧
        θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖} ⊆
      {z | AngGood p k γ u τ z ∧ velBin (p.N k) u z ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) z)} := by
    rintro z ⟨hgood, c, e, hzc, hze, hsep⟩
    refine ⟨hgood, ?_⟩
    have hlc := hknownC c z hzc
    have hle := hknown₁ e z hze
    have hco_eq : obs (p.B k γ) (δ (p.N k) r₁) z = co (obs (p.B k γ) (δ (p.N k) p.L) z) :=
      Submission.Lib.K4XInterface.gobs_coarsen hN1 hr₁ hr₁L (p.B k γ) z
    rw [hco_eq] at hle
    have hpinned := norm_sub_cramer_le (hnC c) (hn₁ e) hθ hsep (hspC c z hzc) (hsp₁ e z hze)
    have hbin := binOf_mem_nbhd hδu (hpinned.trans hpin)
    simp only [hbins, pairBins, Finset.mem_biUnion]
    refine ⟨c, hlc, e, hle, ?_⟩
    rw [if_pos hsep]
    exact hbin
  have hEsub : selected p k γ Set.univ ≤ 1 := by
    obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    have hEs : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
    haveI : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
    unfold selected priorMass
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    calc ((p.ν k γ).prod volume) (p.E k γ) ≤ ((p.ν k γ).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) :=
          measure_mono hEs
      _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp
  calc selected p k γ {z | AngGood p k γ u τ z ∧ ∃ c e, z ∈ FC c ∧ z ∈ F₁ e ∧
          θ < min ‖nC c - n₁ e‖ ‖nC c + n₁ e‖}
      ≤ selected p k γ {z | AngGood p k γ u τ z ∧
          velBin (p.N k) u z ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) z)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κC * κ₁ : ℕ) : ENNReal) *
          selected p k γ Set.univ :=
        angular_listed_le hp k γ hu huη bins (9 * κC * κ₁)
          (fun w => measurableSet_pairBins nC spC n₁ sp₁ θ (δ (p.N k) u) lstC lst₁ hcom hmeasC
            hmeas₁ w)
          (fun o => card_pairBins_le nC spC n₁ sp₁ θ (δ (p.N k) u) lstC lst₁ co hcardC hcard₁ o)
    _ ≤ ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κC * κ₁ : ℕ) : ENNReal) * 1 := by
        gcongr
    _ = _ := mul_one _

end

end Submission.Obl.k4_raw_localized_native_systems.Pairing
