/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldJetDiscovery.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Jets.Interface
import Submission.Obl.k4_scalar_graph_residual_discovery.Packets
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarFitNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- At an interior packet time, the block read by the higher-jet theorem
is the original packet's block, including both endpoints for witness times. -/
theorem dyadicBlock_eq_timeBlock_of_interior (T : ℕ) (j : Fin (2 ^ T)) {t : ℝ}
    (ht : t ∈ Ioo (((j : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) :
    Jets.dyadicBlock T t = timeBlock T j := by
  have hpow : 0 < (2 : ℝ) ^ T := by positivity
  have hfloor : ⌊t * (2 : ℝ) ^ T⌋ = ((j : ℕ) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast ((div_lt_iff₀ hpow).mp ht.1).le
    · exact_mod_cast (lt_div_iff₀ hpow).mp ht.2
  simp only [Jets.dyadicBlock, hfloor, Int.cast_natCast, timeBlock]

/-- Endpoint removal costs no original incidence mass and no prior-time
mass. It can be done before any geometric cut, for all original packet
labels at once. Every later subset then has pointwise interior membership. -/
theorem exists_packet_interior_restriction {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (hμ : μ ≪ ν.prod volume)
    {n T : ℕ} (j : Fin n → Fin (2 ^ T))
    (E : Set (α × ℝ)) (hE : MeasurableSet E) :
    ∃ R : Set (α × ℝ), MeasurableSet R ∧ R ⊆ E ∧ μ R = μ E ∧
      (ν.prod volume) R = (ν.prod volume) E ∧
      ∀ p ∈ R, ∀ i, p.2 ∈ timeBlock T (j i) →
        p.2 ∈ Ioo (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) := by
  let G : Set (α × ℝ) := {p | ∀ i, p.2 ∈ timeBlock T (j i) →
    p.2 ∈ Ioo (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)}
  have hG : MeasurableSet G := by
    have hi (i : Fin n) : MeasurableSet {p : α × ℝ |
        p.2 ∈ timeBlock T (j i) → p.2 ∈ Ioo (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)} := by
      let a : ℝ := ((j i : ℕ) : ℝ) / (2 : ℝ) ^ T
      let b : ℝ := (((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T
      have heq : {p : α × ℝ | p.2 ∈ timeBlock T (j i) → p.2 ∈ Ioo a b} =
          (Prod.snd ⁻¹' Icc a b)ᶜ ∪ Prod.snd ⁻¹' Ioo a b := by
        ext p
        simp only [timeBlock, a, b, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage,
          imp_iff_not_or]
      rw [heq]
      exact (measurable_snd measurableSet_Icc).compl.union (measurable_snd measurableSet_Ioo)
    simpa only [G, Set.ofPred_forall] using MeasurableSet.iInter hi
  have hμG : ∀ᵐ p ∂μ, p ∈ G := by
    simpa only [G, Set.mem_setOf_eq, timeBlock] using
      ae_packet_membership_interior ν μ hμ j
  have hνG : ∀ᵐ p ∂ν.prod volume, p ∈ G := by
    simpa only [G, Set.mem_setOf_eq, timeBlock] using
      ae_packet_membership_interior ν (ν.prod volume) Measure.AbsolutelyContinuous.rfl j
  exact ⟨E ∩ G, hE.inter hG, inter_subset_left,
    measure_inter_conull (ae_iff.mp hμG), measure_inter_conull (ae_iff.mp hνG),
    fun p hp => hp.2⟩

/-- A jet witness is read in exactly the same original packet and on the
same original labelled time fiber. This only adapts the interface; the two
row construction is the existing `row_fit_of_scalar_fit`. -/
theorem row_fit_of_jet_fit
    {E : Set ScalarIncidence} {G : ScalarIncidence → Fin 2 → ℝ}
    (F : ℝ → ℝ) (P : Polynomial ℝ) {p : ScalarIncidence} (hp : p ∈ E)
    {T M : ℕ} (j : Fin (2 ^ T)) (hM : 1 ≤ M)
    (ht : p.2 ∈ Ioo (((j : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))
    {H C σ δ e τ : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hcoeff : ∀ a, |p.1.2 a| ≤ H)
    (hgraph : ∀ z ∈ E,
      |z.1.2 3 + 2 * z.2 * z.1.2 4 - G z 0 - G z 1 * z.1.2 1| ≤ σ)
    (hrow : ∀ z ∈ E, |G z 1 - F z.2| ≤ δ)
    (hfit : Jets.JetFit E F M T C e τ p P) :
    FitsWith E G (timeBlock T j) M (3 * H + (1 + H) * C)
      (σ + (1 + H) * (δ + e)) τ p (recoverRowPolynomial p.1 P) := by
  obtain ⟨hdegree, hpoly, hpoint, hduration⟩ := hfit
  apply row_fit_of_scalar_fit F P hp hM hH hC hcoeff hdegree hpoly
    hgraph hrow hpoint
  apply hduration.trans (measure_mono ?_)
  intro t ht'
  refine ⟨ht'.2.1, ?_, ht'.2.2⟩
  simpa only [dyadicBlock_eq_timeBlock_of_interior T j ht] using ht'.1

/-- The scalar higher-jet error has the precise extra eighth-power gain
used by the existing original-row slack calculation. -/
theorem jet_error_eq {h : ℝ} (hh : 0 < h) (M : ℕ) :
    h ^ ((M : ℝ) + 1 / 8) = h ^ M * h ^ ((1 : ℝ) / 8) := by
  rw [Real.rpow_add hh, Real.rpow_natCast]

/-- A scalar higher-jet witness on a later world subset gives the exact
slack witness required by `QualificationTable.SlackDiscovery`. The graph
event is enlarged back to its original fixed event only AFTER constructing
the witness, retaining its original packet and every original time. -/
theorem eventually_jet_fit_to_discovery_slack {N H K : ℕ → ℝ} (T : ℕ → ℕ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε)
    (hscale : ∀ᶠ k in atTop, ((2 : ℝ) ^ T k)⁻¹ ≤ K k * N k ^ (-κ))
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ k in atTop, ∀ (R E : Set ScalarIncidence) (G : ScalarIncidence → Fin 2 → ℝ)
      (F : ℝ → ℝ) (P : Polynomial ℝ) (p : ScalarIncidence) (j : Fin (2 ^ T k)),
      R ⊆ E → p ∈ R →
      p.2 ∈ Ioo (((j : ℕ) : ℝ) / (2 : ℝ) ^ T k)
        ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T k) →
      (∀ a, |p.1.2 a| ≤ H k) →
      (∀ z ∈ R, |z.1.2 3 + 2 * z.2 * z.1.2 4 - G z 0 - G z 1 * z.1.2 1| ≤
        (((2 : ℝ) ^ T k)⁻¹) ^ M * (((2 : ℝ) ^ T k)⁻¹) ^ ((1 : ℝ) / 8)) →
      (∀ z ∈ R, |G z 1 - F z.2| ≤
        (((2 : ℝ) ^ T k)⁻¹) ^ M * (((2 : ℝ) ^ T k)⁻¹) ^ ((1 : ℝ) / 8)) →
      Jets.JetFit R F M (T k) (N k ^ (ε / 4))
        ((((2 : ℝ) ^ T k)⁻¹) ^ ((M : ℝ) + 1 / 8))
        (((2 : ℝ) ^ T k)⁻¹ * N k ^ (-(ε / 4))) p P →
      FitsWith E G (timeBlock (T k) j) M (N k ^ (ε / 2))
        ((((2 : ℝ) ^ T k)⁻¹) ^ M / 2)
        (((2 : ℝ) ^ T k)⁻¹ * N k ^ (-(ε / 2))) p (recoverRowPolynomial p.1 P) := by
  have hh (k : ℕ) : 0 < ((2 : ℝ) ^ T k)⁻¹ := by positivity
  filter_upwards [eventually_scalar_fit_to_discovery_slack
    hN hNt hH hK hκ hε hh hscale hM] with k hk
  intro R E G F P p j hRE hp ht hcoeff hgraph hrow hfit
  obtain ⟨hdegree, hpoly, hpoint, hduration⟩ := hfit
  rw [jet_error_eq (hh k) M] at hpoint hduration
  have hscalar := hk R G F P p (timeBlock (T k) j) hp hcoeff hdegree hpoly
    hgraph hrow hpoint (hduration.trans (measure_mono (by
      intro t ht'
      refine ⟨ht'.2.1, ?_, ht'.2.2⟩
      simpa only [dyadicBlock_eq_timeBlock_of_interior (T k) j ht] using ht'.1)))
  exact hscalar.mono hRE subset_rfl le_rfl le_rfl le_rfl le_rfl

end Submission.Obl.k4_scalar_graph_residual_discovery
