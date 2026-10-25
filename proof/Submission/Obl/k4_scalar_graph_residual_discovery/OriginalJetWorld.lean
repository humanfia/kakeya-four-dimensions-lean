/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalJetWorld.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldNormal
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldJetDiscovery

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- A retained world uses the original trajectory labels, a full original
coefficient-bin prior, and the original fixed graph. The fields are the
concrete outputs of the global geometric preparation. In particular the
coefficient bound used for transfer is the ORIGINAL subpower bound `H`,
whereas the scalar-normal constant `K` may have a small fixed power cost. -/
structure OriginalJetWorld (D : ScalarData) (H : ℕ → ℝ) (B : ℝ)
    (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence)
    (M : ℕ) (ε : ℝ) (k : ℕ) where
  g : Fin (D.W k)
  θ : Measure ScalarLine
  finite_prior : IsFiniteMeasure θ
  ρ : ℝ
  rho_pos : 0 < ρ
  q : Fin 5 → ℤ
  event : Set ScalarIncidence
  F : ℝ → ℝ
  β : ℝ → ℝ
  K : ℝ
  ζ : ℝ
  normal : Jets.ScalarNormal (Zoom.prior θ ρ q) (Zoom.coeff ρ q) event F
    (fun r l => cell (β r) l.2) K ζ D.d
  sub : event ⊆ E k g
  failed : ∀ p ∈ event, ∃ i : Fin (D.n k 1),
    D.γ k 1 i = g ∧ p.1 ∈ D.A k 1 i ∧ p.2 ∈ timeBlock (D.T k 1) (D.j k 1 i) ∧
      ¬ (D.toQualificationTable B G E).rationalFit M ε k i p
  interior : ∀ p ∈ event, ∀ i : Fin (D.n k 1),
    p.2 ∈ timeBlock (D.T k 1) (D.j k 1 i) →
      p.2 ∈ Ioo (((D.j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ D.T k 1)
        ((((D.j k 1 i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T k 1)
  original_coeff : ∀ p ∈ event, ∀ a, |p.1.2 a| ≤ H k
  graph_error : ∀ p ∈ event,
    |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (D.phys k B p) 0 -
      G k g (D.phys k B p) 1 * p.1.2 1| ≤
      (((2 : ℝ) ^ D.T k 1)⁻¹) ^ M * (((2 : ℝ) ^ D.T k 1)⁻¹) ^ ((1 : ℝ) / 8)
  row_error : ∀ p ∈ event, |G k g (D.phys k B p) 1 - F p.2| ≤
    (((2 : ℝ) ^ D.T k 1)⁻¹) ^ M * (((2 : ℝ) ^ D.T k 1)⁻¹) ^ ((1 : ℝ) / 8)

/-- The floor exponent is fixed BEFORE the qualification accuracy. After
choosing the higher-jet budget exponent, every sufficiently late prepared
world gives the literal slack discovery witness in the same failed packet.
The global geometric construction only needs to produce this concrete
record; no additional endpoint, row-polynomial, or ratio argument remains. -/
theorem original_jet_world_slack_parameters
    (hjets : Jets.HigherJetsStatement) (D : ScalarData) (H : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ D.N k) (hNt : Tendsto D.N atTop atTop)
    (hH : Subpower D.N H) (hK : Subpower D.N D.K)
    (hd : 0 ≤ D.d) (hd₁ : D.d < 1) (hκ : 0 < D.κ)
    (hscale : ∀ᶠ k in atTop, ((2 : ℝ) ^ D.T k 1)⁻¹ ≤ D.K k * D.N k ^ (-D.κ))
    (M : ℕ) (hM : 2 ≤ M) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧
      ∀ᶠ k in atTop, ∀ (B : ℝ)
        (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
        (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence)
        (w : OriginalJetWorld D H B G E M ε k),
        w.K ≤ D.N k ^ α →
        D.N k ^ (-D.κ) / w.K ≤ ((2 : ℝ) ^ D.T k 1)⁻¹ →
        ((2 : ℝ) ^ D.T k 1)⁻¹ ≤ w.K * D.N k ^ (-D.κ) →
        w.ζ ≤ (((2 : ℝ) ^ D.T k 1)⁻¹) ^ cζ →
        ∃ (i : Fin (D.n k 1)) (p : ScalarIncidence) (P : RowPolynomial),
          (D.toQualificationTable B G E).incidence k i p ∧
          ¬ (D.toQualificationTable B G E).rationalFit M ε k i p ∧
          FitsWith (E k (D.γ k 1 i))
            (fun z => G k (D.γ k 1 i) (D.phys k B z))
            (timeBlock (D.T k 1) (D.j k 1 i)) M (D.N k ^ (ε / 2))
            ((((2 : ℝ) ^ D.T k 1)⁻¹) ^ M / 2)
            (((2 : ℝ) ^ D.T k 1)⁻¹ * D.N k ^ (-(ε / 2))) p P := by
  obtain ⟨cζ, hcζ, hfit⟩ := hjets D.d hd hd₁ M hM D.κ hκ
  refine ⟨cζ, hcζ, ?_⟩
  intro ε hε
  obtain ⟨α, hα, N₀, hjet⟩ := hfit (ε / 4) (by positivity)
  refine ⟨α, hα, ?_⟩
  have hM₁ : 1 ≤ M := (by norm_num : 1 ≤ 2).trans hM
  filter_upwards [hNt.eventually (eventually_ge_atTop N₀),
    eventually_jet_fit_to_discovery_slack (fun k => D.T k 1)
      hN hNt hH hK hκ hε hscale hM₁] with k hkN hslack
  intro B G E w hsmall hlow hhigh hfloor
  obtain ⟨p, hp, P, hP⟩ := hjet (D.N k) hkN ScalarLine
    (Zoom.prior w.θ w.ρ w.q) (Zoom.coeff w.ρ w.q) w.event w.F
    (fun r l => cell (w.β r) l.2) w.K w.ζ (D.T k 1)
    hsmall hlow hhigh hfloor w.normal
  obtain ⟨i, hgi, ha, ht, hbad⟩ := w.failed p hp
  have hrow := hslack w.event (E k w.g) (fun z => G k w.g (D.phys k B z))
    w.F P p (D.j k 1 i) w.sub hp (w.interior p hp i ht)
    (w.original_coeff p hp) w.graph_error w.row_error hP
  refine ⟨i, p, recoverRowPolynomial p.1 P, ⟨ha, ht⟩, hbad, ?_⟩
  simpa only [hgi] using hrow

end Submission.Obl.k4_scalar_graph_residual_discovery
