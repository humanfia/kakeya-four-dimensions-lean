import Submission.Obl.k4_balanced_native_packet_transport.Definitions

/-!
The two stages of balanced native transport. The geometric stage retains
regular provisional laws and the earlier window certificate. Its extra
mass/frame and tangent/normal conditions are used by analytical capping.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

/-- Native packets before density masks and light-law deletion. Their
budgets are full original priors, and their signal is the native polynomial.
The lower prior/frame bound retains the original initial density factor. -/
def UncappedNativeSample (N K : ℝ) (W : ℕ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) (E : Fin W → Set Inc)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (loss h χ d s m S U f₀ ξ : ℝ) : Prop :=
  ∃ (T C : ℕ) (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Traj) (F : Fin C → Set Inc)
    (lst : Fin W → Obs → Finset (Fin C))
    (offset : Fin C → ℝ) (tangent : Fin C → Fin 3 → ℝ)
    (law : Fin C → Measure Inc)
    (base : Fin C → Obs → EuclideanSpace ℝ (Fin 2))
    (signal : Fin C → Obs → ℝ),
  let q : ℝ := 1 / (2 : ℝ) ^ T
  let t₀ := fun a => ((j a : ℕ) : ℝ) / (2 : ℝ) ^ T
  let expand := fun a (z : Inc) => (z.1, t₀ a + q * z.2)
  let coeff := fun a => nativeCoeff (P (γ a)) (t₀ a) q (offset a) (tangent a) (A a)
  let budget := fun a => ENNReal.ofReal q * ν (γ a) (A a)
  let R := fun a => ENNReal.ofReal (ω (γ a)) * budget a
  K ≤ N ^ loss ∧ (2 : ℝ) ^ T ≤ N ^ (h + loss) ∧ (C : ℝ) ≤ N ^ M ∧
  (∀ a a', a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a')) ∧
  (∀ w o, ((lst w o).card : ℝ) ≤ N ^ loss) ∧
  (∀ w a, MeasurableSet {o | a ∈ lst w o}) ∧
  (∀ a, chart N M D (N ^ loss) T ((j a : ℕ) : ℝ) 0 (B (γ a)) (E (γ a))
    (c a) (u a) (Q a) (P (γ a)) (A a) (F a)
      (∀ p ∈ F a, a ∈ lst (γ a) (obs (B (γ a)) (δ N 1) p))) ∧
  (∀ a, |offset a| ≤ N ^ M ∧ (∀ i, |tangent a i| ≤ N ^ M) ∧ |q⁻¹| ≤ N ^ M) ∧
  (∑ a, R a) ≤ 1 ∧
  (∀ a, RegularScalarLaw N χ d s m S U
      ((ν (γ a) (A a))⁻¹ • (ν (γ a)).restrict (A a)) (law a) (coeff a) ∧
    ENNReal.ofReal (N ^ (-χ)) ≤ law a Set.univ ∧
    Measurable (base a) ∧ Measurable (signal a) ∧
    (∀ᵐ z ∂law a, base a (obs (B (γ a)) (δ N 1) (expand a z)) =
      WithLp.toLp 2 ![z.2, scalarY (coeff a z.1) z.2] ∧
      |scalarX (coeff a z.1) z.2 - signal a (obs (B (γ a)) (δ N 1) (expand a z))| ≤ N ^ (-1 + χ)) ∧
    (∀ᵐ z ∂law a, z.1 ∈ A a) ∧
    budget a • Measure.map (expand a) (law a) ≤ ((ν (γ a)).prod volume).restrict (F a)) ∧
  ENNReal.ofReal (N ^ (-loss)) ≤ ∑ a, R a * law a Set.univ ∧
  WindowCertificate N χ d s m C R law coeff ∧
  ∀ a, ENNReal.ofReal (N ^ (-f₀ - ξ) * |Matrix.det (Q a)|) ≤ ν (γ a) (A a) ∧
    tangent a 0 = 0 ∧
    ∃ (e n : EuclideanSpace ℝ (Fin 2)) (β : ℝ),
      e = WithLp.toLp 2 ![q * tangent a 1, q * tangent a 2] ∧
      ‖e‖ = 1 ∧ ‖n‖ = 1 ∧ inner ℝ e n = 0 ∧
      q / N ^ loss ≤ ‖Matrix.toEuclideanLin (Q a).transpose e‖ ∧
      ∀ l ∈ A a, |inner ℝ n (v l) - β| ≤ N ^ loss * N ^ (-U)

/-- Both the problem and its formats precede the arbitrary later loss.
Relative profile error and lower prior error have the same outer tolerance. -/
def UncappedNativeAvailable (ds kr S η s m U χ h t ξ : ℝ) : Prop :=
  ∃ N K d W ω ν E P B f g G,
    prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧
    kr - t < H N K 1 W ω ν E B f ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ s → |f r - f 0 - ds * r| ≤ ξ) ∧
    ∃ M D : ℕ, ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
      UncappedNativeSample (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k)
        M D loss h χ ds s m (S / 2) U (f 0) ξ

def UncappedAvailability (ds kr S η s m U : ℝ) : Prop :=
  ∀ χ h t ξ : ℝ, 0 < χ → 0 < h → 0 < t → 0 < ξ →
    UncappedNativeAvailable ds kr S η s m U χ h t ξ

def GeometricRefinementStatement : Prop :=
  initialRaw → ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η →
    LocalizedAvailability ds kr S η →
    ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧ U ≤ η ∧
      UncappedAvailability ds kr S η s m U

def AnalyticalCappingStatement : Prop :=
  ∀ ds kr S η s m U : ℝ, 0 ≤ ds → ds < 1 → 0 < S → 0 < η →
    0 < s → s < 1 → s < m → 0 < U → U < m → U ≤ η →
    UncappedAvailability ds kr S η s m U →
    ∀ χ h t : ℝ, 0 < χ → 0 < h → 0 < t →
      NativeSystemAvailable true ds kr S η s m U χ 1 h t

theorem balancedTransport_of_stages (hgeom : GeometricRefinementStatement)
    (hcap : AnalyticalCappingStatement) : BalancedTransportStatement := by
  intro hi ds kr S η hS hη he hl
  obtain ⟨s, m, U, hs, hs₁, hsm, hU, hUm, hUη, hu⟩ := hgeom hi ds kr S η hS hη he hl
  refine ⟨s, m, U, hs, hs₁, hsm, hU, hUm, ?_⟩
  exact hcap ds kr S η s m U he.1 he.2.1 hS hη hs hs₁ hsm hU hUm hUη hu

end
end Submission.Obl.k4_balanced_native_packet_transport
