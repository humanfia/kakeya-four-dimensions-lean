import Submission.Obl.k4_raw_localized_native_systems.C.PacketInterfaces

/-
Adapted from this LOT tree, o178, session x0596, `LocalizationInterfaces.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
Source: o178/x0639, commit4b06840f, same-obligation LocalizationInterfaces.lean.
Full-time localization and balanced transport are separate geometric steps.
The window certificate records the earlier witnesses before balancing; its
window formulation is preserved when a unit-time block is contracted.
-/
namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section
set_option linter.unusedVariables false
set_option maxRecDepth 4096
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def RegularScalarLaw (N χ d s m S U : ℝ) (ν : Measure Traj) (μ : Measure Inc)
    (b : Traj → Fin 5 → ℝ) : Prop :=
  Measurable b ∧ IsProbabilityMeasure ν ∧
  μ ≤ ENNReal.ofReal (N ^ χ) • (ν.prod volume) ∧
  μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
  (∀ l i, |b l i| ≤ N ^ χ)

def WindowCertificate (N χ d s m : ℝ) (C : ℕ)
    (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (b : Fin C → Traj → Fin 5 → ℝ) : Prop :=
  ∃ (J : ℕ) (w : Fin J → ENNReal)
    (Λ : Fin J → Measure (EuclideanSpace ℝ (Fin 4)))
    (P S : Fin J → MvPolynomial (Fin 4) ℝ)
    (tag : Fin C → Inc → Fin J) (A : Fin C → Set Inc)
    (z : Fin C → Fin J → Inc → EuclideanSpace ℝ (Fin 4)),
  (∑ e, w e) ≤ 1 ∧ 2 ≤ N ^ χ ∧
  (∀ e, IsProbabilityMeasure (Λ e) ∧ (P e).totalDegree ≤ 2 ∧
    (S e).totalDegree ≤ 2 ∧
    Measure.map base4 (Λ e) ≤ ENNReal.ofReal (N ^ χ) • volume ∧
    ∀ᵐ p ∂Λ e,
      ‖base4 p‖ ≤ N ^ χ ∧
      |MvPolynomial.eval (fun i => p i) (P e)| ≤ N ^ χ * N ^ (-s + χ) ∧
      (N ^ χ)⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (P e))| ∧
      |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (P e))| ≤ N ^ χ ∧
      |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (P e)))| ≤ N ^ χ / N ^ (-s + χ) ∧
      |MvPolynomial.eval (fun i => p i) (S e)| ≤ N ^ χ ∧
      |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) (S e))| ≤ N ^ χ ∧
      |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (S e)))| ≤ N ^ χ) ∧
  (∀ a, 0 < R a ∧ Measurable (tag a) ∧ MeasurableSet (A a) ∧
    μ a (A a)ᶜ = 0 ∧ ∀ e, Measurable (z a e)) ∧
  (∀ e, (∑ a, R a • Measure.map (z a e)
      ((μ a).restrict {p | p ∈ A a ∧ tag a p = e})) ≤ w e • Λ e) ∧
  (∀ a p, p ∈ A a → scalarX (b a p.1) p.2 =
    MvPolynomial.eval (fun i => z a (tag a p) p i) (S (tag a p))) ∧
  (∀ a t y, (((Finset.univ : Finset (Fin J)).filter
      (fun e => ∃ p ∈ A a, |p.2 - t| ≤ N ^ (-m) ∧
        |scalarY (b a p.1) p.2 - y| ≤ N ^ (-m) ∧ tag a p = e)).card : ℝ) ≤
      N ^ (d * s + χ)) ∧
  ∀ a p, p ∈ A a → ∀ p', p' ∈ A a → tag a p = tag a p' →
    |p.2 - p'.2| ≤ N ^ (-m) →
    |scalarY (b a p.1) p.2 - scalarY (b a p'.1) p'.2| ≤ N ^ (-m) →
    ‖base4 (z a (tag a p) p) - base4 (z a (tag a p) p')‖ ≤ N ^ (-s + χ)

def NativeSystemSample (balanced : Bool) (N K : ℝ) (W : ℕ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) (E : Fin W → Set Inc)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (a₀ w loss h χ d s m S U : ℝ) : Prop :=
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
  (∀ a, (if balanced then ScalarCaps else RegularScalarLaw) N χ d s m S U
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
  (if balanced then True else
    T = 0 ∧
    (∀ a, tangent a 0 = 0 ∧ (tangent a 1) ^ 2 + (tangent a 2) ^ 2 = 1) ∧
    (∃ g : ℝ, 0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,
      Q a = ![![tangent a 1, -g * tangent a 2],
               ![tangent a 2, g * tangent a 1]]) ∧
    (∑ a, ENNReal.ofReal (ω (γ a)) * ((ν (γ a)).prod volume) (F a)) ≤
      (∑ a, R a * law a Set.univ) + ENNReal.ofReal (N ^ (-a₀)))

/-- The omission exponent and format are fixed before every actual loss.
The complete formatted full-time family stays available for normalization. -/
def NativeSystemAvailable (balanced : Bool)
    (ds kr S η s m U χ w h t : ℝ) : Prop :=
  ∃ N K d W ω ν E P B f g G,
    prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧
      kr - t < H N K 1 W ω ν E B f ∧
    ∃ (a₀ : ℝ) (M D : ℕ), 0 < a₀ ∧ ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
      NativeSystemSample balanced (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k)
        M D a₀ w loss h χ ds s m (S / 2) U

def LocalizedAvailability (ds kr S η : ℝ) : Prop :=
  ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧
    ∀ χ w t : ℝ, 0 < χ → 0 < w → 0 < t →
      NativeSystemAvailable false ds kr S η s m U χ w 1 t

def BalancedAvailability (ds kr S η : ℝ) : Prop :=
  ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧
    ∀ χ h t : ℝ, 0 < χ → 0 < h → 0 < t →
      NativeSystemAvailable true ds kr S η s m U χ 1 h t

def LocalizationStatement : Prop :=
  initialRaw → ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η →
    ¬ widthRaw ds kr S η → LocalizedAvailability ds kr S η

def BalancedTransportStatement : Prop :=
  initialRaw → ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η →
    LocalizedAvailability ds kr S η → BalancedAvailability ds kr S η

end
end Submission.Obl.k4_raw_localized_native_systems.C
