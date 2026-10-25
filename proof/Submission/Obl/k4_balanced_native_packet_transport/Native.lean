import Submission.Obl.k4_balanced_native_packet_transport.Definitions

/-!
The witnesses of one native system sample, bundled in a structure. The
predicate `NativeSample.Holds` is the body of `NativeSystemSample`, so the two
formulations agree by repackaging only.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

/-- All witnesses of `NativeSystemSample`, for `W` worlds. -/
structure NativeSample (W : ℕ) where
  T : ℕ
  C : ℕ
  γ : Fin C → Fin W
  j : Fin C → Fin (2 ^ T)
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  u : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  A : Fin C → Set Traj
  F : Fin C → Set Inc
  lst : Fin W → Obs → Finset (Fin C)
  offset : Fin C → ℝ
  tangent : Fin C → Fin 3 → ℝ
  law : Fin C → Measure Inc
  base : Fin C → Obs → EuclideanSpace ℝ (Fin 2)
  signal : Fin C → Obs → ℝ

/-- The body of `NativeSystemSample` for the bundled witnesses. -/
def NativeSample.Holds {W : ℕ} (σ : NativeSample W) (balanced : Bool) (N K : ℝ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) (E : Fin W → Set Inc)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (a₀ w loss h χ d s m S U : ℝ) : Prop :=
  let q : ℝ := 1 / (2 : ℝ) ^ σ.T
  let t₀ := fun a => ((σ.j a : ℕ) : ℝ) / (2 : ℝ) ^ σ.T
  let expand := fun a (z : Inc) => (z.1, t₀ a + q * z.2)
  let coeff := fun a => nativeCoeff (P (σ.γ a)) (t₀ a) q (σ.offset a) (σ.tangent a) (σ.A a)
  let budget := fun a => ENNReal.ofReal q * ν (σ.γ a) (σ.A a)
  let R := fun a => ENNReal.ofReal (ω (σ.γ a)) * budget a
  K ≤ N ^ loss ∧ (2 : ℝ) ^ σ.T ≤ N ^ (h + loss) ∧ (σ.C : ℝ) ≤ N ^ M ∧
  (∀ a a', a ≠ a' → σ.γ a = σ.γ a' → σ.j a = σ.j a' → Disjoint (σ.A a) (σ.A a')) ∧
  (∀ w o, ((σ.lst w o).card : ℝ) ≤ N ^ loss) ∧
  (∀ w a, MeasurableSet {o | a ∈ σ.lst w o}) ∧
  (∀ a, chart N M D (N ^ loss) σ.T ((σ.j a : ℕ) : ℝ) 0 (B (σ.γ a)) (E (σ.γ a))
    (σ.c a) (σ.u a) (σ.Q a) (P (σ.γ a)) (σ.A a) (σ.F a)
      (∀ p ∈ σ.F a, a ∈ σ.lst (σ.γ a) (obs (B (σ.γ a)) (δ N 1) p))) ∧
  (∀ a, |σ.offset a| ≤ N ^ M ∧ (∀ i, |σ.tangent a i| ≤ N ^ M) ∧ |q⁻¹| ≤ N ^ M) ∧
  (∑ a, R a) ≤ 1 ∧
  (∀ a, (if balanced then ScalarCaps else RegularScalarLaw) N χ d s m S U
      ((ν (σ.γ a) (σ.A a))⁻¹ • (ν (σ.γ a)).restrict (σ.A a)) (σ.law a) (coeff a) ∧
    ENNReal.ofReal (N ^ (-χ)) ≤ σ.law a Set.univ ∧
    Measurable (σ.base a) ∧ Measurable (σ.signal a) ∧
    (∀ᵐ z ∂σ.law a, σ.base a (obs (B (σ.γ a)) (δ N 1) (expand a z)) =
      WithLp.toLp 2 ![z.2, scalarY (coeff a z.1) z.2] ∧
      |scalarX (coeff a z.1) z.2 - σ.signal a (obs (B (σ.γ a)) (δ N 1) (expand a z))| ≤
        N ^ (-1 + χ)) ∧
    (∀ᵐ z ∂σ.law a, z.1 ∈ σ.A a) ∧
    budget a • Measure.map (expand a) (σ.law a) ≤
      ((ν (σ.γ a)).prod volume).restrict (σ.F a)) ∧
  ENNReal.ofReal (N ^ (-loss)) ≤ ∑ a, R a * σ.law a Set.univ ∧
  WindowCertificate N χ d s m σ.C R σ.law coeff ∧
  (if balanced then True else
    σ.T = 0 ∧
    (∀ a, σ.tangent a 0 = 0 ∧ (σ.tangent a 1) ^ 2 + (σ.tangent a 2) ^ 2 = 1) ∧
    (∃ g : ℝ, 0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,
      σ.Q a = ![![σ.tangent a 1, -g * σ.tangent a 2],
               ![σ.tangent a 2, g * σ.tangent a 1]]) ∧
    (∑ a, ENNReal.ofReal (ω (σ.γ a)) * ((ν (σ.γ a)).prod volume) (σ.F a)) ≤
      (∑ a, R a * σ.law a Set.univ) + ENNReal.ofReal (N ^ (-a₀)))

/-- `NativeSystemSample` is exactly the existence of bundled witnesses. -/
theorem nativeSystemSample_iff {balanced : Bool} {N K : ℝ} {W : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ} :
    NativeSystemSample balanced N K W ω ν E P B M D a₀ w loss h χ d s m S U ↔
      ∃ σ : NativeSample W,
        σ.Holds balanced N K ω ν E P B M D a₀ w loss h χ d s m S U := by
  constructor
  · rintro ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal, h⟩
    exact ⟨⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal⟩, h⟩
  · rintro ⟨⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal⟩, h⟩
    exact ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal, h⟩

end
end Submission.Obl.k4_balanced_native_packet_transport
