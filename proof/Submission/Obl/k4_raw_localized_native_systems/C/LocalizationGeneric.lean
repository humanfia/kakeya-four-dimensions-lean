import Submission.Obl.k4_raw_localized_native_systems.C.LocalizationInterfaces

/-
Adapted from this LOT tree, o178, session x0596, `LocalizationGeneric.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Localized native samples with an arbitrary witness certificate

`NativeSystemSample false` with its window certificate replaced by an arbitrary
predicate on the budgets, laws and coefficients.  With the window certificate it is
the original notion (definitionally); the availability notions are monotone in the
certificate.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

/-- A certificate predicate on budgets, laws and coefficients. -/
abbrev CertPred := ∀ (N χ d s m : ℝ) (C : ℕ), (Fin C → ENNReal) → (Fin C → Measure Inc) →
  (Fin C → Traj → Fin 5 → ℝ) → Prop

/-- `NativeSystemSample false` with an arbitrary certificate. -/
def NativeSampleCert (cert : CertPred) (N K : ℝ) (W : ℕ)
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
  cert N χ d s m C R law coeff ∧
  (T = 0 ∧
    (∀ a, tangent a 0 = 0 ∧ (tangent a 1) ^ 2 + (tangent a 2) ^ 2 = 1) ∧
    (∃ g : ℝ, 0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,
      Q a = ![![tangent a 1, -g * tangent a 2],
               ![tangent a 2, g * tangent a 1]]) ∧
    (∑ a, ENNReal.ofReal (ω (γ a)) * ((ν (γ a)).prod volume) (F a)) ≤
      (∑ a, R a * law a Set.univ) + ENNReal.ofReal (N ^ (-a₀)))

theorem nativeSampleCert_window_iff {N K : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ} :
    NativeSampleCert WindowCertificate N K W ω ν E P B M D a₀ w loss h χ d s m S U ↔
      NativeSystemSample false N K W ω ν E P B M D a₀ w loss h χ d s m S U :=
  Iff.rfl

theorem nativeSampleCert_mono {cert cert' : CertPred}
    (hcert : ∀ N χ d s m C R μ b, cert N χ d s m C R μ b → cert' N χ d s m C R μ b)
    {N K : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ}
    (hs : NativeSampleCert cert N K W ω ν E P B M D a₀ w loss h χ d s m S U) :
    NativeSampleCert cert' N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  obtain ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, hs⟩ := hs
  refine ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, ?_⟩
  dsimp only at hs ⊢
  obtain ⟨hK, hT, hC, hd, hl, hlm, hc, hcoef, hR, hlaw, hmass, hsupport, hgeo⟩ := hs
  exact ⟨hK, hT, hC, hd, hl, hlm, hc, hcoef, hR, hlaw, hmass,
    hcert _ _ _ _ _ _ _ _ _ hsupport, hgeo⟩

/-- Availability with an arbitrary certificate. -/
def NativeAvailableCert (cert : CertPred) (ds kr S η s m U χ w h t : ℝ) : Prop :=
  ∃ N K d W ω ν E P B f g G,
    prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧
      kr - t < H N K 1 W ω ν E B f ∧
    ∃ (a₀ : ℝ) (M D : ℕ), 0 < a₀ ∧ ∀ loss : ℝ, 0 < loss → ∃ᶠ k in atTop,
      NativeSampleCert cert (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k)
        M D a₀ w loss h χ ds s m (S / 2) U

def LocalizedCert (cert : CertPred) (ds kr S η : ℝ) : Prop :=
  ∃ s m U : ℝ, 0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧
    ∀ χ w t : ℝ, 0 < χ → 0 < w → 0 < t →
      NativeAvailableCert cert ds kr S η s m U χ w 1 t

theorem localizedCert_window_iff (ds kr S η : ℝ) :
    LocalizedCert WindowCertificate ds kr S η ↔ LocalizedAvailability ds kr S η :=
  Iff.rfl

end

end Submission.Obl.k4_raw_localized_native_systems.C
