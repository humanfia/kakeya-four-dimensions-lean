/- Adapted from this LOT tree, o197, session x0721, SplitInterfaces.lean,
   commit d876ce83 (retaining the original attribution below). -/
import Submission.Obl.k4_raw_localized_native_systems.Definitions

/-! The certificate argument is kept explicit only for the split. All remaining
native-sample clauses are the exact ones named by x0690 in Definitions.lean. -/

namespace Submission.Obl.k4_raw_localized_native_systems

open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false
set_option maxRecDepth 4096

abbrev CertificateType := ∀ (N χ d s m : ℝ) (C : ℕ), (Fin C → ENNReal) → (Fin C → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) → (Fin C → (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ) → Prop

def NativeSampleWith (cert : CertificateType) : ∀ (p₀:Bool) (N K:ℝ) (W:ℕ) (ω:Fin W → ℝ) (ν:Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E:Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P:Fin W → MvPolynomial (Fin 4) ℝ) (B:Fin W → ℝ) (M D:ℕ) (a₀ w loss h χ d s m S U:ℝ),Prop :=
  fun p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U => ∃ (T C:ℕ) (γ:Fin C → Fin W) (j:Fin C → Fin (2 ^ T)) (c u:Fin C → EuclideanSpace ℝ (Fin 2)) (Q:Fin C → Matrix (Fin 2) (Fin 2) ℝ) (A:Fin C → Set (ℕ × (Fin 6 → ℝ))) (F:Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst:Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) (α₀:Fin C → ℝ) (v₀:Fin C → Fin 3 → ℝ) (law:Fin C → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Y₁:Fin C → (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2)) (X₁:Fin C → (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),((fun (q:ℝ) => ((fun t₀ => ((fun e₀ => ((fun b₁ => ((fun r₀ => ((fun R => K ≤ N ^ loss ∧ (2:ℝ) ^ T ≤ N ^ (h + loss) ∧ (C:ℝ) ≤ N ^ M ∧ (∀ a a',a ≠ a' → γ a = γ a' → j a = j a' → Disjoint (A a) (A a')) ∧ (∀ w o,((lst w o).card:ℝ) ≤ N ^ loss) ∧ (∀ w a,MeasurableSet {o | a ∈ lst w o}) ∧ (∀ a,chart N M D (N ^ loss) T ((j a:ℕ):ℝ) 0 (B (γ a)) (E (γ a)) (c a) (u a) (Q a) (P (γ a)) (A a) (F a) (∀ p ∈ F a,a ∈ lst (γ a) (obs (B (γ a)) (δ N 1) p))) ∧ (∀ a,|α₀ a| ≤ N ^ M ∧ (∀ i,|v₀ a i| ≤ N ^ M) ∧ |q⁻¹| ≤ N ^ M) ∧ (∑ a,R a) ≤ 1 ∧ (∀ a,BasicScalarLaw N χ d s m S U ((ν (γ a) (A a))⁻¹ • (ν (γ a)).restrict (A a)) (law a) (b₁ a) ∧ toE (N ^ (-χ)) ≤ law a Set.univ ∧ Measurable (Y₁ a) ∧ Measurable (X₁ a) ∧ (∀ᵐ z ∂law a,Y₁ a (obs (B (γ a)) (δ N 1) (e₀ a z)) = WithLp.toLp 2 ![z.2,scalarY (b₁ a z.1) z.2] ∧ |scalarX (b₁ a z.1) z.2 - X₁ a (obs (B (γ a)) (δ N 1) (e₀ a z))| ≤ N ^ (-1 + χ)) ∧ (∀ᵐ z ∂law a,z.1 ∈ A a) ∧ r₀ a • MeasureTheory.Measure.map (e₀ a) (law a) ≤ ((ν (γ a)).prod MeasureTheory.volume).restrict (F a)) ∧ toE (N ^ (-loss)) ≤ ∑ a,R a * law a Set.univ ∧ cert N χ d s m C R law b₁ ∧ (if false then True else T = 0 ∧ (∀ a,v₀ a 0 = 0 ∧ (v₀ a 1) ^ 2 + (v₀ a 2) ^ 2 = 1) ∧ (∃ g:ℝ,0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,Q a = ![![v₀ a 1,-g * v₀ a 2],![v₀ a 2,g * v₀ a 1]]) ∧ (∑ a,toE (ω (γ a)) * ((ν (γ a)).prod MeasureTheory.volume) (F a)) ≤ (∑ a,R a * law a Set.univ) + toE (N ^ (-a₀)))) (fun a => toE (ω (γ a)) * r₀ a))) (fun a => toE q * ν (γ a) (A a)))) (fun a => nativeCoeff (P (γ a)) (t₀ a) q (α₀ a) (v₀ a) (A a)))) (fun a (z:((ℕ × (Fin 6 → ℝ)) × ℝ)) => (z.1,t₀ a + q * z.2)))) (fun a => ((j a:ℕ):ℝ) / (2:ℝ) ^ T))) (1 / (2:ℝ) ^ T))

def NativeAvailableWith (cert : CertificateType) : ∀ (p₀:Bool) (ds kr S η s m U χ w h t:ℝ),Prop :=
  fun p₀ ds kr S η s m U χ w h t => ∃ N K d W ω ν E P B f g G,prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < H N K 1 W ω ν E B f ∧ ∃ (a₀:ℝ) (M D:ℕ),0 < a₀ ∧ ∀ loss:ℝ,0 < loss → ∃ᶠ k in Filter.atTop,NativeSampleWith cert p₀ (N k) (K k) (W k) (ω k) (ν k) (E k) (P k) (B k) M D a₀ w loss h χ ds s m (S / 2) U

def LocalizedSystemsWith (cert : CertificateType) : ∀ (ds kr S η:ℝ),Prop :=
  fun ds kr S η => ∃ s m U:ℝ,0 < s ∧ s < 1 ∧ s < m ∧ 0 < U ∧ U < m ∧ ∀ χ w t:ℝ,0 < χ → 0 < w → 0 < t → NativeAvailableWith cert false ds kr S η s m U χ w 1 t

theorem nativeSampleWith_mono {cert cert' : CertificateType}
    (hcert : ∀ N χ d s m C R μ b, cert N χ d s m C R μ b → cert' N χ d s m C R μ b)
    {p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U}
    (hs : NativeSampleWith cert p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U) :
    NativeSampleWith cert' p₀ N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  obtain ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, hs⟩ := hs
  refine ⟨T, C, γ, j, c, u, Q, A, F, lst, α, v, law, Y, X, ?_⟩
  dsimp only at hs ⊢
  obtain ⟨hK, hT, hC, hd, hl, hlm, hc, hcoef, hR, hlaw, hmass, hsupport, hgeo⟩ := hs
  exact ⟨hK, hT, hC, hd, hl, hlm, hc, hcoef, hR, hlaw, hmass,
    hcert _ _ _ _ _ _ _ _ _ hsupport, hgeo⟩

theorem nativeAvailableWith_mono {cert cert' : CertificateType}
    (hcert : ∀ N χ d s m C R μ b, cert N χ d s m C R μ b → cert' N χ d s m C R μ b)
    {p₀ ds kr S η s m U χ w h t}
    (hs : NativeAvailableWith cert p₀ ds kr S η s m U χ w h t) :
    NativeAvailableWith cert' p₀ ds kr S η s m U χ w h t := by
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, a₀, M, D, ha, hsample⟩ := hs
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, a₀, M, D, ha, ?_⟩
  intro loss hloss
  exact (hsample loss hloss).mono fun _ hk => nativeSampleWith_mono hcert hk

theorem localizedSystemsWith_mono {cert cert' : CertificateType}
    (hcert : ∀ N χ d s m C R μ b, cert N χ d s m C R μ b → cert' N χ d s m C R μ b)
    {ds kr S η} (hs : LocalizedSystemsWith cert ds kr S η) :
    LocalizedSystemsWith cert' ds kr S η := by
  obtain ⟨s, m, U, hs0, hs1, hsm, hU0, hUm, hall⟩ := hs
  refine ⟨s, m, U, hs0, hs1, hsm, hU0, hUm, ?_⟩
  intro χ w t hχ hw ht
  exact nativeAvailableWith_mono hcert (hall χ w t hχ hw ht)

theorem localizedSystemsWith_support_iff (ds kr S η : ℝ) :
    LocalizedSystemsWith SupportCertificate ds kr S η ↔ LocalizedSystems ds kr S η := Iff.rfl

end
end Submission.Obl.k4_raw_localized_native_systems
