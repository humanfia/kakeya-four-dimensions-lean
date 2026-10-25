/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/PacketAnalysis.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.PacketData
import Submission.Obl.k4_uncapped_native_capping.OriginalCapTransport
import Submission.Obl.k4_uncapped_native_capping.PacketRestriction

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
noncomputable section

namespace PacketData

variable {W : ℕ}

/-- The analytical clauses before adding pure and angular caps. -/
structure ProvisionalAnalysis (p : PacketData W) (N χ d s m S U : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Traj) (P : Fin W → MvPolynomial (Fin 4) ℝ)
    (B : Fin W → ℝ) : Prop where
  regular : ∀ a, RegularScalarLaw N χ d s m S U
    ((ν (p.γ a) (p.A a))⁻¹ • (ν (p.γ a)).restrict (p.A a)) (p.law a) (p.coeff P a)
  base_measurable : ∀ a, Measurable (p.base a)
  signal_measurable : ∀ a, Measurable (p.signal a)
  observed : ∀ a, ∀ᵐ z ∂p.law a,
    p.base a (Submission.Obl.k4_finite_width_output_exclusion.obs
        (B (p.γ a)) (Submission.Obl.k4_finite_width_output_exclusion.δ N 1) (p.expand a z)) =
        WithLp.toLp 2 ![z.2, scalarY (p.coeff P a z.1) z.2] ∧
      |scalarX (p.coeff P a z.1) z.2 - p.signal a
        (Submission.Obl.k4_finite_width_output_exclusion.obs
          (B (p.γ a)) (Submission.Obl.k4_finite_width_output_exclusion.δ N 1) (p.expand a z))| ≤
        N ^ (-1 + χ)
  assignment_support : ∀ a, ∀ᵐ z ∂p.law a, z.1 ∈ p.A a
  original_domination : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤
    ((ν (p.γ a)).prod volume).restrict (p.F a)
  certificate : WindowCertificate N χ d s m p.C (p.weight ω ν) p.law (p.coeff P)

theorem ProvisionalAnalysis.withLaws {p : PacketData W} {N χ d s m S U : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B)
    (μ : Fin p.C → Measure Inc) (hμ : ∀ a, μ a ≤ p.law a) :
    (p.withLaws μ).ProvisionalAnalysis N χ d s m S U ω ν P B := by
  refine ⟨?_, hp.base_measurable, hp.signal_measurable,
    fun a => (ae_mono (hμ a)) (hp.observed a),
    fun a => (ae_mono (hμ a)) (hp.assignment_support a), ?_, hp.certificate.mono hμ⟩
  · intro a
    obtain ⟨hb, hν, hdom, htime, hcoeff⟩ := hp.regular a
    exact ⟨hb, hν, (hμ a).trans hdom,
      le_antisymm ((hμ a _).trans_eq htime) bot_le, hcoeff⟩
  · intro a
    apply le_trans _ (hp.original_domination a)
    have hmap : Measure.map (p.expand a) (μ a) ≤ Measure.map (p.expand a) (p.law a) :=
      Measure.map_mono (hμ a) (by unfold expand; fun_prop)
    intro S
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (hmap S)

theorem ProvisionalAnalysis.restrictOriginal {p : PacketData W} {N χ d s m S U : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B) (H : Fin W → Set Inc) :
    (p.restrictOriginal H).ProvisionalAnalysis N χ d s m S U ω ν P B :=
  hp.withLaws _ (fun _ => Measure.restrict_le_self)

theorem ProvisionalAnalysis.restrictOriginal_domination
    {p : PacketData W} {N χ d s m S U : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B)
    (H : Fin W → Set Inc) (hH : ∀ w, MeasurableSet (H w)) (a : Fin p.C) :
    p.budget ν a • Measure.map (p.expand a) ((p.restrictOriginal H).law a) ≤
      ((ν (p.γ a)).prod volume).restrict (H (p.γ a) ∩ p.F a) := by
  have hh := original_domination_restrict_preimage (p.law a)
    (((ν (p.γ a)).prod volume).restrict (p.F a)) (p.budget ν a) (p.expand a)
    (by unfold expand; fun_prop) (H (p.γ a)) (hH _) (hp.original_domination a)
  rw [Measure.restrict_restrict (hH _)] at hh
  exact hh

theorem ProvisionalAnalysis.with_caps {p : PacketData W} {N χ d s m S U : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B)
    (hcaps : ∀ a, ScalarCaps N χ d s m S U
      ((ν (p.γ a) (p.A a))⁻¹ • (ν (p.γ a)).restrict (p.A a)) (p.law a) (p.coeff P a)) :
    p.Analysis N χ d s m S U ω ν P B :=
  ⟨hcaps, hp.base_measurable, hp.signal_measurable, hp.observed,
    hp.assignment_support, hp.original_domination, hp.certificate⟩

/-- The original projected estimates complete the provisional analytical
record without changing any geometry, budgets, readers or window references. -/
theorem ProvisionalAnalysis.cap {p : PacketData W} {N χ d s m S U : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B) (hN : 0 < N)
    (hP : ∀ a, (P (p.γ a)).totalDegree ≤ 2)
    (hA : ∀ a, ν (p.γ a) (p.A a) ≠ 0) (hAfin : ∀ a, ν (p.γ a) (p.A a) ≠ ⊤)
    (hv : ∀ a, p.tangent a 0 = 0) (ρ : Fin p.C → Measure Inc)
    (hdom : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤ ρ a)
    (hpure : ∀ (a : Fin p.C) (r : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 ≤ r → r ≤ s → MeasurableSet E →
      ρ a {z | physicalProjection (packetAxis p.q (p.tangent a)) (p.t₀ a)
        (-p.q * p.offset a) p.q z ∈ E ∧
        ⌊MvPolynomial.eval (Submission.Obl.k4_finite_width_output_exclusion.x z.1 z.2)
          (P (p.γ a)) / N ^ (-r)⌋ = j} ≤
          p.budget ν a * ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) * volume E)
    (hangular : ∀ (a : Fin p.C) (r : ℝ) (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 < r → r ≤ U → MeasurableSet E →
      ρ a {z | physicalProjection (packetAxis p.q (p.tangent a)) (p.t₀ a)
        (-p.q * p.offset a) p.q z ∈ E ∧
        ⌊MvPolynomial.eval (Submission.Obl.k4_finite_width_output_exclusion.x z.1 z.2)
          (P (p.γ a)) / N ^ (-s)⌋ = j ∧
        ⌊inner ℝ (packetAxis p.q (p.tangent a))
          (Submission.Obl.k4_finite_width_output_exclusion.v z.1) / N ^ (-r)⌋ = k} ≤
          p.budget ν a * ENNReal.ofReal (N ^ χ * (N ^ (-s)) ^ d * N ^ (-S * r)) * volume E) :
    p.Analysis N χ d s m S U ω ν P B := by
  apply hp.with_caps
  intro a
  exact native_law_caps_of_original_domination hN (ν (p.γ a)) (p.A a)
    (p.t₀ a) p.q (p.offset a) (by unfold q; positivity) (p.tangent a) (hv a)
    (P (p.γ a)) (hP a) (p.law a) (ρ a) (hA a) (hAfin a) (hdom a)
    (hp.assignment_support a) (hp.regular a) (hpure a) (hangular a)

end PacketData
end
end Submission.Obl.k4_uncapped_native_capping
