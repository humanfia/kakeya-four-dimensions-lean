/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/PacketRestriction.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.PacketData
import Submission.Obl.k4_uncapped_native_capping.ScalarCapAssembly
import Submission.Lib.K4ChartLifting.NormTerminal

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

namespace PacketData

variable {W : ℕ}

/-- Change only the analytical laws. All original geometric data and budgets
are retained. -/
def withLaws (p : PacketData W) (μ : Fin p.C → Measure Inc) : PacketData W :=
  { p with law := μ }

theorem Geometry.withLaws {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (μ : Fin p.C → Measure Inc) :
    (p.withLaws μ).Geometry N K ω ν E P B M D loss h :=
  ⟨hp.ambient, hp.time, hp.count, hp.separated, hp.list_bound,
    hp.list_measurable, hp.charts, hp.coordinates, hp.budget_sum⟩

theorem Analysis.withLaws {p : PacketData W} {N χ d s m S U : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.Analysis N χ d s m S U ω ν P B)
    (μ : Fin p.C → Measure Inc) (hμ : ∀ a, μ a ≤ p.law a) :
    (p.withLaws μ).Analysis N χ d s m S U ω ν P B := by
  refine ⟨fun a => (hp.caps a).mono (hμ a), hp.base_measurable, hp.signal_measurable,
    fun a => (ae_mono (hμ a)) (hp.observed a),
    fun a => (ae_mono (hμ a)) (hp.assignment_support a), ?_, hp.certificate.mono hμ⟩
  intro a
  apply le_trans _ (hp.original_domination a)
  have hmap : Measure.map (p.expand a) (μ a) ≤ Measure.map (p.expand a) (p.law a) :=
    Measure.map_mono (hμ a) (by unfold expand; fun_prop)
  intro S
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (hmap S)

/-- Restrict the analytical laws by a common original-world event. -/
def restrictOriginal (p : PacketData W) (H : Fin W → Set Inc) : PacketData W :=
  p.withLaws (fun a => (p.law a).restrict (p.expand a ⁻¹' H (p.γ a)))

theorem Geometry.restrictOriginal {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (H : Fin W → Set Inc) :
    (p.restrictOriginal H).Geometry N K ω ν E P B M D loss h := hp.withLaws _

theorem Analysis.restrictOriginal {p : PacketData W} {N χ d s m S U : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.Analysis N χ d s m S U ω ν P B) (H : Fin W → Set Inc) :
    (p.restrictOriginal H).Analysis N χ d s m S U ω ν P B :=
  hp.withLaws _ (fun _ => Measure.restrict_le_self)

/-- Use the accepted original-world chart budget, including closed block
endpoints, to charge a common mask once rather than once per packet. -/
theorem Geometry.weighted_event_le {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (hE : ∀ w, MeasurableSet (E w)) (H : Fin W → Set Inc)
    (hH : ∀ w, MeasurableSet (H w)) :
    (∑ a, ENNReal.ofReal (ω (p.γ a)) *
      ((ν (p.γ a)).prod volume) (p.F a ∩ H (p.γ a))) ≤
      2 * ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (H w) := by
  let cs : Submission.Lib.K4ChartLifting.ChartSystem W p.T := {
    count := p.C
    world := p.γ
    block := p.j
    center := p.c
    speed := p.u
    frame := p.Q
    test := P ∘ p.γ
    assignment := p.A
    event := p.F
  }
  apply cs.weighted_event_le ω ν E hE
  · intro a
    exact (hp.charts a).2.2.2.2.2.2.2.1
  · exact hp.separated
  · intro a z hz
    have hh := (hp.charts a).2.2.2.2.2.2.2.2.2.2.1 z hz
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  · exact hH

theorem weighted_mask_le {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (hdom : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤
      ((ν (p.γ a)).prod volume).restrict (p.F a))
    (hE : ∀ w, MeasurableSet (E w)) (H : Fin W → Set Inc)
    (hH : ∀ w, MeasurableSet (H w)) :
    (∑ a, p.weight ω ν a * p.law a (p.expand a ⁻¹' H (p.γ a))) ≤
      2 * ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (H w) := by
  apply le_trans _ (hp.weighted_event_le hE H hH)
  apply Finset.sum_le_sum
  intro a _
  have hh := hdom a (H (p.γ a))
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by unfold expand; fun_prop) (hH _),
    Measure.restrict_apply (hH _), inter_comm (H _) (p.F a)] at hh
  simpa only [weight, mul_assoc] using
    (mul_le_mul' (le_refl (ENNReal.ofReal (ω (p.γ a)))) hh)

theorem mass_eq_restrictOriginal_add_compl (p : PacketData W) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Traj) (H : Fin W → Set Inc)
    (hH : ∀ w, MeasurableSet (H w)) :
    p.mass ω ν = (p.restrictOriginal H).mass ω ν +
      ∑ a, p.weight ω ν a * p.law a (p.expand a ⁻¹' (H (p.γ a))ᶜ) := by
  change (∑ a, p.weight ω ν a * p.law a univ) =
    (∑ a, p.weight ω ν a * (p.law a).restrict (p.expand a ⁻¹' H (p.γ a)) univ) + _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hm : MeasurableSet (p.expand a ⁻¹' H (p.γ a)) :=
    (hH _).preimage (by unfold expand; fun_prop)
  change p.weight ω ν a * p.law a univ =
    p.weight ω ν a * (p.law a).restrict (p.expand a ⁻¹' H (p.γ a)) univ + _
  rw [Measure.restrict_apply_univ, ← mul_add, preimage_compl,
    measure_add_measure_compl hm]

theorem mass_le_restrictOriginal_add_bad {p : PacketData W} {N K : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (hdom : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤
      ((ν (p.γ a)).prod volume).restrict (p.F a))
    (hE : ∀ w, MeasurableSet (E w)) (H : Fin W → Set Inc)
    (hH : ∀ w, MeasurableSet (H w)) :
    p.mass ω ν ≤ (p.restrictOriginal H).mass ω ν +
      2 * ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) ((H w)ᶜ) := by
  rw [mass_eq_restrictOriginal_add_compl p ω ν H hH]
  exact add_le_add le_rfl (weighted_mask_le hp hdom hE (fun w => (H w)ᶜ)
    (fun w => (hH w).compl))

/-- A power-small original-world exceptional set costs no packet-count
factor. Its loss can be reserved before the later light-law pruning. -/
theorem mass_lower_restrictOriginal {p : PacketData W} {N K : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    (hdom : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤
      ((ν (p.γ a)).prod volume).restrict (p.F a))
    (hE : ∀ w, MeasurableSet (E w)) (H : Fin W → Set Inc)
    (hH : ∀ w, MeasurableSet (H w)) {target bad : ENNReal} (hbad : bad ≠ ⊤)
    (hmask : (∑ w, ENNReal.ofReal (ω w) *
      (((ν w).prod volume).restrict (E w)) ((H w)ᶜ)) ≤ bad)
    (hmass : target + 2 * bad ≤ p.mass ω ν) :
    target ≤ (p.restrictOriginal H).mass ω ν := by
  have hfinite : 2 * bad ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hbad
  apply ENNReal.le_of_add_le_add_right hfinite
  exact hmass.trans ((mass_le_restrictOriginal_add_bad hp hdom hE H hH).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl hmask)))

end PacketData
end
end Submission.Obl.k4_uncapped_native_capping
