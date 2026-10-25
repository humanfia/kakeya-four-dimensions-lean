/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/PacketData.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.Definitions
import Submission.Obl.k4_uncapped_native_capping.WindowSelection
import Submission.Obl.k4_coarsened_outer_horizon_composition.Finish

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- The original geometric arrays and their auxiliary analytical laws. -/
structure PacketData (W : ℕ) where
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

namespace PacketData

variable {W : ℕ}

def q (p : PacketData W) : ℝ := 1 / (2 : ℝ) ^ p.T
def t₀ (p : PacketData W) (a : Fin p.C) : ℝ := ((p.j a : ℕ) : ℝ) / (2 : ℝ) ^ p.T
def expand (p : PacketData W) (a : Fin p.C) (z : Inc) : Inc := (z.1, p.t₀ a + p.q * z.2)
def coeff (p : PacketData W) (P : Fin W → MvPolynomial (Fin 4) ℝ) (a : Fin p.C) :=
  nativeCoeff (P (p.γ a)) (p.t₀ a) p.q (p.offset a) (p.tangent a) (p.A a)
def budget (p : PacketData W) (ν : Fin W → Measure Traj) (a : Fin p.C) : ENNReal :=
  ENNReal.ofReal p.q * ν (p.γ a) (p.A a)
def weight (p : PacketData W) (ω : Fin W → ℝ) (ν : Fin W → Measure Traj)
    (a : Fin p.C) : ENNReal := ENNReal.ofReal (ω (p.γ a)) * p.budget ν a
def mass (p : PacketData W) (ω : Fin W → ℝ) (ν : Fin W → Measure Traj) : ENNReal :=
  ∑ a, p.weight ω ν a * p.law a univ

structure Geometry (p : PacketData W) (N K : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Traj) (E : Fin W → Set Inc)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (loss h : ℝ) : Prop where
  ambient : K ≤ N ^ loss
  time : (2 : ℝ) ^ p.T ≤ N ^ (h + loss)
  count : (p.C : ℝ) ≤ N ^ M
  separated : ∀ a a', a ≠ a' → p.γ a = p.γ a' → p.j a = p.j a' → Disjoint (p.A a) (p.A a')
  list_bound : ∀ w o, ((p.lst w o).card : ℝ) ≤ N ^ loss
  list_measurable : ∀ w a, MeasurableSet {o | a ∈ p.lst w o}
  charts : ∀ a, chart N M D (N ^ loss) p.T ((p.j a : ℕ) : ℝ) 0 (B (p.γ a))
    (E (p.γ a)) (p.c a) (p.u a) (p.Q a) (P (p.γ a)) (p.A a) (p.F a)
    (∀ z ∈ p.F a, a ∈ p.lst (p.γ a) (obs (B (p.γ a)) (δ N 1) z))
  coordinates : ∀ a, |p.offset a| ≤ N ^ M ∧ (∀ i, |p.tangent a i| ≤ N ^ M) ∧ |p.q⁻¹| ≤ N ^ M
  budget_sum : (∑ a, p.weight ω ν a) ≤ 1

structure Analysis (p : PacketData W) (N χ d s m S U : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Traj) (P : Fin W → MvPolynomial (Fin 4) ℝ)
    (B : Fin W → ℝ) : Prop where
  caps : ∀ a, ScalarCaps N χ d s m S U
    ((ν (p.γ a) (p.A a))⁻¹ • (ν (p.γ a)).restrict (p.A a)) (p.law a) (p.coeff P a)
  base_measurable : ∀ a, Measurable (p.base a)
  signal_measurable : ∀ a, Measurable (p.signal a)
  observed : ∀ a, ∀ᵐ z ∂p.law a,
    p.base a (obs (B (p.γ a)) (δ N 1) (p.expand a z)) =
        WithLp.toLp 2 ![z.2, scalarY (p.coeff P a z.1) z.2] ∧
      |scalarX (p.coeff P a z.1) z.2 - p.signal a (obs (B (p.γ a)) (δ N 1) (p.expand a z))| ≤
        N ^ (-1 + χ)
  assignment_support : ∀ a, ∀ᵐ z ∂p.law a, z.1 ∈ p.A a
  original_domination : ∀ a, p.budget ν a • Measure.map (p.expand a) (p.law a) ≤
    ((ν (p.γ a)).prod volume).restrict (p.F a)
  certificate : WindowCertificate N χ d s m p.C (p.weight ω ν) p.law (p.coeff P)

/-- Subselect whole packets while keeping their full original priors. -/
def reindex (p : PacketData W) {C' : ℕ} (e : Fin C' ↪ Fin p.C) : PacketData W := by
  classical
  exact {
    T := p.T
    C := C'
    γ := p.γ ∘ e
    j := p.j ∘ e
    c := p.c ∘ e
    u := p.u ∘ e
    Q := p.Q ∘ e
    A := p.A ∘ e
    F := p.F ∘ e
    lst w o := @Finset.filter (Fin C') (fun a => e a ∈ p.lst w o)
      (fun _ => Classical.propDecidable _) Finset.univ
    offset := p.offset ∘ e
    tangent := p.tangent ∘ e
    law := p.law ∘ e
    base := p.base ∘ e
    signal := p.signal ∘ e
  }

theorem mem_reindex_list (p : PacketData W) {C' : ℕ} (e : Fin C' ↪ Fin p.C)
    (w : Fin W) (o : Obs) (a : Fin C') :
    a ∈ (p.reindex e).lst w o ↔ e a ∈ p.lst w o := by
  classical
  exact (@Finset.mem_filter (Fin C') (fun i => e i ∈ p.lst w o)
    (fun _ => Classical.propDecidable _) Finset.univ a).trans (by simp)

theorem Geometry.reindex {p : PacketData W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h : ℝ} (hp : p.Geometry N K ω ν E P B M D loss h)
    {C' : ℕ} (e : Fin C' ↪ Fin p.C) :
    (p.reindex e).Geometry N K ω ν E P B M D loss h := by
  classical
  refine ⟨hp.ambient, hp.time, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : C' ≤ p.C := by simpa using Fintype.card_le_of_injective e e.injective
    exact (Nat.cast_le.mpr hc).trans hp.count
  · intro a a' hne hγ hj
    exact hp.separated (e a) (e a') (fun heq => hne (e.injective heq)) hγ hj
  · intro w o
    let F := (p.reindex e).lst w o
    have hs : F.image e ⊆ p.lst w o := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact (mem_reindex_list p e w o i).mp hi
    have hc : F.card ≤ (p.lst w o).card := by
      rw [← Finset.card_image_of_injective F e.injective]
      exact Finset.card_le_card hs
    exact (Nat.cast_le.mpr hc).trans (hp.list_bound w o)
  · intro w a
    have heq : {o | a ∈ (p.reindex e).lst w o} = {o | e a ∈ p.lst w o} := by
      ext o
      exact mem_reindex_list p e w o a
    rw [heq]
    exact hp.list_measurable w (e a)
  · intro a
    exact Submission.Obl.k4_coarsened_outer_horizon_composition.chart_extra_mono
      (fun hk z hz => (mem_reindex_list p e _ _ a).mpr (hk z hz))
      (hp.charts (e a))
  · intro a
    exact hp.coordinates (e a)
  · change (∑ a, p.weight ω ν (e a)) ≤ 1
    apply le_trans _ hp.budget_sum
    calc
      _ = ∑ a ∈ Finset.univ.image e, p.weight ω ν a := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ heq => e.injective heq
      _ ≤ ∑ a, p.weight ω ν a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => bot_le)

theorem Analysis.reindex {p : PacketData W} {N χ d s m S U : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.Analysis N χ d s m S U ω ν P B) {C' : ℕ} (e : Fin C' ↪ Fin p.C) :
    (p.reindex e).Analysis N χ d s m S U ω ν P B := by
  refine ⟨fun a => hp.caps (e a), fun a => hp.base_measurable (e a),
    fun a => hp.signal_measurable (e a), fun a => hp.observed (e a),
    fun a => hp.assignment_support (e a), fun a => hp.original_domination (e a), ?_⟩
  exact hp.certificate.reindex e

/-- With its law floors and total mass, the record is exactly the frozen
balanced native packet sample. -/
theorem to_sample (p : PacketData W) {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ}
    (hg : p.Geometry N K ω ν E P B M D loss h)
    (ha : p.Analysis N χ d s m S U ω ν P B)
    (hfloor : ∀ a, ENNReal.ofReal (N ^ (-χ)) ≤ p.law a univ)
    (hmass : ENNReal.ofReal (N ^ (-loss)) ≤ p.mass ω ν) :
    NativeSystemSample true N K W ω ν E P B M D a₀ w loss h χ d s m S U := by
  refine ⟨p.T, p.C, p.γ, p.j, p.c, p.u, p.Q, p.A, p.F, p.lst, p.offset, p.tangent,
    p.law, p.base, p.signal, hg.ambient, hg.time, hg.count, hg.separated,
    hg.list_bound, hg.list_measurable, hg.charts, hg.coordinates, hg.budget_sum,
    ?_, hmass, ha.certificate, trivial⟩
  intro a
  exact ⟨ha.caps a, hfloor a, ha.base_measurable a, ha.signal_measurable a,
    ha.observed a, ha.assignment_support a, ha.original_domination a⟩

end PacketData
end
end Submission.Obl.k4_uncapped_native_capping
