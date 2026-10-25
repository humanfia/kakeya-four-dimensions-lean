-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Clauses, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The clause groups of the relative row packet (session x1088).

x1080's `RelativeRowPacket` (`O204/Tangent/RowTransport.lean`) is the certificate the relative
source must produce at a packet `b` below an ancestor block `A`.  Its clauses fall into groups
that different producers supply:

* `ScalarClauses`: the scalar constraints on `K, ε, pv, θ` (the relative scales);
* `PointClauses`: assignment, blocks, base and velocity bounds, jets and floor of `RA`;
* `CapClauses`: base ceiling, band cap and census for the signal `RA / aB` (monotone in `Se`);
* `StateClauses`: states refining the physical code, per-state breadth, one palette;
* `RowClauses`: bounded rows, rows fitting the rate of `RA`, coarse row lists over `Er`;
* `QualClauses`: the qualification failure set is small.

`relativeRowPacket_of_clauses` packs them.  The restriction lemmas say which groups survive
passing to a smaller event set: `PointClauses` and `CapClauses` to every measurable subset,
`StateClauses` to every union of whole states (`Se ∩ st ⁻¹' S`), `RowClauses` to every subset. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.NaturalCore

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

noncomputable section

/-- The scalar clauses of the relative row packet. -/
def ScalarClauses (Ep : ℕ) (Nk L gain loss ζ κ K ε pv θ a' h' : ℝ) : Prop :=
  0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a' / h') * ζ ∧ 0 < a' ∧ a' ≤ K * h' ∧ h' ≤ ζ ∧ ζ ≤ 1 ∧ 2 ≤ K ∧
    κ ≤ K ∧ K ^ Ep ≤ Nk ^ (loss * gain * L) ∧ θ = (a' / h') * ζ ^ Ep / K ^ Ep ∧
    K ^ Ep * ε ≤ θ ∧ 0 < pv ∧ K ^ Ep * pv ≤ θ

/-- The pointwise clauses at the events of `Se`: assignment and blocks of `b`, the block of
the ancestor, base and velocity bounds, the jets of `RA` over the ancestor block and its
hidden floor. -/
def PointClauses (K aA B t₀ q hb : ℝ) (jb : ℕ) (RA : Po) (zb : Ev → P3) (Ab : Set Ln)
    (Se : Set Ev) : Prop :=
  ∀ p ∈ Se, (p.1 ∈ Ab ∧ p.2 ∈ Set.Icc ((jb : ℝ) * hb) (((jb : ℝ) + 1) * hb) ∧
      p.2 ∈ Set.Icc t₀ (t₀ + q)) ∧
    ‖zb p‖ ≤ K ∧ ‖O204.Split.v p.1‖ ≤ K ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + q), |MvPolynomial.eval (xp p.1 t) RA| ≤ K * aA ∧
        |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 RA)| ≤ K * B ∧
        |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 RA))| ≤
          K * B ^ 2 / aA) ∧
      B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 RA)|

/-- The non-potential caps: base ceiling, band cap and census of `(zb, Xnb)`. -/
def CapClauses (K ε d₁ h' a' : ℝ) (ref : ENNReal) (ν : Measure Ln) (zb : Ev → P3)
    (Xnb : Ev → ℝ) (Se : Set Ev) : Prop :=
  (∀ U : Set P3, MeasurableSet U →
      ((ν.prod volume).restrict Se) {p | zb p ∈ U} ≤ ENNReal.ofReal K * ref * volume U) ∧
    (∀ w : ℝ, ε ≤ w → w ≤ 1 → ∀ U : Set P3, MeasurableSet U → ∀ f : P3 → ℝ, Measurable f →
      ((ν.prod volume).restrict Se) {p | zb p ∈ U ∧ |Xnb p - f (zb p)| ≤ w} ≤
        ENNReal.ofReal (K * w ^ d₁) * ref * volume U) ∧
    (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h' * p ≤ a' * w →
      Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊zb e i / p⌋, ⌊Xnb e / w⌋)) e = k} ∧
      (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊zb e i / p⌋, ⌊Xnb e / w⌋)) e = k}).ncard : ℝ) ≤
          K / (p ^ (3 : ℕ) * w ^ d₁))

/-- The state clauses: states refining the physical code at mesh `ε`, strip breadth of the
original velocity in every state, and domination of every state's velocity bins at mesh `pv`
by one probability palette. -/
def StateClauses (K ε pv : ℝ) (ν : Measure Ln) (zb : Ev → P3) (Xnb : Ev → ℝ) (Se : Set Ev)
    (st : Ev → ℕ) (pal : Measure (Fin 2 → ℤ)) : Prop :=
  MeasurableSet Se ∧ Measurable st ∧ (st '' Se).Finite ∧
    (∀ p p' : Ev, st p = st p' → physicalCode zb Xnb ε p = physicalCode zb Xnb ε p') ∧
    (∀ k : ℕ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict Se)
          {p | st p = k ∧ |inner ℝ n (O204.Split.v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
        (1 / 2000000000000 : ENNReal) * ((ν.prod volume).restrict Se) {p | st p = k}) ∧
    IsProbabilityMeasure pal ∧
    (∀ k : ℕ, ∀ b : Fin 2 → ℤ,
      ((ν.prod volume).restrict Se)
          {p | st p = k ∧ (fun i : Fin 2 => ⌊O204.Split.v p.1 i / pv⌋) = b} ≤
        ENNReal.ofReal K * ((ν.prod volume).restrict Se) {p | st p = k} * pal {b})

/-- The row clauses: bounded rows, rows fitting the original line rate of `RA` within
`(aA/q) θ` on `Se`, and at most `K` row bins at mesh `(aA/q) θ` over every base cube of side
`θ`, on the qualification reference `Er`. -/
def RowClauses (K θ aA q : ℝ) (RA : Po) (zb : Ev → P3) (Se Er : Set Ev) (st : Ev → ℕ)
    (G : ℕ → Fin 3 → ℝ) : Prop :=
  (∀ k : ℕ, ∀ i : Fin 3, |G k i| ≤ K * (aA / q)) ∧
    (∀ p ∈ Se, |Submission.Lib.K4GlobalParentSignal.rate RA p.1 p.2 -
      ∑ i : Fin 3, (![1, p.1.2 3, p.1.2 4] : Fin 3 → ℝ) i * G (st p) i| ≤ (aA / q) * θ) ∧
    (∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧ ∀ p ∈ Er,
      (∀ i : Fin 3, |zb p i - c' i| ≤ θ) →
        (fun i : Fin 3 => ⌊G (st p) i / ((aA / q) * θ)⌋) ∈ Fc)

/-- The events of `Se` whose rows are NOT qualified by a polynomial of degree `M` along a
time set of measure `≥ 1/K` of their line in the reference `Er`. -/
def unqualified (M : ℕ) (K θ aA q : ℝ) (jb : ℕ) (hb : ℝ) (Se Er : Set Ev) (st : Ev → ℕ)
    (G : ℕ → Fin 3 → ℝ) : Set Ev :=
  {w | w ∈ Se ∧ ¬ ∃ Pq : Fin 3 → Polynomial ℝ, (∀ i, (Pq i).natDegree ≤ M) ∧
    (∀ i n, |(Pq i).coeff n| ≤ K * (aA / q)) ∧
    (∀ i, |G (st w) i - (Pq i).eval ((w.2 - (jb : ℝ) * hb) / hb)| ≤ (aA / q) * θ) ∧
    ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ Set.Icc (0 : ℝ) 1 ∧
      ENNReal.ofReal (1 / K) ≤ volume Et ∧ ∀ s ∈ Et, ((w.1, (jb : ℝ) * hb + hb * s) : Ev) ∈ Er ∧
        ∀ i, |G (st (w.1, (jb : ℝ) * hb + hb * s)) i - (Pq i).eval s| ≤ (aA / q) * θ}

/-- The qualification clause: a measurable cover `bad` of the unqualified events of `Se`
carrying at most `1/10000` of the mass of `Se`. -/
def QualClauses (M : ℕ) (K θ aA q : ℝ) (jb : ℕ) (hb : ℝ) (ν : Measure Ln) (Se Er bad : Set Ev)
    (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ) : Prop :=
  MeasurableSet bad ∧ unqualified M K θ aA q jb hb Se Er st G ⊆ bad ∧
    ((ν.prod volume).restrict Se) bad ≤
      (1 / 10000 : ENNReal) * ((ν.prod volume).restrict Se) Set.univ

/-- **Packing.** The clause groups give x1080's `RelativeRowPacket`. -/
theorem relativeRowPacket_of_clauses (M Ep : ℕ) (precision loss Nk L d₁ gain κ : ℝ)
    (ν : Measure Ln) (B : ℝ) (TA jA : ℕ) (aA : ℝ) (RA : Po) (T' j' : ℕ) (cb ub : P2)
    (aB a' : ℝ) (Ab : Set Ln) (Fb H : Set Ev)
    (K ε pv θ : ℝ) (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ)
    (pal : Measure (Fin 2 → ℤ))
    (hsc : ScalarClauses Ep Nk L gain loss (O204.Split.δ Nk (precision * gain * L)) κ K ε pv θ a'
      ((2 : ℝ) ^ T')⁻¹)
    (hSe : Se ⊆ H ∩ Fb) (hEr : Se ⊆ Er)
    (hpt : PointClauses K aA B ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) ((2 : ℝ) ^ TA)⁻¹
      ((2 : ℝ) ^ (TA + T'))⁻¹ (jA * 2 ^ T' + j') RA
      (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub) Ab Se)
    (href : 0 < ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab)
    (hmass : (ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab) / ENNReal.ofReal K ≤
      ((ν.prod volume).restrict Se) Set.univ)
    (hcap : CapClauses K ε d₁ ((2 : ℝ) ^ T')⁻¹ a'
      (ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab) ν
      (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub) (fun p => packetSignal RA p / aB) Se)
    (hst : StateClauses K ε pv ν (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub)
      (fun p => packetSignal RA p / aB) Se st pal)
    (hrow : RowClauses K θ aA ((2 : ℝ) ^ TA)⁻¹ RA
      (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub) Se Er st G)
    (hq : QualClauses M K θ aA ((2 : ℝ) ^ TA)⁻¹ (jA * 2 ^ T' + j') ((2 : ℝ) ^ (TA + T'))⁻¹ ν
      Se Er bad st G) :
    RelativeRowPacket M Ep precision loss Nk L d₁ gain κ ν B TA jA aA RA T' j' cb ub aB a' Ab
      Fb H := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hsc
  obtain ⟨hb1, hb2, hb3⟩ := hcap
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hst
  obtain ⟨hr1, hr2, hr3⟩ := hrow
  obtain ⟨hq1, hq2, hq3⟩ := hq
  exact ⟨K, ε, pv, θ, Se, Er, bad, st, G, pal, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, hs1, hSe, hEr, fun p hp => (hpt p hp).1, href, hmass,
    fun p hp => (hpt p hp).2, hb1, hb2, hb3, hs2, hs3, hs4, hs5, hs6, hs7, hr1, hr2, hr3, hq1,
    hq2, hq3⟩

/-! ## Restriction -/

/-- Pointwise clauses pass to subsets. -/
theorem PointClauses.mono {K aA B t₀ q hb : ℝ} {jb : ℕ} {RA : Po} {zb : Ev → P3} {Ab : Set Ln}
    {Se Se' : Set Ev} (h : PointClauses K aA B t₀ q hb jb RA zb Ab Se) (hsub : Se' ⊆ Se) :
    PointClauses K aA B t₀ q hb jb RA zb Ab Se' :=
  fun p hp => h p (hsub hp)

/-- Caps pass to measurable subsets. -/
theorem CapClauses.mono {K ε d₁ h' a' : ℝ} {ref : ENNReal} {ν : Measure Ln} {zb : Ev → P3}
    {Xnb : Ev → ℝ} {Se Se' : Set Ev} (h : CapClauses K ε d₁ h' a' ref ν zb Xnb Se)
    (hsub : Se' ⊆ Se) : CapClauses K ε d₁ h' a' ref ν zb Xnb Se' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun U hU => le_trans (Measure.restrict_mono hsub le_rfl _) (h1 U hU),
    fun w hw hw1 U hU f hf => le_trans (Measure.restrict_mono hsub le_rfl _) (h2 w hw hw1 U hU f hf),
    fun pm w hp hp1 hw hw1 hrel => ?_⟩
  obtain ⟨hfin, hcard⟩ := h3 pm w hp hp1 hw hw1 hrel
  have hsubk : {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se',
      (fun e => (fun i : Fin 3 => ⌊zb e i / pm⌋, ⌊Xnb e / w⌋)) e = k} ⊆
      {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
        (fun e => (fun i : Fin 3 => ⌊zb e i / pm⌋, ⌊Xnb e / w⌋)) e = k} := by
    rintro k ⟨e, he, hek⟩
    exact ⟨e, hsub he, hek⟩
  refine ⟨hfin.subset hsubk, le_trans ?_ hcard⟩
  exact_mod_cast Set.ncard_le_ncard hsubk hfin

/-- Rows pass to subsets of `Se` (the lists live on `Er`). -/
theorem RowClauses.mono {K θ aA q : ℝ} {RA : Po} {zb : Ev → P3} {Se Se' Er : Set Ev}
    {st : Ev → ℕ} {G : ℕ → Fin 3 → ℝ} (h : RowClauses K θ aA q RA zb Se Er st G)
    (hsub : Se' ⊆ Se) : RowClauses K θ aA q RA zb Se' Er st G :=
  ⟨h.1, fun p hp => h.2.1 p (hsub hp), h.2.2⟩

/-- The restricted mass of a kept state is unchanged. -/
theorem restrict_state_mem {ν : Measure Ln} {Se : Set Ev} {st : Ev → ℕ} (S : Set ℕ)
    (hSe : MeasurableSet Se) (hst : Measurable st) {k : ℕ} (hk : k ∈ S) (X : Set Ev) :
    ((ν.prod volume).restrict (Se ∩ st ⁻¹' S)) {p | st p = k ∧ p ∈ X} =
      ((ν.prod volume).restrict Se) {p | st p = k ∧ p ∈ X} := by
  have hS' : MeasurableSet (Se ∩ st ⁻¹' S) :=
    hSe.inter (hst (Set.to_countable S).measurableSet)
  rw [Measure.restrict_apply' hS', Measure.restrict_apply' hSe]
  congr 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨⟨h1, h1'⟩, h2, -⟩; exact ⟨⟨h1, h1'⟩, h2⟩
  · rintro ⟨⟨h1, h1'⟩, h2⟩; exact ⟨⟨h1, h1'⟩, h2, h1 ▸ hk⟩

/-- A dropped state has restricted mass zero. -/
theorem restrict_state_not_mem {ν : Measure Ln} {Se : Set Ev} {st : Ev → ℕ} (S : Set ℕ)
    (hSe : MeasurableSet Se) (hst : Measurable st) {k : ℕ} (hk : k ∉ S) (X : Set Ev) :
    ((ν.prod volume).restrict (Se ∩ st ⁻¹' S)) {p | st p = k ∧ p ∈ X} = 0 := by
  have hS' : MeasurableSet (Se ∩ st ⁻¹' S) :=
    hSe.inter (hst (Set.to_countable S).measurableSet)
  rw [Measure.restrict_apply' hS']
  have : {p : Ev | st p = k ∧ p ∈ X} ∩ (Se ∩ st ⁻¹' S) = ∅ := by
    ext p
    constructor
    · rintro ⟨⟨h1, -⟩, -, h3⟩
      exact absurd (h1 ▸ h3) hk
    · intro h
      exact absurd h (Set.notMem_empty p)
  rw [this, measure_empty]

/-- **State clauses pass to unions of whole states.** -/
theorem StateClauses.restrict {K ε pv : ℝ} {ν : Measure Ln} {zb : Ev → P3} {Xnb : Ev → ℝ}
    {Se : Set Ev} {st : Ev → ℕ} {pal : Measure (Fin 2 → ℤ)}
    (h : StateClauses K ε pv ν zb Xnb Se st pal) (S : Set ℕ) :
    StateClauses K ε pv ν zb Xnb (Se ∩ st ⁻¹' S) st pal := by
  obtain ⟨hSe, hst, hfin, hcode, hbr, hpal, hdom⟩ := h
  have hS' : MeasurableSet (Se ∩ st ⁻¹' S) :=
    hSe.inter (hst (Set.to_countable S).measurableSet)
  refine ⟨hS', hst, hfin.subset (Set.image_mono Set.inter_subset_left), hcode, ?_, hpal, ?_⟩
  · intro k n t hn
    by_cases hk : k ∈ S
    · have h1 := restrict_state_mem (ν := ν) S hSe hst hk
        {p | |inner ℝ n (O204.Split.v p.1) - t| ≤ K ^ (-100 : ℝ)}
      have h2 := restrict_state_mem (ν := ν) S hSe hst hk Set.univ
      simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true] at h1 h2
      rw [h1, h2]
      exact hbr k n t hn
    · have h1 := restrict_state_not_mem (ν := ν) S hSe hst hk
        {p | |inner ℝ n (O204.Split.v p.1) - t| ≤ K ^ (-100 : ℝ)}
      simp only [Set.mem_ofPred_eq] at h1
      rw [h1]
      exact zero_le
  · intro k b
    by_cases hk : k ∈ S
    · have h1 := restrict_state_mem (ν := ν) S hSe hst hk
        {p | (fun i : Fin 2 => ⌊O204.Split.v p.1 i / pv⌋) = b}
      have h2 := restrict_state_mem (ν := ν) S hSe hst hk Set.univ
      simp only [Set.mem_ofPred_eq, Set.mem_univ, and_true] at h1 h2
      rw [h1, h2]
      exact hdom k b
    · have h1 := restrict_state_not_mem (ν := ν) S hSe hst hk
        {p | (fun i : Fin 2 => ⌊O204.Split.v p.1 i / pv⌋) = b}
      simp only [Set.mem_ofPred_eq] at h1
      rw [h1]
      exact zero_le

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
