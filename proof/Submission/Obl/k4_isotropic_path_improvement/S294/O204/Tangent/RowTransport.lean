-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.RowTransport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/RowTransport.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Forward transport of o295's RowPacket to a tangent packet (x1080, o204).
-- Builds on `Tangent.Forward` (this obligation) and x1078's `Tangent.Frame`.
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Forward

/-!
# `RowPacket` for a tangent packet from original-unit clauses

`RelativeRowPacket` states o295's `RowPacket` clauses at a packet `b` inside a parent block, in
ORIGINAL units, with the parent's own test `RA` as the signal and with precisions RELATIVE to the
parent (relative thickness `aB/aA`, relative time length `2^-T'`). In particular the velocity
palette mesh `pv` is relative: it is `θ/K^Ep` with `θ = (a'/h') ζ^Ep / K^Ep` for the relative
`a'/h'`, not the packet's absolute `a/h` (the obstruction recorded on o294's thread).

`rowPacket_of_relative`: these clauses give o295's `RowPacket` for the tangent instance of the
parent (`isoPFrame`, tangent prior `tanPrior`, hidden unit one, signal `normTest aA RA`, all sets
pulled back by `invEvent`). Normalized bases, physical codes, velocities and states are literally
the original ones; every restricted mass and the reference scale by the same `(q ν(A_A))⁻¹`; rows,
row lists and fits scale by `q/aA` on both sides; the qualification failure set only needs a
measurable cover. o295 can then be applied to the tangent instance as it is frozen.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

/-- The pointwise identities behind the transport, at an arbitrary tangent event. -/
lemma packetBase_eq_inv (TA T' jA j' : ℕ) (cA cb ub : P2) (sc : ℝ) (hsc : sc ≠ 0) (p' : Ev) :
    packetBase T' j'
        ((((2 : ℝ) ^ TA)⁻¹)⁻¹ • (cb + (((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹) • ub - cA)
          - ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) • ub) ub p' =
      packetBase (TA + T') (jA * 2 ^ T' + j') cb ub
        (invEvent ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) (((2 : ℝ) ^ TA)⁻¹) cA sc p') := by
  have hq : ((2 : ℝ) ^ TA)⁻¹ ≠ 0 := by positivity
  have h := packetBase_tanEvent TA T' jA j' cA sc cb ub
    (invEvent ((jA : ℝ) * ((2 : ℝ) ^ TA)⁻¹) (((2 : ℝ) ^ TA)⁻¹) cA sc p')
  simp only at h
  rw [tanEvent_invEvent _ _ cA sc hq hsc] at h
  exact h

section Pointwise

variable (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
include hq hsc

lemma tanLine_invLine_fst (p' : Ev) :
    p'.1 = tanLine (isoPFrame t₀ q c sc) 0 (invEvent t₀ q c sc p').1 :=
  (tanLine_invLine t₀ q c sc hq hsc p'.1).symm

lemma v_inv (p' : Ev) : Split.v p'.1 = Split.v (invEvent t₀ q c sc p').1 := by
  conv_lhs => rw [tanLine_invLine_fst t₀ q c sc hq hsc p']
  exact v_tanLine t₀ q c sc hq _

lemma eval_inv (δ : ℝ) (R : Po) (p' : Ev) (τ : ℝ) :
    MvPolynomial.eval (xp p'.1 τ) ((isoPFrame t₀ q c sc).normTest δ R) =
      δ⁻¹ * MvPolynomial.eval (xp (invEvent t₀ q c sc p').1 (t₀ + q * τ)) R := by
  conv_lhs => rw [tanLine_invLine_fst t₀ q c sc hq hsc p']
  exact eval_normTest_tan t₀ q c sc hq hsc δ R _ τ

lemma eval_d_inv (δ : ℝ) (R : Po) (p' : Ev) (τ : ℝ) :
    MvPolynomial.eval (xp p'.1 τ) (pderiv 3 ((isoPFrame t₀ q c sc).normTest δ R)) =
      sc⁻¹ * (δ⁻¹ * MvPolynomial.eval (xp (invEvent t₀ q c sc p').1 (t₀ + q * τ)) (pderiv 3 R)) := by
  conv_lhs => rw [tanLine_invLine_fst t₀ q c sc hq hsc p']
  exact eval_pderiv_normTest_tan t₀ q c sc hq hsc δ R _ τ

lemma eval_dd_inv (δ : ℝ) (R : Po) (p' : Ev) (τ : ℝ) :
    MvPolynomial.eval (xp p'.1 τ) (pderiv 3 (pderiv 3 ((isoPFrame t₀ q c sc).normTest δ R))) =
      sc⁻¹ * (sc⁻¹ * (δ⁻¹ * MvPolynomial.eval (xp (invEvent t₀ q c sc p').1 (t₀ + q * τ))
        (pderiv 3 (pderiv 3 R)))) := by
  conv_lhs => rw [tanLine_invLine_fst t₀ q c sc hq hsc p']
  exact eval_pderiv2_normTest_tan t₀ q c sc hq hsc δ R _ τ

lemma rate_inv (δ : ℝ) (R : Po) (p' : Ev) :
    Submission.Lib.K4GlobalParentSignal.rate ((isoPFrame t₀ q c sc).normTest δ R) p'.1 p'.2 =
      δ⁻¹ * q * Submission.Lib.K4GlobalParentSignal.rate R (invEvent t₀ q c sc p').1
        (invEvent t₀ q c sc p').2 := by
  conv_lhs => rw [tanLine_invLine_fst t₀ q c sc hq hsc p']
  exact rate_normTest_tan t₀ q c sc hq hsc δ R _ p'.2

omit hq hsc in
lemma invLine_vel (l : Ln) : (invLine t₀ q c sc l).2 3 = l.2 3 ∧ (invLine t₀ q c sc l).2 4 = l.2 4 := by
  simp [invLine]

end Pointwise

/-- o295's `RowPacket` clauses for packet `b = (TA + T', jA*2^T' + j', cb, ub)` inside the parent
block `[jA/2^TA, (jA+1)/2^TA]`, written in ORIGINAL units with the parent test `RA` as signal and
precisions RELATIVE to the parent: `a'` is the relative thickness `a_b/a_A`, `h' = 2^-T'` the
relative time length; rows fit the original line rate of `RA` within `(aA/q) θ`, `q = 2^-TA`;
the qualification failure set is covered by a measurable `bad` set. -/
def RelativeRowPacket (M Ep : ℕ) (precision loss Nk L d₁ gain κ : ℝ) (ν : Measure Ln) (B : ℝ)
    (TA jA : ℕ) (aA : ℝ) (RA : Po) (T' j' : ℕ) (cb ub : P2) (aB a' : ℝ) (Ab : Set Ln)
    (Fb H : Set Ev) : Prop :=
  let q : ℝ := ((2 : ℝ) ^ TA)⁻¹
  let t₀ : ℝ := (jA : ℝ) * q
  let Tb : ℕ := TA + T'
  let jb : ℕ := jA * 2 ^ T' + j'
  let hb : ℝ := ((2 : ℝ) ^ Tb)⁻¹
  let h' : ℝ := ((2 : ℝ) ^ T')⁻¹
  let ζ : ℝ := Split.δ Nk (precision * gain * L)
  let zb : Ev → P3 := packetBase Tb jb cb ub
  let Xnb : Ev → ℝ := fun p => packetSignal RA p / aB
  let ref : ENNReal := ENNReal.ofReal hb * ν Ab
  ∃ (K ε pv θ : ℝ) (Se Er bad : Set Ev) (st : Ev → ℕ) (G : ℕ → Fin 3 → ℝ)
    (pal : Measure (Fin 2 → ℤ)),
    0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a' / h') * ζ ∧ 0 < a' ∧ a' ≤ K * h' ∧ h' ≤ ζ ∧ ζ ≤ 1 ∧ 2 ≤ K ∧
    κ ≤ K ∧ K ^ Ep ≤ Nk ^ (loss * gain * L) ∧ θ = (a' / h') * ζ ^ Ep / K ^ Ep ∧
    K ^ Ep * ε ≤ θ ∧ 0 < pv ∧ K ^ Ep * pv ≤ θ ∧
    MeasurableSet Se ∧ Se ⊆ H ∩ Fb ∧ Se ⊆ Er ∧
    (∀ p ∈ Se, p.1 ∈ Ab ∧ p.2 ∈ Set.Icc ((jb : ℝ) * hb) (((jb : ℝ) + 1) * hb) ∧
      p.2 ∈ Set.Icc t₀ (t₀ + q)) ∧
    0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod volume).restrict Se) Set.univ ∧
    (∀ p ∈ Se, ‖zb p‖ ≤ K ∧ ‖Split.v p.1‖ ≤ K ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + q), |MvPolynomial.eval (xp p.1 t) RA| ≤ K * aA ∧
        |MvPolynomial.eval (xp p.1 t) (pderiv 3 RA)| ≤ K * B ∧
        |MvPolynomial.eval (xp p.1 t) (pderiv 3 (pderiv 3 RA))| ≤ K * B ^ 2 / aA) ∧
      B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (pderiv 3 RA)|) ∧
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
          K / (p ^ (3 : ℕ) * w ^ d₁)) ∧
    Measurable st ∧ (st '' Se).Finite ∧
    (∀ p p' : Ev, st p = st p' → physicalCode zb Xnb ε p = physicalCode zb Xnb ε p') ∧
    (∀ k : ℕ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
      ((ν.prod volume).restrict Se) {p | st p = k ∧ |inner ℝ n (Split.v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
        (1 / 2000000000000 : ENNReal) * ((ν.prod volume).restrict Se) {p | st p = k}) ∧
    IsProbabilityMeasure pal ∧
    (∀ k : ℕ, ∀ b : Fin 2 → ℤ,
      ((ν.prod volume).restrict Se) {p | st p = k ∧ (fun i : Fin 2 => ⌊Split.v p.1 i / pv⌋) = b} ≤
        ENNReal.ofReal K * ((ν.prod volume).restrict Se) {p | st p = k} * pal {b}) ∧
    (∀ k : ℕ, ∀ i : Fin 3, |G k i| ≤ K * (aA / q)) ∧
    (∀ p ∈ Se, |Submission.Lib.K4GlobalParentSignal.rate RA p.1 p.2 -
      ∑ i : Fin 3, (![1, p.1.2 3, p.1.2 4] : Fin 3 → ℝ) i * G (st p) i| ≤ (aA / q) * θ) ∧
    (∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧ ∀ p ∈ Er,
      (∀ i : Fin 3, |zb p i - c' i| ≤ θ) → (fun i : Fin 3 => ⌊G (st p) i / ((aA / q) * θ)⌋) ∈ Fc) ∧
    MeasurableSet bad ∧
    {w | w ∈ Se ∧ ¬ ∃ Pq : Fin 3 → Polynomial ℝ, (∀ i, (Pq i).natDegree ≤ M) ∧
        (∀ i n, |(Pq i).coeff n| ≤ K * (aA / q)) ∧
        (∀ i, |G (st w) i - (Pq i).eval ((w.2 - (jb : ℝ) * hb) / hb)| ≤ (aA / q) * θ) ∧
        ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ Set.Icc (0 : ℝ) 1 ∧
          ENNReal.ofReal (1 / K) ≤ volume Et ∧ ∀ s ∈ Et, ((w.1, (jb : ℝ) * hb + hb * s) : Ev) ∈ Er ∧
            ∀ i, |G (st (w.1, (jb : ℝ) * hb + hb * s)) i - (Pq i).eval s| ≤ (aA / q) * θ} ⊆ bad ∧
    ((ν.prod volume).restrict Se) bad ≤ (1 / 10000 : ENNReal) * ((ν.prod volume).restrict Se) Set.univ

lemma measurable_xp_pt : Measurable (fun p : Ev => xp p.1 p.2) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i <;> simp [xp] <;> fun_prop

lemma measurable_packetBase (T j : ℕ) (c u : P2) : Measurable (packetBase T j c u) := by
  unfold packetBase
  dsimp only
  have h1 : Measurable (fun p : Ev => (xp p.1 p.2) 1) :=
    (measurable_pi_apply 1).comp measurable_xp_pt
  have h2 : Measurable (fun p : Ev => (xp p.1 p.2) 2) :=
    (measurable_pi_apply 2).comp measurable_xp_pt
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma measurable_packetSignal (P : Po) : Measurable (packetSignal P) :=
  (MvPolynomial.continuous_eval P).measurable.comp measurable_xp_pt

lemma tanPrior_invLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (ν : Measure Ln) (AA Ab : Set Ln) (hAb : MeasurableSet Ab) :
    tanPrior (isoPFrame t₀ q c sc) 0 ν AA (invLine t₀ q c sc ⁻¹' Ab) = nuE ν AA Ab := by
  rw [tanPrior_apply _ _ _ _ ((measurable_invLine t₀ q c sc) hAb)]
  congr 1
  ext l
  simp [invLine_tanLine t₀ q c sc hq hsc]

/-- The tangent center of the relative packet. -/
def relCenter (TA T' jA j' : ℕ) (cA cb ub : P2) : P2 :=
  (((2 : ℝ) ^ TA)⁻¹)⁻¹ • (cb + (((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹) • ub - cA)
    - ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) • ub

set_option maxHeartbeats 4000000 in
/-- The forward transport (see the module docstring). -/
theorem rowPacket_of_relative (M Ep : ℕ) (precision loss Nk L d₁ gain κ : ℝ)
    (ν : Measure Ln) [SFinite ν] (B : ℝ) (hB : 0 < B)
    (TA jA : ℕ) (cA : P2) (AA : Set Ln) (hAA : MeasurableSet AA) (hAA0 : ν AA ≠ 0)
    (hAAT : ν AA ≠ ⊤) (aA : ℝ) (haA : 0 < aA) (RA : Po) (hRA : RA.totalDegree ≤ 2)
    (T' j' : ℕ) (cb ub : P2) (aB r' : ℝ) (haB : 0 < aB) (hr' : aB = aA * Split.δ Nk r')
    (Ab : Set Ln) (hAb : MeasurableSet Ab) (hAbA : Ab ⊆ AA) (Fb H : Set Ev)
    (h : RelativeRowPacket M Ep precision loss Nk L d₁ gain κ ν B TA jA aA RA T' j' cb ub aB
      (Split.δ Nk r') Ab Fb H) :
    let q : ℝ := ((2 : ℝ) ^ TA)⁻¹
    let t₀ : ℝ := (jA : ℝ) * q
    let sc : ℝ := B / aA
    RowPacket M Ep precision loss Nk L d₁ gain κ
      (tanPrior (isoPFrame t₀ q cA sc) 0 ν AA) 1 r' T' j' (relCenter TA T' jA j' cA cb ub) ub
      ((isoPFrame t₀ q cA sc).normTest aA RA) (invLine t₀ q cA sc ⁻¹' Ab)
      (invEvent t₀ q cA sc ⁻¹' Fb) (invEvent t₀ q cA sc ⁻¹' H) := by
  intro q t₀ sc
  have hq : 0 < q := by positivity
  have hsc : sc ≠ 0 := (div_pos hB haA).ne'
  obtain ⟨K, ε, pv, θ, Se, Er, bad, st, G, pal, hε, hεζ, hεa, ha', ha'K, hh'ζ, hζ1, hK2, hκK,
    hKEp, hθ, hKε, hpv, hKpv, hSe, hSeHF, hSeEr, hSeIn, href, hrefK, hjets, hbase, hband,
    hcensus, hst, hstfin, hstcode, hbreadth, hpal, hpaldom, hGbd, hrows, hlists, hbadm, hfail,
    hbadmass⟩ := h
  unfold RowPacket
  dsimp only
  have hAA_le : ∀ p ∈ Se, p.1 ∈ AA := fun p hp => hAbA (hSeIn p hp).1
  set inv := invEvent t₀ q cA sc with hinv_def
  have hinvm : Measurable inv := measurable_invEvent t₀ q cA sc
  have hscale : ∀ Y, MeasurableSet Y →
      (((tanPrior (isoPFrame t₀ q cA sc) 0 ν AA).prod volume).restrict (inv ⁻¹' Se)) (inv ⁻¹' Y) =
        (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se) Y :=
    fun Y hY => tan_restrict_apply t₀ q cA sc hq hsc ν AA hAA hSe hY hAA_le
  have hzb : ∀ p', packetBase T' j' (relCenter TA T' jA j' cA cb ub) ub p' =
      packetBase (TA + T') (jA * 2 ^ T' + j') cb ub (inv p') :=
    fun p' => packetBase_eq_inv TA T' jA j' cA cb ub sc hsc p'
  have hXn : ∀ p', packetSignal ((isoPFrame t₀ q cA sc).normTest aA RA) p' / Split.δ Nk r' =
      packetSignal RA (inv p') / aB := by
    intro p'
    unfold packetSignal
    rw [eval_inv t₀ q cA sc hq.ne' hsc aA RA p' p'.2, hr']
    show aA⁻¹ * MvPolynomial.eval (xp (inv p').1 (inv p').2) RA / Split.δ Nk r' = _
    rw [div_mul_eq_div_div, inv_mul_eq_div]
  have hv : ∀ p' : Ev, Split.v p'.1 = Split.v (inv p').1 := v_inv t₀ q cA sc hq.ne' hsc
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hc0 : ENNReal.ofReal q * ν AA ≠ 0 := mul_ne_zero hq0 hAA0
  have hc0T : ENNReal.ofReal q * ν AA ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAAT
  have hh' : ((2 : ℝ) ^ T')⁻¹ = ((2 : ℝ) ^ (TA + T'))⁻¹ / q := by
    simp only [q, pow_add]; field_simp
  have hrefs : ENNReal.ofReal ((2 : ℝ) ^ T')⁻¹ *
      tanPrior (isoPFrame t₀ q cA sc) 0 ν AA (invLine t₀ q cA sc ⁻¹' Ab) =
      (ENNReal.ofReal q * ν AA)⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab) := by
    rw [tanPrior_invLine t₀ q cA sc hq.ne' hsc ν AA Ab hAb, nuE, Measure.smul_apply,
      Measure.restrict_apply hAb, Set.inter_eq_left.mpr hAbA, smul_eq_mul, hh',
      ENNReal.ofReal_div_of_pos hq, ENNReal.mul_inv (Or.inl hq0) (Or.inl ENNReal.ofReal_ne_top),
      div_eq_mul_inv]
    ring
  have hjbT : ((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹ =
      t₀ + q * ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) := by
    simp only [t₀, q, pow_add]; push_cast; field_simp; try ring
  have hqh : q * ((2 : ℝ) ^ T')⁻¹ = ((2 : ℝ) ^ (TA + T'))⁻¹ := by
    simp only [q, pow_add]; field_simp
  have hτ : ∀ w' : Ev, (w'.2 - (j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) / ((2 : ℝ) ^ T')⁻¹ =
      ((inv w').2 - ((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹) /
        ((2 : ℝ) ^ (TA + T'))⁻¹ := by
    intro w'
    have : (inv w').2 = t₀ + q * w'.2 := rfl
    rw [this, hjbT, ← hqh]
    have hq' : q ≠ 0 := hq.ne'
    have hH : ((2 : ℝ) ^ T')⁻¹ ≠ 0 := by positivity
    field_simp
    ring
  have hev : ∀ (w' : Ev) (s' : ℝ), inv ((w'.1, (j' : ℝ) * ((2 : ℝ) ^ T')⁻¹ + ((2 : ℝ) ^ T')⁻¹ * s') : Ev) =
      ((inv w').1, ((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹ +
        ((2 : ℝ) ^ (TA + T'))⁻¹ * s') := by
    intro w' s'
    show (invLine t₀ q cA sc w'.1, t₀ + q * ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹ + ((2 : ℝ) ^ T')⁻¹ * s')) = _
    rw [hjbT, ← hqh]
    refine Prod.ext rfl ?_
    ring
  refine ⟨K, ε, pv, θ, inv ⁻¹' Se, inv ⁻¹' Er, st ∘ inv, fun k i => (q / aA) * G k i, pal,
    isProbability_tanPrior _ 0 ν AA hAA0 hAAT,
    ((isoPFrame t₀ q cA sc).totalDegree_normTest_le aA RA).trans hRA,
    (measurable_invLine t₀ q cA sc) hAb, hε, hεζ, hεa, ha', ha'K, hh'ζ, hζ1, hK2, hκK, hKEp, hθ,
    hKε, hpv, hKpv, hinvm hSe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p' hp'
    exact ⟨(hSeHF hp').1, (hSeHF hp').2⟩
  · intro p' hp'
    exact hSeEr hp'
  · intro p' hp'
    obtain ⟨h1, h2, h3⟩ := hSeIn (inv p') hp'
    refine ⟨h1, ?_, ?_⟩
    · have : (inv p').2 = t₀ + q * p'.2 := rfl
      rw [this] at h2
      obtain ⟨h2a, h2b⟩ := h2
      have hH : (0 : ℝ) < (2 : ℝ) ^ T' := by positivity
      have hjb : ((jA * 2 ^ T' + j' : ℕ) : ℝ) * ((2 : ℝ) ^ (TA + T'))⁻¹ =
          t₀ + q * ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) := by
        simp only [t₀, q, pow_add]; push_cast; field_simp; try ring
      have hjb1 : (((jA * 2 ^ T' + j' : ℕ) : ℝ) + 1) * ((2 : ℝ) ^ (TA + T'))⁻¹ =
          t₀ + q * (((j' : ℝ) + 1) * ((2 : ℝ) ^ T')⁻¹) := by
        simp only [t₀, q, pow_add]; push_cast; field_simp; try ring
      rw [hjb] at h2a
      rw [hjb1] at h2b
      constructor
      · nlinarith
      · nlinarith
    · have : (inv p').2 = t₀ + q * p'.2 := rfl
      rw [this] at h3
      obtain ⟨h3a, h3b⟩ := h3
      constructor
      · nlinarith
      · nlinarith
  · rw [hrefs]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hc0T) href.ne'
  · rw [hrefs, ← Set.preimage_univ (f := inv), hscale Set.univ MeasurableSet.univ, mul_div_assoc]
    gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- jets on the tangent unit block
    intro p' hp'
    obtain ⟨hz, hvb, hjet, hlow⟩ := hjets (inv p') hp'
    refine ⟨by rw [hzb]; exact hz, by rw [hv]; exact hvb, ?_, ?_⟩
    · intro τ hτ
      have hτ' : t₀ + q * τ ∈ Set.Icc t₀ (t₀ + q) := by
        constructor <;> nlinarith [hτ.1, hτ.2]
      obtain ⟨j0, j1, j2⟩ := hjet (t₀ + q * τ) hτ'
      refine ⟨?_, ?_, ?_⟩
      · rw [eval_inv t₀ q cA sc hq.ne' hsc aA RA p' τ, abs_mul, abs_inv, abs_of_pos haA]
        rw [inv_mul_le_iff₀ haA]
        linarith
      · rw [eval_d_inv t₀ q cA sc hq.ne' hsc aA RA p' τ]
        simp only [sc]
        rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_div, abs_of_pos hB, abs_of_pos haA, mul_one]
        rw [inv_div, ← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ haA.ne', one_div,
          inv_mul_le_iff₀ hB]
        linarith
      · rw [eval_dd_inv t₀ q cA sc hq.ne' hsc aA RA p' τ]
        simp only [sc]
        have hbound : |MvPolynomial.eval (xp (inv p').1 (t₀ + q * τ)) (pderiv 3 (pderiv 3 RA))| ≤
            K * B ^ 2 / aA := j2
        set E := |MvPolynomial.eval (xp (inv p').1 (t₀ + q * τ)) (pderiv 3 (pderiv 3 RA))| with hEdef
        rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_inv, abs_div, abs_of_pos hB, abs_of_pos haA,
          one_pow, mul_one, ← hEdef]
        rw [inv_div]
        have key : aA / B * (aA / B * (aA⁻¹ * E)) = aA / B ^ 2 * E := by field_simp
        rw [key]
        calc aA / B ^ 2 * E ≤ aA / B ^ 2 * (K * B ^ 2 / aA) :=
              mul_le_mul_of_nonneg_left hbound (by positivity)
          _ = K := by field_simp
    · rw [eval_d_inv t₀ q cA sc hq.ne' hsc aA RA p' p'.2]
      simp only [sc]
      have hp2 : (inv p').2 = t₀ + q * p'.2 := rfl
      rw [← hp2, abs_mul, abs_mul, abs_inv, abs_inv, abs_div, abs_of_pos hB, abs_of_pos haA,
        inv_div, ← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ haA.ne', one_div]
      have hK0 : 0 < K := by linarith
      calc K⁻¹ = 1 / B * (B / K) := by field_simp
        _ ≤ 1 / B * _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  · -- base ceiling
    intro U hU
    have hset : {p' : Ev | packetBase T' j' (relCenter TA T' jA j' cA cb ub) ub p' ∈ U} =
        inv ⁻¹' {p | packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p ∈ U} := by
      ext p'; simp [hzb]
    rw [hset, hscale {p | packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p ∈ U}
      ((measurable_packetBase _ _ _ _) hU), hrefs]
    calc (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se)
          {p | packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p ∈ U}
        ≤ (ENNReal.ofReal q * ν AA)⁻¹ *
            (ENNReal.ofReal K * (ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab) * volume U) := by
          gcongr; exact hbase U hU
      _ = _ := by ring
  · -- band caps
    intro w hw1 hw2 U hU f hf
    have hset : {p' : Ev | packetBase T' j' (relCenter TA T' jA j' cA cb ub) ub p' ∈ U ∧
          |packetSignal ((isoPFrame t₀ q cA sc).normTest aA RA) p' / Split.δ Nk r' -
            f (packetBase T' j' (relCenter TA T' jA j' cA cb ub) ub p')| ≤ w} =
        inv ⁻¹' {p | packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p ∈ U ∧
          |packetSignal RA p / aB - f (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p)| ≤ w} := by
      ext p'; simp [hzb, hXn]
    have hmeas : MeasurableSet {p : Ev | packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p ∈ U ∧
        |packetSignal RA p / aB - f (packetBase (TA + T') (jA * 2 ^ T' + j') cb ub p)| ≤ w} := by
      refine ((measurable_packetBase _ _ _ _) hU).inter ?_
      exact measurableSet_le (((measurable_packetSignal RA).div_const aB).sub
        (hf.comp (measurable_packetBase _ _ _ _))).abs measurable_const
    rw [hset, hscale _ hmeas, hrefs]
    calc (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se) _
        ≤ (ENNReal.ofReal q * ν AA)⁻¹ *
            (ENNReal.ofReal (K * w ^ d₁) * (ENNReal.ofReal ((2 : ℝ) ^ (TA + T'))⁻¹ * ν Ab) *
              volume U) := by
          gcongr; exact hband w hw1 hw2 U hU f hf
      _ = _ := by ring
  · -- census
    intro p w hp1 hp2 hw1 hw2 hcond
    have hset : {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ inv ⁻¹' Se,
          (fun e => (fun i : Fin 3 => ⌊packetBase T' j' (relCenter TA T' jA j' cA cb ub) ub e i / p⌋,
            ⌊packetSignal ((isoPFrame t₀ q cA sc).normTest aA RA) e / Split.δ Nk r' / w⌋)) e = k} =
        {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se,
          (fun e => (fun i : Fin 3 => ⌊packetBase (TA + T') (jA * 2 ^ T' + j') cb ub e i / p⌋,
            ⌊packetSignal RA e / aB / w⌋)) e = k} := by
      ext k
      constructor
      · rintro ⟨e', he', rfl⟩
        exact ⟨inv e', he', by simp [hzb, hXn]⟩
      · rintro ⟨e, he, rfl⟩
        refine ⟨tanEvent (isoPFrame t₀ q cA sc) 0 e, ?_, ?_⟩
        · show inv (tanEvent _ 0 e) ∈ Se
          rw [hinv_def, invEvent_tanEvent t₀ q cA sc hq.ne' hsc]; exact he
        · have he' := invEvent_tanEvent t₀ q cA sc hq.ne' hsc e
          simp only [hzb, hXn, ← hinv_def] at *
          rw [he']
    rw [hset]
    exact hcensus p w hp1 hp2 hw1 hw2 hcond
  · exact hst.comp hinvm
  · refine hstfin.subset ?_
    rintro k ⟨p', hp', rfl⟩
    exact ⟨inv p', hp', rfl⟩
  · intro p p' hpp
    have := hstcode (inv p) (inv p') hpp
    simp only [physicalCode, hzb, hXn] at this ⊢
    exact this
  · -- strip breadth
    intro k n t hn
    have hst1 : ∀ k, MeasurableSet {p : Ev | st p = k} := fun k => hst (measurableSet_singleton k)
    have hvm : Measurable (fun p : Ev => inner ℝ n (Split.v p.1)) := by
      unfold Split.v; fun_prop
    have hA : {p' : Ev | (st ∘ inv) p' = k ∧ |inner ℝ n (Split.v p'.1) - t| ≤ K ^ (-100 : ℝ)} =
        inv ⁻¹' {p | st p = k ∧ |inner ℝ n (Split.v p.1) - t| ≤ K ^ (-100 : ℝ)} := by
      ext p'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply]
      rw [hv p']
    have hB' : {p' : Ev | (st ∘ inv) p' = k} = inv ⁻¹' {p | st p = k} := by ext p'; simp
    have hmA : MeasurableSet {p : Ev | st p = k ∧ |inner ℝ n (Split.v p.1) - t| ≤ K ^ (-100 : ℝ)} :=
      (hst1 k).inter (measurableSet_le (hvm.sub_const t).abs measurable_const)
    rw [hA, hB', hscale _ hmA, hscale _ (hst1 k)]
    calc (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se) _
        ≤ (ENNReal.ofReal q * ν AA)⁻¹ * ((1 / 2000000000000 : ENNReal) *
            ((ν.prod volume).restrict Se) {p | st p = k}) := by
          gcongr; exact hbreadth k n t hn
      _ = _ := by ring
  · exact hpal
  · -- palette domination
    intro k b
    have hst1 : ∀ k, MeasurableSet {p : Ev | st p = k} := fun k => hst (measurableSet_singleton k)
    have hbin : Measurable (fun p : Ev => (fun i : Fin 2 => ⌊Split.v p.1 i / pv⌋)) := by
      refine measurable_pi_iff.mpr (fun i => ?_)
      have : Measurable (fun p : Ev => Split.v p.1 i) := by unfold Split.v; fin_cases i <;> fun_prop
      exact Int.measurable_floor.comp (this.div_const pv)
    have hA : {p' : Ev | (st ∘ inv) p' = k ∧ (fun i : Fin 2 => ⌊Split.v p'.1 i / pv⌋) = b} =
        inv ⁻¹' {p | st p = k ∧ (fun i : Fin 2 => ⌊Split.v p.1 i / pv⌋) = b} := by
      ext p'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply]
      rw [hv p']
    have hB' : {p' : Ev | (st ∘ inv) p' = k} = inv ⁻¹' {p | st p = k} := by ext p'; simp
    have hmA : MeasurableSet {p : Ev | st p = k ∧ (fun i : Fin 2 => ⌊Split.v p.1 i / pv⌋) = b} :=
      (hst1 k).inter (hbin (measurableSet_singleton b))
    rw [hA, hB', hscale _ hmA, hscale _ (hst1 k)]
    calc (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se) _
        ≤ (ENNReal.ofReal q * ν AA)⁻¹ * (ENNReal.ofReal K *
            ((ν.prod volume).restrict Se) {p | st p = k} * pal {b}) := by
          gcongr; exact hpaldom k b
      _ = _ := by ring
  · -- row bound
    intro k i
    have := hGbd k i
    rw [abs_mul, abs_of_pos (div_pos hq haA)]
    calc q / aA * |G k i| ≤ q / aA * (K * (aA / q)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = K := by field_simp
  · -- rows
    intro p' hp'
    have hrate : (∑ i : Fin 4, MvPolynomial.eval (xp p'.1 p'.2)
          (pderiv i ((isoPFrame t₀ q cA sc).normTest aA RA)) *
            (![1, p'.1.2 3, p'.1.2 4, p'.1.2 5] : Fin 4 → ℝ) i) =
        aA⁻¹ * q * Submission.Lib.K4GlobalParentSignal.rate RA (inv p').1 (inv p').2 :=
      rate_inv t₀ q cA sc hq.ne' hsc aA RA p'
    have hvel := invLine_vel t₀ q cA sc p'.1
    have hrow := hrows (inv p') hp'
    rw [hrate]
    have hsum : (∑ i : Fin 3, (![1, p'.1.2 3, p'.1.2 4] : Fin 3 → ℝ) i *
          (q / aA * G ((st ∘ inv) p') i)) =
        q / aA * ∑ i : Fin 3, (![1, (inv p').1.2 3, (inv p').1.2 4] : Fin 3 → ℝ) i *
          G (st (inv p')) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      fin_cases i <;> simp [hinv_def, invEvent, hvel.1, hvel.2] <;> ring
    rw [hsum, show aA⁻¹ * q * Submission.Lib.K4GlobalParentSignal.rate RA (inv p').1 (inv p').2 -
        q / aA * (∑ i : Fin 3, (![1, (inv p').1.2 3, (inv p').1.2 4] : Fin 3 → ℝ) i *
          G (st (inv p')) i) =
        q / aA * (Submission.Lib.K4GlobalParentSignal.rate RA (inv p').1 (inv p').2 -
          ∑ i : Fin 3, (![1, (inv p').1.2 3, (inv p').1.2 4] : Fin 3 → ℝ) i *
            G (st (inv p')) i) by ring, abs_mul, abs_of_pos (div_pos hq haA)]
    calc q / aA * _ ≤ q / aA * (aA / q * θ) := mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = θ := by field_simp
  · -- coarse row lists
    intro c'
    obtain ⟨Fc, hFc, hmem⟩ := hlists c'
    refine ⟨Fc, hFc, fun p' hp' hz => ?_⟩
    have h := hmem (inv p') hp' (fun i => by rw [← hzb]; exact hz i)
    convert h using 2
    congr 1
    show q / aA * G (st (inv p')) _ / θ = G (st (inv p')) _ / (aA / q * θ)
    by_cases hθ0 : θ = 0
    · simp [hθ0]
    · field_simp
  · -- qualification
    have hSe' : MeasurableSet (inv ⁻¹' Se) := hinvm hSe
    rw [Measure.restrict_apply' hSe']
    calc ((tanPrior (isoPFrame t₀ q cA sc) 0 ν AA).prod volume) (_ ∩ inv ⁻¹' Se)
        ≤ ((tanPrior (isoPFrame t₀ q cA sc) 0 ν AA).prod volume) (inv ⁻¹' bad ∩ inv ⁻¹' Se) := by
          apply measure_mono
          rintro w' ⟨hnot, hw'⟩
          refine ⟨hfail ⟨hw', fun ⟨Pq, hdeg, hcoef, hfit, Et, hEt, hEtsub, hEtvol, hEtfit⟩ => hnot ?_⟩, hw'⟩
          refine ⟨fun i => Polynomial.C (q / aA) * Pq i, fun i => ?_, fun i n => ?_, fun i => ?_,
            Et, hEt, hEtsub, hEtvol, fun s' hs' => ?_⟩
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (hdeg i)
          · rw [Polynomial.coeff_C_mul, abs_mul, abs_of_pos (div_pos hq haA)]
            calc q / aA * |(Pq i).coeff n| ≤ q / aA * (K * (aA / q)) :=
                  mul_le_mul_of_nonneg_left (hcoef i n) (by positivity)
              _ = K := by field_simp
          · simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_C]
            rw [hτ w', ← mul_sub, abs_mul, abs_of_pos (div_pos hq haA)]
            calc q / aA * _ ≤ q / aA * (aA / q * θ) :=
                  mul_le_mul_of_nonneg_left (hfit i) (by positivity)
              _ = θ := by field_simp
          · obtain ⟨hEr, hfit2⟩ := hEtfit s' hs'
            refine ⟨?_, fun i => ?_⟩
            · show inv _ ∈ Er
              rw [hev w' s']; exact hEr
            · simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_C]
              rw [hev w' s', ← mul_sub, abs_mul, abs_of_pos (div_pos hq haA)]
              calc q / aA * _ ≤ q / aA * (aA / q * θ) :=
                    mul_le_mul_of_nonneg_left (hfit2 i) (by positivity)
                _ = θ := by field_simp
      _ = (((tanPrior (isoPFrame t₀ q cA sc) 0 ν AA).prod volume).restrict (inv ⁻¹' Se))
            (inv ⁻¹' bad) := (Measure.restrict_apply (hinvm hbadm)).symm
      _ = (ENNReal.ofReal q * ν AA)⁻¹ * ((ν.prod volume).restrict Se) bad := hscale _ hbadm
      _ ≤ (ENNReal.ofReal q * ν AA)⁻¹ * ((1 / 10000 : ENNReal) *
            ((ν.prod volume).restrict Se) Set.univ) := by gcongr
      _ = (1 / 10000 : ENNReal) * ((ENNReal.ofReal q * ν AA)⁻¹ *
            ((ν.prod volume).restrict Se) Set.univ) := by ring
      _ = _ := by rw [← hscale Set.univ MeasurableSet.univ, Set.preimage_univ]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
