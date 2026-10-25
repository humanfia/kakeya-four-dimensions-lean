-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Forward, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1080,
-- branch x1080, commit 5a0a478a0, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/Forward.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Forward transport to a tangent packet (x1080, o204). Builds on x1078's `Tangent.Frame`
-- (same obligation) and the accepted o280 `k4_finite_affine_candidate_return` frames and
-- normalized tests, and on lib `K4GlobalParentSignal.rate` (all imported, not copied).
-- `packetBase`, `packetSignal`, `physicalCode` and `RowPacket` are the bindings of the frozen
-- statement of o295 `k4_physical_row_packet_potential`, verbatim.
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Frame
import Submission.Obl.k4_finite_affine_candidate_return.ParentFrameInv
import Submission.Lib.K4GlobalParentSignal

/-!
# Isotropic tangent frames

A parent block `[t₀, t₀ + q]` with base center `c` gives the unsheared isotropic frame
`isoPFrame t₀ q c sc`: tangent time `(t - t₀)/q`, tangent base `(y - c)/q`, hidden coordinate
rescaled by `sc`. In this frame

* velocities are unchanged: `v (tanLine Φ 0 l) = v l` (`v_tanLine`);
* a packet `b` inside the parent keeps its normalized base: `packetBase` of the tangent event in
  the relative packet equals `packetBase` of the original event (`packetBase_tanEvent`);
* an original test `R` normalized by `δ` becomes the tangent test `Φ.normTest δ R`, with values
  `δ⁻¹ R` (`eval_normTest_tan`) and line rates `(q/δ)` times the original rates
  (`rate_normTest_tan`).

These are the identities that move o295's `RowPacket` clauses from original units, at
precisions relative to the parent, to the tangent instance.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-! ## The bindings of o295's frozen statement -/

/-- o295's `packetBase`. -/
def packetBase : ℕ → ℕ → P2 → P2 → Ev → P3 :=
  fun T j c u p => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with
    | h => (match (((j : ℝ) * h : ℝ)) with
      | t0 => WithLp.toLp 2 ![(p.2 - t0) / h, ((xp p.1 p.2) 1 - (c 0 + t0 * u 0)) / h,
          ((xp p.1 p.2) 2 - (c 1 + t0 * u 1)) / h]))

/-- o295's `packetSignal`. -/
def packetSignal : Po → Ev → ℝ := fun P p => MvPolynomial.eval (xp p.1 p.2) P

/-- o295's `physicalCode`. -/
def physicalCode : (Ev → P3) → (Ev → ℝ) → ℝ → Ev → ((Fin 3 → ℤ) × ℤ) :=
  fun z X ε p => (fun i => ⌊z p i / ε⌋, ⌊X p / ε⌋)

/-! ## The isotropic unsheared frame -/

/-- The frame of a parent block: time `(t - t₀)/q`, base `(y - c)/q`, no shear. -/
def isoFrame (t₀ q : ℝ) (c : P2) : Frame := ⟨t₀, q, c, 0, q • (1 : Matrix (Fin 2) (Fin 2) ℝ)⟩

/-- The parent frame with hidden scale `sc`. -/
def isoPFrame (t₀ q : ℝ) (c : P2) (sc : ℝ) : PFrame := ⟨isoFrame t₀ q c, sc⟩

lemma smul_one_inv (q : ℝ) (hq : q ≠ 0) :
    (q • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = q⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hq, one_smul]

lemma isoFrame_Dinv (t₀ q : ℝ) (c : P2) (hq : q ≠ 0) :
    (isoFrame t₀ q c).D⁻¹ = q⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  smul_one_inv q hq

lemma hiddenShear_zero {α : Type} (b : α → Fin 6 → ℝ) (l : α) :
    hiddenShear b 0 l = b l := by
  funext i
  fin_cases i <;> simp [hiddenShear, Submission.Lib.K4ContactNormalization.residualCoeff]

/-- Tangent line coefficients in the isotropic frame. -/
lemma tanLine_iso (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (l : Ln) :
    tanLine (isoPFrame t₀ q c sc) 0 l =
      (l.1, ![(l.2 0 + t₀ * l.2 3 - c 0) / q, (l.2 1 + t₀ * l.2 4 - c 1) / q,
        sc * (l.2 2 + t₀ * l.2 5), l.2 3, l.2 4, sc * (q * l.2 5)]) := by
  have hD := smul_one_inv q hq
  unfold tanLine
  rw [hiddenShear_zero]
  congr 1
  funext i
  fin_cases i <;>
    simp [PFrame.eb, isoPFrame, Frame.normCoeff, hD, isoFrame, Matrix.smul_apply] <;>
    field_simp

/-- Velocities are unchanged by the isotropic frame. -/
lemma v_tanLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (l : Ln) :
    Split.v (tanLine (isoPFrame t₀ q c sc) 0 l) = Split.v l := by
  rw [tanLine_iso t₀ q c sc hq]
  simp [Split.v]

/-- The tangent point of an original incidence, coordinate by coordinate. -/
lemma xp_tanLine_iso (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (l : Ln) (τ : ℝ) :
    xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ =
      ![τ, (xp l (t₀ + q * τ) 1 - c 0) / q, (xp l (t₀ + q * τ) 2 - c 1) / q,
        sc * xp l (t₀ + q * τ) 3] := by
  rw [tanLine_iso t₀ q c sc hq]
  funext i
  fin_cases i <;> simp [xp] <;> field_simp <;> ring

/-- The relative packet of a packet `b` inside the parent: its normalized base is unchanged.
`T = Tp + T'`, `j = jp * 2^T' + j'`, parent block `[jp/2^Tp, (jp+1)/2^Tp]`. -/
lemma packetBase_tanEvent (Tp T' jp j' : ℕ) (c : P2) (sc : ℝ) (cb ub : P2) (p : Ev) :
    let q : ℝ := ((2 : ℝ) ^ Tp)⁻¹
    let t₀ : ℝ := (jp : ℝ) * q
    let T := Tp + T'
    let j := jp * 2 ^ T' + j'
    let hb : ℝ := ((2 : ℝ) ^ T)⁻¹
    packetBase T' j' ((q⁻¹) • (cb + ((j : ℝ) * hb) • ub - c) - ((j' : ℝ) * ((2 : ℝ) ^ T')⁻¹) • ub)
        ub (tanEvent (isoPFrame t₀ q c sc) 0 p) =
      packetBase T j cb ub p := by
  intro q t₀ T j hb
  have hq : q ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ T = (2 : ℝ) ^ Tp * (2 : ℝ) ^ T' := by
    simp only [T, pow_add]
  unfold packetBase tanEvent
  simp only
  rw [xp_tanLine_iso t₀ q c sc hq]
  ext i
  fin_cases i <;> simp [xp, q, t₀, j, hb, h2, isoPFrame, isoFrame] <;> field_simp <;> ring

lemma isoFrame_det_isUnit (t₀ q : ℝ) (c : P2) (hq : q ≠ 0) : IsUnit (isoFrame t₀ q c).D.det := by
  show IsUnit (q • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hq)

/-- The tangent point is o280's model point. -/
lemma xp_tanLine_zero (Φ : PFrame) (l : Ln) (τ : ℝ) :
    xp (tanLine Φ 0 l) τ = exS Φ.eb l τ := by
  rw [xp_tanLine]
  have : hiddenShear Φ.eb 0 = Φ.eb := funext (hiddenShear_zero Φ.eb)
  rw [this]

/-- The normalized test at a tangent point is `δ⁻¹` times the original test. -/
lemma eval_normTest_tan (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (δ : ℝ)
    (R : Po) (l : Ln) (τ : ℝ) :
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        ((isoPFrame t₀ q c sc).normTest δ R) =
      δ⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ)) R := by
  have h := (isoPFrame t₀ q c sc).eval_normTest hq (isoFrame_det_isUnit t₀ q c hq) hsc δ R l
    (t₀ + q * τ)
  have hτ : (t₀ + q * τ - (isoPFrame t₀ q c sc).F.t₀) / (isoPFrame t₀ q c sc).F.q = τ := by
    show (t₀ + q * τ - t₀) / q = τ
    field_simp; ring
  rw [hτ] at h
  rw [xp_tanLine_zero]
  exact h

/-- Hidden derivatives of the normalized test scale by `sc⁻¹` (o280 `pderiv_normTest`). -/
lemma eval_pderiv_normTest_tan (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (δ : ℝ) (R : Po) (l : Ln) (τ : ℝ) :
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        (pderiv 3 ((isoPFrame t₀ q c sc).normTest δ R)) =
      sc⁻¹ * (δ⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ)) (pderiv 3 R)) := by
  rw [PFrame.pderiv_normTest, MvPolynomial.smul_eval, eval_normTest_tan t₀ q c sc hq hsc]
  rfl

lemma eval_pderiv2_normTest_tan (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (δ : ℝ) (R : Po) (l : Ln) (τ : ℝ) :
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        (pderiv 3 (pderiv 3 ((isoPFrame t₀ q c sc).normTest δ R))) =
      sc⁻¹ * (sc⁻¹ * (δ⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ)) (pderiv 3 (pderiv 3 R)))) := by
  rw [PFrame.pderiv_normTest, Derivation.map_smul, PFrame.pderiv_normTest, smul_smul,
    MvPolynomial.smul_eval, eval_normTest_tan t₀ q c sc hq hsc]
  show sc⁻¹ * sc⁻¹ * (δ⁻¹ * _) = _
  ring

/-- Line rates of the normalized test: `(q/δ)` times the original rate. -/
lemma rate_normTest_tan (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (δ : ℝ)
    (R : Po) (l : Ln) (τ : ℝ) :
    Submission.Lib.K4GlobalParentSignal.rate ((isoPFrame t₀ q c sc).normTest δ R)
        (tanLine (isoPFrame t₀ q c sc) 0 l) τ =
      δ⁻¹ * q * Submission.Lib.K4GlobalParentSignal.rate R l (t₀ + q * τ) := by
  have hL := Submission.Lib.K4GlobalParentSignal.hasDerivAt_signal
    ((isoPFrame t₀ q c sc).normTest δ R) (tanLine (isoPFrame t₀ q c sc) 0 l) τ
  have hlin : HasDerivAt (fun s : ℝ => t₀ + q * s) q τ := by
    simpa using ((hasDerivAt_id τ).const_mul q).const_add t₀
  have hR := (Submission.Lib.K4GlobalParentSignal.hasDerivAt_signal R l (t₀ + q * τ)).comp τ hlin
  have hR' := hR.const_mul δ⁻¹
  have heq : (fun s => MvPolynomial.eval (Submission.Lib.K4GlobalParentSignal.xp
        (tanLine (isoPFrame t₀ q c sc) 0 l) s) ((isoPFrame t₀ q c sc).normTest δ R)) =
      (fun s => δ⁻¹ * ((fun t => MvPolynomial.eval (Submission.Lib.K4GlobalParentSignal.xp l t) R) ∘
        (fun s : ℝ => t₀ + q * s)) s) := by
    funext s
    exact eval_normTest_tan t₀ q c sc hq hsc δ R l s
  rw [heq] at hL
  have := hL.unique hR'
  rw [this]
  ring

/-- o295's `RowPacket`, verbatim. -/
def RowPacket : ℕ → ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → MeasureTheory.Measure Ln → ℝ → ℝ → ℕ → ℕ → P2 → P2 → Po → Set Ln → Set Ev → Set Ev → Prop :=
  (fun M Ep precision loss Nk L d₁ gain κ ν B r T j c u P A F H => (match (Split.δ Nk r) with | a => (match ((((2 : ℝ) ^ T)⁻¹ : ℝ)) with | h => (match (Split.δ Nk (precision * gain * L)) with | ζ => (match (packetBase T j c u) with | z => (match (packetSignal P) with | X => (match ((fun p => X p / a)) with | Xn => (match (ENNReal.ofReal h * ν A) with | ref => ∃ (K ε pv θ : ℝ) (Se Er : Set Ev) (st : Ev → ℕ) (Gs : ℕ → Fin 3 → ℝ) (pal : MeasureTheory.Measure (Fin 2 → ℤ)), MeasureTheory.IsProbabilityMeasure ν ∧ P.totalDegree ≤ 2 ∧ MeasurableSet A ∧ 0 < ε ∧ ε ≤ ζ ∧ ε ≤ (a / h) * ζ ∧ 0 < a ∧ a ≤ K * h ∧ h ≤ ζ ∧ ζ ≤ 1 ∧ 2 ≤ K ∧ κ ≤ K ∧ K ^ Ep ≤ Nk ^ (loss * gain * L) ∧ θ = (a / h) * ζ ^ Ep / K ^ Ep ∧ K ^ Ep * ε ≤ θ ∧ 0 < pv ∧ K ^ Ep * pv ≤ θ ∧ MeasurableSet Se ∧ Se ⊆ H ∩ F ∧ Se ⊆ Er ∧ (∀ p ∈ Se, p.1 ∈ A ∧ p.2 ∈ Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ∧ p.2 ∈ Set.Icc (0 : ℝ) 1) ∧ 0 < ref ∧ ref / ENNReal.ofReal K ≤ ((ν.prod MeasureTheory.volume).restrict Se) Set.univ ∧ (∀ p ∈ Se, ‖z p‖ ≤ K ∧ ‖Split.v p.1‖ ≤ K ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧ |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤ K * B ^ 2) ∧ B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|) ∧ (∀ U : Set P3, MeasurableSet U → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U} ≤ ENNReal.ofReal K * ref * MeasureTheory.volume U) ∧ (∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U → ∀ f : P3 → ℝ, Measurable f → ((ν.prod MeasureTheory.volume).restrict Se) {p | z p ∈ U ∧ |Xn p - f (z p)| ≤ w} ≤ ENNReal.ofReal (K * w ^ d₁) * ref * MeasureTheory.volume U) ∧ (∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 → K ^ (100 : ℕ) * h * p ≤ a * w → Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k} ∧ (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ Se, (fun e => (fun i : Fin 3 => ⌊z e i / p⌋, ⌊Xn e / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁)) ∧ Measurable st ∧ (st '' Se).Finite ∧ (∀ p p' : Ev, st p = st p' → physicalCode z Xn ε p = physicalCode z Xn ε p') ∧ (∀ k : ℕ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 → ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ |inner ℝ n (Split.v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤ (1 / 2000000000000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k}) ∧ MeasureTheory.IsProbabilityMeasure pal ∧ (∀ k : ℕ, ∀ b : Fin 2 → ℤ, ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k ∧ (fun i : Fin 2 => ⌊Split.v p.1 i / pv⌋) = b} ≤ ENNReal.ofReal K * ((ν.prod MeasureTheory.volume).restrict Se) {p | st p = k} * pal {b}) ∧ (∀ k : ℕ, ∀ i : Fin 3, |Gs k i| ≤ K) ∧ (∀ p ∈ Se, |(∑ i : Fin 4, MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv i P) * (![1, p.1.2 3, p.1.2 4, p.1.2 5] : Fin 4 → ℝ) i) - ∑ i : Fin 3, (![1, p.1.2 3, p.1.2 4] : Fin 3 → ℝ) i * Gs (st p) i| ≤ θ) ∧ (∀ c' : Fin 3 → ℝ, ∃ Fc : Finset (Fin 3 → ℤ), (Fc.card : ℝ) ≤ K ∧ ∀ p ∈ Er, (∀ i : Fin 3, |z p i - c' i| ≤ θ) → (fun i : Fin 3 => ⌊Gs (st p) i / θ⌋) ∈ Fc) ∧ ((ν.prod MeasureTheory.volume).restrict Se) {w | ¬ ∃ Pq : Fin 3 → Polynomial ℝ, (∀ i, (Pq i).natDegree ≤ M) ∧ (∀ i n, |(Pq i).coeff n| ≤ K) ∧ (∀ i, |Gs (st w) i - (Pq i).eval ((w.2 - (j : ℝ) * h) / h)| ≤ θ) ∧ ∃ Et : Set ℝ, MeasurableSet Et ∧ Et ⊆ Set.Icc (0 : ℝ) 1 ∧ ENNReal.ofReal (1 / K) ≤ MeasureTheory.volume Et ∧ ∀ s ∈ Et, ((w.1, (j : ℝ) * h + h * s) : Ev) ∈ Er ∧ ∀ i, |Gs (st (w.1, (j : ℝ) * h + h * s)) i - (Pq i).eval s| ≤ θ} ≤ (1 / 10000 : ENNReal) * ((ν.prod MeasureTheory.volume).restrict Se) Set.univ))))))))

/-! ## The inverse tangent map -/

/-- The inverse of the isotropic tangent line map (`tanLine (isoPFrame t₀ q c sc) 0`). -/
def invLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (l : Ln) : Ln :=
  (l.1, ![q * l.2 0 + c 0 - t₀ * l.2 3, q * l.2 1 + c 1 - t₀ * l.2 4,
    l.2 2 / sc - t₀ * (l.2 5 / (sc * q)), l.2 3, l.2 4, l.2 5 / (sc * q)])

/-- The inverse of the tangent event map. -/
def invEvent (t₀ q : ℝ) (c : P2) (sc : ℝ) (p : Ev) : Ev :=
  (invLine t₀ q c sc p.1, t₀ + q * p.2)

lemma invLine_tanLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (l : Ln) :
    invLine t₀ q c sc (tanLine (isoPFrame t₀ q c sc) 0 l) = l := by
  rw [tanLine_iso t₀ q c sc hq]
  ext i
  · rfl
  · fin_cases i <;> simp [invLine] <;> field_simp <;> ring

lemma tanLine_invLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (l : Ln) :
    tanLine (isoPFrame t₀ q c sc) 0 (invLine t₀ q c sc l) = l := by
  rw [tanLine_iso t₀ q c sc hq]
  ext i
  · rfl
  · fin_cases i <;> simp [invLine] <;> field_simp <;> ring

lemma invEvent_tanEvent (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (p : Ev) :
    invEvent t₀ q c sc (tanEvent (isoPFrame t₀ q c sc) 0 p) = p := by
  unfold invEvent tanEvent
  rw [invLine_tanLine t₀ q c sc hq hsc]
  refine Prod.ext rfl ?_
  show t₀ + q * ((p.2 - t₀) / q) = p.2
  field_simp; ring

lemma tanEvent_invEvent (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (p : Ev) :
    tanEvent (isoPFrame t₀ q c sc) 0 (invEvent t₀ q c sc p) = p := by
  unfold invEvent tanEvent
  rw [tanLine_invLine t₀ q c sc hq hsc]
  refine Prod.ext rfl ?_
  show (t₀ + q * p.2 - t₀) / q = p.2
  field_simp; ring

lemma measurable_invLine (t₀ q : ℝ) (c : P2) (sc : ℝ) : Measurable (invLine t₀ q c sc) := by
  unfold invLine
  refine measurable_fst.prodMk ?_
  refine measurable_pi_iff.mpr (fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma measurable_invEvent (t₀ q : ℝ) (c : P2) (sc : ℝ) : Measurable (invEvent t₀ q c sc) :=
  ((measurable_invLine t₀ q c sc).comp measurable_fst).prodMk
    (measurable_const.add (measurable_snd.const_mul q))

/-! ## Mass transport -/

lemma measurable_tanEvent (Φ : PFrame) (a : Fin 4 → ℝ) : Measurable (tanEvent Φ a) :=
  ((measurable_tanLine Φ a).comp measurable_fst).prodMk
    ((measurable_snd.sub_const _).div_const _)

/-- The tangent product mass of a set is the original product mass of its pull-back, inside the
parent assignment, divided by `q * ν A₀`. -/
lemma tan_prod_apply (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : 0 < q)
    (ν : Measure Ln) [SFinite ν] (A₀ : Set Ln) (hA₀ : MeasurableSet A₀) {X : Set Ev}
    (hX : MeasurableSet X) :
    ((tanPrior (isoPFrame t₀ q c sc) 0 ν A₀).prod volume) X =
      (ENNReal.ofReal q * ν A₀)⁻¹ *
        (ν.prod volume) {p | p.1 ∈ A₀ ∧ tanEvent (isoPFrame t₀ q c sc) 0 p ∈ X} := by
  have hq' : (isoPFrame t₀ q c sc).F.q = q := rfl
  have hm : Measurable (Prod.map (tanLine (isoPFrame t₀ q c sc) 0) (id : ℝ → ℝ)) :=
    (measurable_tanLine _ 0).prodMap measurable_id
  rw [tanPrior_prod_apply (isoPFrame t₀ q c sc) 0 ν A₀ (by rw [hq']; exact hq) hX, muE,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_tnorm _ _) (hm hX),
    Measure.restrict_apply ((measurable_tnorm _ _) (hm hX))]
  congr 2
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- Restricted tangent masses of pull-backs: the scale `(q * ν A₀)⁻¹` is the same for every set. -/
lemma tan_restrict_apply (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : 0 < q) (hsc : sc ≠ 0)
    (ν : Measure Ln) [SFinite ν] (A₀ : Set Ln) (hA₀ : MeasurableSet A₀) {Se Y : Set Ev}
    (hSe : MeasurableSet Se) (hY : MeasurableSet Y) (hSeA : ∀ p ∈ Se, p.1 ∈ A₀) :
    (((tanPrior (isoPFrame t₀ q c sc) 0 ν A₀).prod volume).restrict
        (invEvent t₀ q c sc ⁻¹' Se)) (invEvent t₀ q c sc ⁻¹' Y) =
      (ENNReal.ofReal q * ν A₀)⁻¹ * ((ν.prod volume).restrict Se) Y := by
  have hinv := measurable_invEvent t₀ q c sc
  rw [Measure.restrict_apply (hinv hY), ← Set.preimage_inter,
    tan_prod_apply t₀ q c sc hq ν A₀ hA₀ (hinv (hY.inter hSe)),
    Measure.restrict_apply hY]
  congr 2
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff,
    invEvent_tanEvent t₀ q c sc hq.ne' hsc]
  constructor
  · rintro ⟨_, hY', hS'⟩; exact ⟨hY', hS'⟩
  · rintro ⟨hY', hS'⟩; exact ⟨hSeA p hS', hY', hS'⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
