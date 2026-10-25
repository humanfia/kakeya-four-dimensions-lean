-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.NonPotentialPacket, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/NonPotentialPacket.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). The non-potential clauses of the frozen packet for an event
set inside one actual old packet: reference mass, pointwise bounds, base
ceiling, moving-band cap and census, in the frozen form consumed by
`Switch.PacketSwitching.frozen_packet_final`.

The base ceiling and the moving-band cap are x1035's `OriginalPacketCaps`;
the census is any all-width census in the frozen form (for instance
`CapturedAncestorCensus.exists_captured_all_width_census`).
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPacketCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Lib.K4ParentSignalPreparation.Census
import Submission.Lib.K4GlobalParentSignal

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal

noncomputable section

namespace NonPotentialPacket

open ParentSource ParentSource.Native

/-- Events of an actual packet have a bounded packet base. -/
theorem unsheared_base_norm_le {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) {z : Ev} (hz : z ∈ p.F old) :
    ‖unshearedPacketBase p old z‖ ≤ 1 + 2 * (p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2)) := by
  rcases hp.2.2.2.2.2.2.2 old with
    ⟨hlev, hj, hdet, hcu, hQsum, hsize, hR, hRc, hAm, hFm, hfmt, hfit, hF, hrest⟩
  obtain ⟨hzE, hzA, hzt, -⟩ := hF z hz
  have hu := (hd.path_frame_bounds hp old).1
  set q : ℝ := ((2 : ℝ) ^ p.T (p.lev old))⁻¹ with hq_def
  have hq : 0 < q := by rw [hq_def]; positivity
  set t0 : ℝ := (p.j old : ℝ) * q with ht0
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  have hzt' : z.2 ∈ Icc ((p.j old : ℝ) / (2 : ℝ) ^ p.T (p.lev old))
      (((p.j old : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev old)) := hzt
  have herr : ‖y z.1 z.2 - p.c old - z.2 • p.u old‖ ≤ p.κ ^ 2 * q := by
    apply physical_error_le_of_frame hdet hκ hq (by simpa [q, div_eq_mul_inv] using hsize)
    exact ((hfit z.1 hzA).2.2 z.2 hzt').1
  have hs0 : 0 ≤ (z.2 - t0) / q := by
    apply div_nonneg _ hq.le
    have := hzt'.1
    rw [div_eq_mul_inv] at this
    simp only [ht0, hq_def]; linarith
  have hs1 : (z.2 - t0) / q ≤ 1 := by
    rw [div_le_one hq]
    have := hzt'.2
    rw [div_eq_mul_inv, add_mul, one_mul] at this
    simp only [ht0, hq_def]; linarith
  -- the two planar coordinates
  have hcoord (i : Fin 2) :
      |(y z.1 z.2 - p.c old - t0 • p.u old) i / q| ≤ p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2) := by
    have hsplit : (y z.1 z.2 - p.c old - t0 • p.u old) =
        (y z.1 z.2 - p.c old - z.2 • p.u old) + (z.2 - t0) • p.u old := by
      rw [sub_smul]; abel
    rw [hsplit, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_div, abs_le]
    have h1 : |(y z.1 z.2 - p.c old - z.2 • p.u old) i| ≤ p.κ ^ 2 * q :=
      (PiLp.norm_apply_le _ i).trans herr
    have h2 : |p.u old i| ≤ d.K k + 2 * p.κ ^ 2 := (PiLp.norm_apply_le _ i).trans hu
    have e1 : |(y z.1 z.2 - p.c old - z.2 • p.u old) i / q| ≤ p.κ ^ 2 := by
      rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]; exact h1
    have e2 : |(z.2 - t0) * p.u old i / q| ≤ d.K k + 2 * p.κ ^ 2 := by
      rw [mul_div_right_comm, abs_mul, abs_of_nonneg hs0]
      calc (z.2 - t0) / q * |p.u old i| ≤ 1 * (d.K k + 2 * p.κ ^ 2) :=
            mul_le_mul hs1 h2 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    rw [abs_le] at e1 e2
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hcoord0 : (y z.1 z.2 - p.c old - t0 • p.u old) 0 / q =
      unshearedPacketBase p old z 1 := by
    simp [unshearedPacketBase, y, x, ParentSource.xp, q, t0, PiLp.sub_apply, PiLp.smul_apply]
    ring
  have hcoord1 : (y z.1 z.2 - p.c old - t0 • p.u old) 1 / q =
      unshearedPacketBase p old z 2 := by
    simp [unshearedPacketBase, y, x, ParentSource.xp, q, t0, PiLp.sub_apply, PiLp.smul_apply]
    ring
  have htime : unshearedPacketBase p old z 0 = (z.2 - t0) / q := by
    simp [unshearedPacketBase, q, t0]
  calc ‖unshearedPacketBase p old z‖ ≤ ∑ i, |unshearedPacketBase p old z i| :=
        euclidean_norm_le_sum_abs _
    _ = |unshearedPacketBase p old z 0| + |unshearedPacketBase p old z 1| +
        |unshearedPacketBase p old z 2| := Fin.sum_univ_three _
    _ ≤ 1 + (p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2)) + (p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2)) := by
        rw [htime, ← hcoord0, ← hcoord1, abs_of_nonneg hs0]
        exact add_le_add (add_le_add hs1 (hcoord 0)) (hcoord 1)
    _ = _ := by ring

/-- **The non-potential frozen clauses of an event set in one old packet.** -/
theorem nonpotential_clauses
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set ParentSource.Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    (S : Set Ev) (hS : MeasurableSet S)
    (hSE : S ⊆ d.E k (p.γ old)) (hSbase : S ⊆ Q.base (p.γ old)) (hSF : S ⊆ p.F old)
    (hSgood : ∀ z ∈ S, z.1 ∈ Submission.Lib.K4GlobalParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    (hSvel : ∀ z ∈ S, ‖v z.1‖ ≤ d.K k)
    (hSB : ∀ z ∈ S, d.B k (p.γ old) / d.K k ≤
      |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k (p.γ old)))|)
    (hA : d.ν k (p.γ old) (p.A old) ≠ 0)
    {dens : ℝ} (hdens : 0 < dens)
    (hmass : ENNReal.ofReal dens *
      (d.ν k (p.γ old) (p.A old) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) ≤
        ((d.ν k (p.γ old)).prod volume) S)
    {d₁ : ℝ} (hd₁ : 0 ≤ d₁)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {εm Kcensus : ℝ} (hεm : 0 < εm) (hKc1 : 1 ≤ Kcensus)
    (hresolved : d.N k ^ (-(d.L - p.r (p.lev old))) ≤ 4 * εm)
    (hcensus : ∀ base hidden : ℝ, εm ≤ base → base ≤ 1 → εm ≤ hidden → hidden ≤ 1 →
      Kcensus ^ (100 : ℕ) * base ≤
        (δ (d.N k) (p.r (p.lev old)) / (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * hidden →
      (occupied S (fun z j => packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z j)
        (fun z => packetSignal (d.P k (p.γ old)) z / δ (d.N k) (p.r (p.lev old))) base hidden).Finite ∧
      ((occupied S (fun z j => packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z j)
        (fun z => packetSignal (d.P k (p.γ old)) z / δ (d.N k) (p.r (p.lev old)))
          base hidden).ncard : ℝ) ≤ Kcensus / (base ^ 3 * hidden ^ d₁))
    (K : ℝ) (hKdens : dens⁻¹ ≤ K)
    (hKbase : 1 + 2 * (p.κ ^ 2 + (d.K k + 2 * p.κ ^ 2)) ≤ K) (hKdK : d.K k ≤ K)
    (hKceil : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + ε) ≤ K)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + ε) ≤ K)
    (hKcensus : Kcensus ≤ K) :
    ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * d.ν k (p.γ old) (p.A old) / ENNReal.ofReal K ≤
        ((d.ν k (p.γ old)).prod volume).restrict S univ ∧
    (∀ z ∈ S, ‖packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z‖ ≤ K ∧ ‖v z.1‖ ≤ K ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp z.1 t) (d.P k (p.γ old))| ≤ K ∧
        |MvPolynomial.eval (xp z.1 t) (MvPolynomial.pderiv 3 (d.P k (p.γ old)))| ≤
          K * d.B k (p.γ old) ∧
        |MvPolynomial.eval (xp z.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3
          (d.P k (p.γ old))))| ≤ K * d.B k (p.γ old) ^ 2) ∧
      d.B k (p.γ old) / K ≤
        |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k (p.γ old)))|) ∧
    (∀ U : Set P3, MeasurableSet U →
      ((d.ν k (p.γ old)).prod volume).restrict S
          {z | packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z ∈ U} ≤
        ENNReal.ofReal K * (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
          d.ν k (p.γ old) (p.A old)) * volume U) ∧
    (∀ (w : ℝ), εm ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U → ∀ f : P3 → ℝ, Measurable f →
      ((d.ν k (p.γ old)).prod volume).restrict S
          {z | packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z ∈ U ∧
            |packetSignal (d.P k (p.γ old)) z / δ (d.N k) (p.r (p.lev old)) -
              f (packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z)| ≤ w} ≤
        ENNReal.ofReal (K * w ^ d₁) * (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
          d.ν k (p.γ old) (p.A old)) * volume U) ∧
    (∀ pm w : ℝ, εm ≤ pm → pm ≤ 1 → εm ≤ w → w ≤ 1 →
      K ^ (100 : ℕ) * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * pm ≤ δ (d.N k) (p.r (p.lev old)) * w →
      Set.Finite {q : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        (fun e => (fun i : Fin 3 =>
          ⌊packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) e i / pm⌋,
          ⌊packetSignal (d.P k (p.γ old)) e / δ (d.N k) (p.r (p.lev old)) / w⌋)) e = q} ∧
      (({q : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
        (fun e => (fun i : Fin 3 =>
          ⌊packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) e i / pm⌋,
          ⌊packetSignal (d.P k (p.γ old)) e / δ (d.N k) (p.r (p.lev old)) / w⌋)) e = q}).ncard : ℝ) ≤
        K / (pm ^ (3 : ℕ) * w ^ d₁)) := by
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hdK1 : 1 ≤ d.K k := hd.2.2.1.1 k
  have hK1 : 1 ≤ K := hdK1.trans hKdK
  have hK0 : 0 < K := by linarith
  have hB0 : 0 < d.B k (p.γ old) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ old)).2.1
  have hh0 : 0 < ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by positivity
  have ha0 : 0 < δ (d.N k) (p.r (p.lev old)) := by unfold δ; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- reference mass
    rw [Measure.restrict_apply_univ]
    refine le_trans ?_ hmass
    rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hK0, mul_comm (ENNReal.ofReal dens)]
    have hd' : ENNReal.ofReal K⁻¹ ≤ ENNReal.ofReal dens := by
      apply ENNReal.ofReal_le_ofReal
      rw [inv_le_comm₀ hK0 hdens]; exact hKdens
    calc ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * d.ν k (p.γ old) (p.A old) *
          ENNReal.ofReal K⁻¹
        = d.ν k (p.γ old) (p.A old) * ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev old))⁻¹ *
          ENNReal.ofReal K⁻¹ := by ring
      _ ≤ _ := by gcongr
  · -- pointwise bounds
    intro z hz
    have hg := hSgood z hz
    refine ⟨(unsheared_base_norm_le hd hp old (hSF hz)).trans hKbase, (hSvel z hz).trans hKdK,
      fun t ht => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hg t ht
      refine ⟨h1.trans hKdK, h2.trans ?_, h3.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right hKdK hB0.le
      · exact mul_le_mul_of_nonneg_right hKdK (by positivity)
    · refine le_trans ?_ (hSB z hz)
      exact div_le_div_of_nonneg_left hB0.le (by linarith) hKdK
  · -- base ceiling
    intro U hU
    have hc := OriginalPacketCaps.base_cap Q hpure hd hp old hr hrL S hS hSE hSbase hSF hA U hU
    refine hc.trans ?_
    gcongr
  · -- moving-band cap
    intro w hw hw1 U hU f hf
    have hprof' : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L := hprofile
    have hc := OriginalPacketCaps.moving_band_cap Q hpure hd hp old hr hrL S hS hSE hSbase hSF hA
      hd₁ hprof' (hεm.trans_le hw) (hresolved.trans (by linarith)) U hU f hf
    have hset : {z | packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z ∈ U ∧
        |packetSignal (d.P k (p.γ old)) z / δ (d.N k) (p.r (p.lev old)) -
          f (packetBase (p.T (p.lev old)) (p.j old) (p.c old) (p.u old) z)| ≤ w} =
        {z | unshearedPacketBase p old z ∈ U ∧
          |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z -
            f (unshearedPacketBase p old z)| ≤ w} := by
      ext z
      simp only [mem_setOf_eq]
      have : packetSignal (d.P k (p.γ old)) z / δ (d.N k) (p.r (p.lev old)) =
          physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z := by
        unfold physicalParentSignal packetSignal
        rw [div_eq_inv_mul]; rfl
      rw [this]; rfl
    rw [hset]
    refine hc.trans ?_
    gcongr
    all_goals first
      | exact Real.rpow_nonneg (hεm.le.trans hw) _
      | exact hKband
  · -- census
    intro pm w hpm hpm1 hw hw1 hshape
    have hshape' : Kcensus ^ (100 : ℕ) * pm ≤
        (δ (d.N k) (p.r (p.lev old)) / (((2 : ℝ) ^ p.T (p.lev old))⁻¹)) * w := by
      have hpow : Kcensus ^ (100 : ℕ) ≤ K ^ (100 : ℕ) :=
        pow_le_pow_left₀ (by linarith) hKcensus 100
      have h1 : Kcensus ^ (100 : ℕ) * pm * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ ≤
          δ (d.N k) (p.r (p.lev old)) * w := by
        calc _ ≤ K ^ (100 : ℕ) * pm * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ := by
              gcongr; exact hεm.le.trans hpm
          _ = K ^ (100 : ℕ) * ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * pm := by ring
          _ ≤ _ := hshape
      rw [div_mul_eq_mul_div, le_div_iff₀ hh0]
      exact h1
    obtain ⟨hfin, hcard⟩ := hcensus pm w hpm hpm1 hw hw1 hshape'
    refine ⟨hfin, hcard.trans ?_⟩
    have hden : 0 < pm ^ 3 * w ^ d₁ := by
      have := hεm.trans_le hpm
      have := hεm.trans_le hw
      positivity
    exact div_le_div_of_nonneg_right hKcensus hden.le

end NonPotentialPacket

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
