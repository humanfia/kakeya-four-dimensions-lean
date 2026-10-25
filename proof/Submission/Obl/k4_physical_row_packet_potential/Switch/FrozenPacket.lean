-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/FrozenPacket.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Assembly of the frozen `PhysicalPotentialPacket` of one old
packet. Every clause except the potential is an input in its frozen form;
the potential comes from `packet_potential_from_switching`, whose switching
inputs are exactly those frozen clauses (strip breadth, base ceiling, census)
together with per-state palette domination and the Cartesian field.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketPotential

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialNorming
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal

noncomputable section

namespace PacketSwitching

theorem ofReal_strip_ratio :
    ENNReal.ofReal (1 / 1000000000000 : ℝ) = (1 / 1000000000000 : ENNReal) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
  norm_num

/-- Restricting the line law to the packet's assignment does not change the
incidence law of an event set over assigned lines. -/
theorem restrict_assigned_prod {ν : Measure Ln} [SFinite ν] {A : Set Ln} (hA : MeasurableSet A)
    {S : Set Ev} (hSA : S ⊆ A ×ˢ univ) :
    ((ν.restrict A).prod volume).restrict S = (ν.prod volume).restrict S := by
  rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict,
    Measure.restrict_univ, Measure.restrict_restrict' (hA.prod MeasurableSet.univ),
    inter_eq_left.mpr hSA]

theorem restrict_assigned_prod_apply {ν : Measure Ln} [SFinite ν] {A : Set Ln}
    (hA : MeasurableSet A) {S : Set Ev} (hS : MeasurableSet S) (hSA : S ⊆ A ×ˢ univ)
    (X : Set Ev) : ((ν.restrict A).prod volume) (X ∩ S) = (ν.prod volume) (X ∩ S) := by
  rw [← Measure.restrict_apply' hS, ← Measure.restrict_apply' hS, restrict_assigned_prod hA hSA]

/-- **The frozen packet of one old block from its clauses and the switching.** -/
theorem frozen_packet_from_switching (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ (q : ℕ) (precision loss Nk L d₁ gain κ : ℝ) (ν : Measure Ln) [IsProbabilityMeasure ν]
      (B r : ℝ) (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (A : Set Ln) (hA : MeasurableSet A) (F H : Set Ev)
      (K ε : ℝ) (S : Set Ev)
      -- the scalar clauses
      (hε : 0 < ε) (hεζ : ε ≤ δ Nk (precision * gain * L))
      (hεa : ε ≤ (δ Nk r / ((2:ℝ)^T)⁻¹) * δ Nk (precision * gain * L))
      (ha : 0 < δ Nk r) (haK : δ Nk r ≤ K * ((2:ℝ)^T)⁻¹)
      (hhζ : ((2:ℝ)^T)⁻¹ ≤ δ Nk (precision * gain * L))
      (hK2 : 2 ≤ K) (hκK : κ ≤ K) (hKN : K ≤ Nk ^ (loss * gain * L))
      -- the event set
      (hS : MeasurableSet S) (hSHF : S ⊆ H ∩ F) (hSA : S ⊆ A ×ˢ univ)
      (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (href : 0 < ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A)
      (hmass : ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A / ENNReal.ofReal K ≤
        ((ν.prod volume).restrict S) univ)
      -- pointwise clauses (without the potential)
      (hpts : ∀ p ∈ S, ‖packetBase T j c u p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧
        (∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
            K * B ^ 2) ∧
        B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|)
      -- strip breadth, base ceiling, band cap, census (frozen forms)
      (hstrip : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k ∧
              |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k})
      (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U} ≤
          ENNReal.ofReal K * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hband : ∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U →
        ∀ f : P3 → ℝ, Measurable f →
        ((ν.prod volume).restrict S)
            {p | packetBase T j c u p ∈ U ∧ |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w} ≤
          ENNReal.ofReal (K * w ^ d₁) * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hcount : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
        K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * p ≤ δ Nk r * w →
        Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k} ∧
        (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁))
      -- the switching states: any refinement of the frozen state
      {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
      [StandardBorelSpace σ] (st : Ev → σ) (hstm : Measurable st)
      (hrefine : ∀ z z', st z = st z' →
        packetState T j c u P (δ Nk r) ε z = packetState T j c u P (δ Nk r) ε z')
      (hstripSt : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
        ((ν.prod volume).restrict S) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S) {p | st p = k})
      -- palette domination per switching state over velocity bins
      (pv : ℝ) (hpv : 0 < pv) (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] (Kr : ℝ)
      (hKr : 0 ≤ Kr)
      (hrect : ∀ k (Aw : Set (Fin 2 → ℤ)), MeasurableSet Aw →
        (ν.prod volume) ({z | st z = k ∧ velBin pv z.1 ∈ Aw} ∩ S) ≤
          ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S) * π Aw)
      (rp : ℝ) (hrp : 0 < rp) (hrw : 2 * (K + 1) * (rp + pv) ≤ K ^ (-100 : ℝ))
      (hr4 : rp + pv ≤ 1 / 4)
      -- the census used as switching target
      (pc wc : ℝ) (hpc0 : ε ≤ pc) (hpc1 : pc ≤ 1) (hwc0 : ε ≤ wc) (hwc1 : wc ≤ 1)
      (hpw : K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * pc ≤ δ Nk r * wc)
      -- the field and its long qualified fits
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D) (hDq : D + 1 ≤ q)
      (AT : ℝ) (hAT : 0 ≤ AT) (hcoeffT : ∀ i m, |(Tf i).coeff m| ≤ AT)
      (hcoeffBudget : ((D + 1 : ℕ) : ℝ) * 3 * AT ≤ K)
      (Lines : Set Ln) (hLines : ∀ z ∈ S, z.1 ∈ Lines) (times : Ln → Set ℝ)
      (η err : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (herr : 0 ≤ err)
      (htimes : ∀ l ∈ Lines, times l ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (times l))
      (hfitL : ∀ l ∈ Lines, ∀ s ∈ times l,
        |ParentSignal.rate P l (start T j + clock T * s) - ∑ i : Fin 3,
          direction l i * MvPolynomial.eval
            (fun i => packetBase T j c u (l, start T j + clock T * s) i) (Tf i)| ≤ err)
      (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
      (hbaseL : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T), ∀ i,
        |packetBase T j c u (l, t) i| ≤ U)
      (hvelL : ∀ l ∈ Lines, ∀ i, |direction l i| ≤ V)
      -- numerics
      (qd : ℝ) (hqd : 0 < qd) (hqdh : qd ≤ clock T)
      (hwidthH : simHeightError D (clock T / qd) ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err)
          (ε + ε * K) (pv / 2) (δ Nk r / clock T * ε + ε * (40 * K))
          ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D * AT)
          (max 1 (K + pv))
          (3 * ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D *
            ((D : ℝ) * AT))) ≤ δ Nk r / clock T * wc / 2)
      (hwidthB : 6 * (ε + ε * K + pv / 2) ≤ pc / 2)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (Kr * (clock T / qd)) ^ 6 *
            (Λ⁻¹ + 9216 * ((D : ℝ) + 2) * (K / (pc ^ (3 : ℕ) * wc ^ d₁)) * pc ^ 3 *
              (δ Nk r / clock T) * wc * (max 1 (K + pv)) ^ 4 * Λ ^ cNorm / (θ * rp ^ 9)) +
          6 * (qd * (ν A).toReal / (ν.prod volume).real S + 1 / 1000000000000) +
          K * (clock T * (ν A).toReal) * K ^ 3 / ((ν.prod volume).real S * Λ') < 1)
      (herrorBudget : clock T * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err +
        3 * gradientBudget D U (Λ' ^ cCurl * θ) * V) ≤ δ Nk r * δ Nk (precision * gain * L)),
      PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H := by
  obtain ⟨cNorm, cCurl, hpot⟩ := packet_potential_from_switching D
  refine ⟨cNorm, cCurl, ?_⟩
  intro q precision loss Nk L d₁ gain κ ν _ B r T j c u P hP A hA F H K ε S hε hεζ hεa ha haK hhζ
    hK2 hκK hKN hS hSHF hSA hSunit htime href hmass hpts hstrip hceil hband hcount σ _ _ _ _ st hstm
    hrefine hstripSt pv hpv π _ Kr hKr hrect rp hrp hrw hr4 pc wc hpc0 hpc1 hwc0 hwc1 hpw Tf hT hDq AT hAT hcoeffT
    hcoeffBudget Lines hLines times η err hη hη1 herr htimes hfitL U V hU hV hbaseL hvelL qd hqd
    hqdh hwidthH hwidthB θ Λ Λ' hθ hΛ hΛ' hbudget herrorBudget
  have hh : clock T = ((2:ℝ)^T)⁻¹ := rfl
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hpc : 0 < pc := hε.trans_le hpc0
  have hwc : 0 < wc := hε.trans_le hwc0
  -- the law of S is finite and positive
  have hfin : (ν.prod volume) S < ⊤ := by
    calc (ν.prod volume) S ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hSunit
      _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
      _ < ⊤ := by rw [Real.volume_Icc]; simp
  have hrestr : ((ν.prod volume).restrict S) univ = (ν.prod volume) S := by
    rw [Measure.restrict_apply_univ]
  have hpos : 0 < (ν.prod volume).real S := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ hfin.ne
    intro h0
    rw [hrestr, h0] at hmass
    have : ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A / ENNReal.ofReal K ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨href.ne', ENNReal.ofReal_ne_top⟩
    exact this (le_antisymm hmass bot_le)
  -- the same incidence law under the assigned prior
  have hlaw := restrict_assigned_prod (ν := ν) hA hSA
  have happ := restrict_assigned_prod_apply (ν := ν) hA hS hSA
  have hposA : 0 < ((ν.restrict A).prod volume).real S := by
    rw [measureReal_def, ← inter_self S, happ, inter_self, ← measureReal_def]
    exact hpos
  have hνA : (ν.restrict A).real univ = (ν A).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  have hνAtop : ν A ≠ ⊤ := measure_ne_top _ _
  -- the census at (pc, wc)
  obtain ⟨hfinC, hcardC⟩ := hcount pc wc hpc0 hpc1 hwc0 hwc1 hpw
  -- the potential
  obtain ⟨Pot, hdeg, hcoeff, hfit⟩ := hpot T j c u P hP (ν.restrict A) S hS hSunit htime hposA
    (δ Nk r) K ha hK1 (fun z hz => (hpts z hz).1) (fun z hz => (hpts z hz).2.1)
    (fun z hz t ht => ((hpts z hz).2.2.1 t ht).1) ε hε st hstm hrefine pv hpv π Kr hKr
    (fun k Aw hAw => by rw [happ, happ]; exact hrect k Aw hAw)
    (K ^ (-100 : ℝ)) (1 / 1000000000000) (by norm_num)
    (fun k n t hn => by
      rw [hlaw, ofReal_strip_ratio]
      exact hstripSt k n t hn)
    rp hrp hrw hr4 (K * (clock T * (ν A).toReal))
    (mul_nonneg hK0 (mul_nonneg (clock_pos T).le ENNReal.toReal_nonneg))
    (fun U hU => by
      rw [hlaw]
      convert hceil U hU using 2
      rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul (clock_pos T).le,
        ENNReal.ofReal_toReal hνAtop, hh])
    pc wc hpc hwc hfinC (K / (pc ^ (3 : ℕ) * wc ^ d₁)) hcardC Tf hT AT hAT hcoeffT Lines hLines
    times η err hη hη1 herr htimes hfitL U V hU hV hbaseL hvelL qd hqd hqdh hwidthH hwidthB
    θ Λ Λ' hθ hΛ hΛ'
    (by
      rw [hνA, measureReal_def, ← inter_self S, happ, inter_self, ← measureReal_def]
      exact hbudget)
    K (δ Nk (precision * gain * L)) hcoeffBudget herrorBudget
  refine ⟨K, ε, S, Pot, hε, hεζ, hεa, ha, haK, hhζ, hK2, hκK, hKN, hS, hSHF, href, hmass,
    hdeg.trans hDq, hcoeff, ?_, hstrip, hceil, hband, hcount⟩
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hpts p hp
  exact ⟨h1, h2, h3, h4, fun t ht => hfit p.1 (hLines p hp) t ht⟩

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
