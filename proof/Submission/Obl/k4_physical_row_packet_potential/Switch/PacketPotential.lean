-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketPotential.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The potential of one old packet: the switching curl bound of
`packet_curl_from_clauses_real` feeds `PotentialFits.physical_potential_from_qualified_rows`.
The field fit is needed only on long qualified time sets of the packet's
lines; on the events it follows by the whole-block Remez extension.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketBudget
import Submission.Obl.k4_physical_row_packet_potential.PhysicalPotential

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

/-- **The potential of one old packet.** The frozen potential clauses (degree,
coefficients `≤ Kpot h`, own-intercept fit `≤ a ζ` on every line of the packet
over the whole block) from the switching inputs and long qualified fits. -/
theorem packet_potential_from_switching (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (ν₀ : Measure Ln) [IsFiniteMeasure ν₀]
      (S : Set Ev) (hS : MeasurableSet S) (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (hpos : 0 < (ν₀.prod volume).real S)
      (a K : ℝ) (ha : 0 < a) (hK : 1 ≤ K)
      (hbaseK : ∀ z ∈ S, ‖packetBase T j c u z‖ ≤ K)
      (hvK : ∀ z ∈ S, ‖v z.1‖ ≤ K)
      (hPK : ∀ z ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp z.1 t) P| ≤ K)
      (εs : ℝ) (hεs : 0 < εs)
      {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
      [StandardBorelSpace σ] (st : Ev → σ) (hstm : Measurable st)
      (hrefine : ∀ z z', st z = st z' →
        packetState T j c u P a εs z = packetState T j c u P a εs z')
      (pv : ℝ) (hpv : 0 < pv) (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] (Kr : ℝ)
      (hKr : 0 ≤ Kr)
      (hrect : ∀ k (A : Set (Fin 2 → ℤ)), MeasurableSet A →
        (ν₀.prod volume) ({z | st z = k ∧ velBin pv z.1 ∈ A} ∩ S) ≤
          ENNReal.ofReal Kr * (ν₀.prod volume) (st ⁻¹' {k} ∩ S) * π A)
      (wstrip ps : ℝ) (hps : 0 ≤ ps)
      (hstrip : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
        ((ν₀.prod volume).restrict S)
            {z | st z = k ∧ |inner ℝ n (v z.1) - t| ≤ wstrip} ≤
          ENNReal.ofReal ps * ((ν₀.prod volume).restrict S) {z | st z = k})
      (r : ℝ) (hr : 0 < r) (hrw : 2 * (K + 1) * (r + pv) ≤ wstrip) (hr4 : r + pv ≤ 1 / 4)
      (Kc : ℝ) (hKc : 0 ≤ Kc)
      (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν₀.prod volume).restrict S) {z | packetBase T j c u z ∈ U} ≤
          ENNReal.ofReal Kc * volume U)
      (pc wc : ℝ) (hpc : 0 < pc) (hwc : 0 < wc)
      (hfin : (occupied S (fun z i => packetBase T j c u z i)
        (fun z => packetSignal P z / a) pc wc).Finite)
      (M : ℝ) (hM : ((occupied S (fun z i => packetBase T j c u z i)
        (fun z => packetSignal P z / a) pc wc).ncard : ℝ) ≤ M)
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D)
      (AT : ℝ) (hAT : 0 ≤ AT) (hcoeffT : ∀ i m, |(Tf i).coeff m| ≤ AT)
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
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ clock T)
      (hwidthH : simHeightError D (clock T / q) ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err)
          (εs + εs * K) (pv / 2) (a / clock T * εs + εs * (40 * K))
          ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (εs + εs * K + pv / 2)))) ^ D * AT)
          (max 1 (K + pv))
          (3 * ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (εs + εs * K + pv / 2)))) ^ D *
            ((D : ℝ) * AT))) ≤ a / clock T * wc / 2)
      (hwidthB : 6 * (εs + εs * K + pv / 2) ≤ pc / 2)
      (θ Λ Λ' : ℝ) (hθ : 0 < θ) (hΛ : 2 ≤ Λ) (hΛ' : 2 ≤ Λ')
      (hbudget : (Kr * (clock T / q)) ^ 6 *
            (Λ⁻¹ + 9216 * ((D : ℝ) + 2) * M * pc ^ 3 * (a / clock T) * wc *
              (max 1 (K + pv)) ^ 4 * Λ ^ cNorm / (θ * r ^ 9)) +
          6 * (q * ν₀.real univ / (ν₀.prod volume).real S + ps) +
          Kc * K ^ 3 / ((ν₀.prod volume).real S * Λ') < 1)
      (Kpot ζ : ℝ) (hcoeffBudget : ((D + 1 : ℕ) : ℝ) * 3 * AT ≤ Kpot)
      (herrorBudget : clock T * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err +
        3 * gradientBudget D U (Λ' ^ cCurl * θ) * V) ≤ a * ζ),
      ∃ Pot : MvPolynomial (Fin 3) ℝ,
        Pot.totalDegree ≤ D + 1 ∧ (∀ e, |Pot.coeff e| ≤ Kpot * clock T) ∧
        ∀ l ∈ Lines, ∀ t ∈ Icc ((j : ℝ) * clock T) (((j : ℝ) + 1) * clock T),
          |(MvPolynomial.eval (xp l t) P -
              MvPolynomial.eval (fun i => packetBase T j c u (l, t) i) Pot) -
            (MvPolynomial.eval (xp l ((j : ℝ) * clock T)) P -
              MvPolynomial.eval (fun i => packetBase T j c u (l, (j : ℝ) * clock T) i) Pot)| ≤
            a * ζ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := packet_curl_from_clauses_real D
  refine ⟨cNorm, cCurl, ?_⟩
  intro T j c u P hP ν₀ _ S hS hSunit htime hpos a K ha hK hbaseK hvK hPK εs hεs σ _ _ _ _ st hstm
    hrefine pv hpv π _ Kr
    hKr hrect wstrip ps hps hstrip r hr hrw hr4 Kc hKc hceil pc wc hpc hwc hfin M hM Tf hT AT
    hAT hcoeffT Lines hLines times η err hη hη1 herr htimes hfitL U V hU hV hbaseL hvelL q hq
    hqh hwidthH hwidthB θ Λ Λ' hθ hΛ hΛ' hbudget Kpot ζ hcoeffBudget herrorBudget
  -- the fit on the events, by the whole-block extension
  have hfitS : ∀ z ∈ S, |ParentSignal.rate P z.1 z.2 -
      ∑ i, direction z.1 i * MvPolynomial.eval (fun k => packetBase T j c u z k) (Tf i)| ≤
        (8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err := by
    intro z hz
    have hl := hLines z hz
    exact whole_block_row_of_long_times Tf D hT T j c u P hP z.1 (times z.1) hη hη1 herr
      (htimes z.1 hl).1 (htimes z.1 hl).2 (hfitL z.1 hl) z.2 (htime z hz)
  have hskew := hcurl T j c u P hP ν₀ S hS hSunit htime hpos a K ha hK hbaseK hvK hPK εs hεs
    st hstm hrefine pv hpv π Kr hKr hrect wstrip ps hps hstrip r hr hrw hr4 Kc hKc hceil pc wc hpc hwc hfin M
    hM Tf hT AT hAT hcoeffT _ (by positivity) hfitS q hq hqh hwidthH hwidthB θ Λ Λ' hθ hΛ hΛ'
    hbudget
  exact physical_potential_from_qualified_rows Tf D hT hAT (by positivity) herr hU hV hη hη1
    hcoeffT (fun i k m => hskew i k m) T j c u P hP Lines times hbaseL hvelL htimes hfitL
    hcoeffBudget herrorBudget

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
