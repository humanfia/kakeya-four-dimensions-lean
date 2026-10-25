-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/PacketBudget.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Numerics of the packet switching: with the census half-widths
as target widths, the switching volume is an explicit real expression, and
the whole budget of `packet_curl_from_clauses` is one real inequality.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketClauses

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

/-- The switching volume over census boxes, as a real expression. -/
theorem switchVolumeBound_census_le (D cNorm : ℕ) {ι : Type*} (I : Finset ι)
    {M pc wc θh r U θ Λ : ℝ} (hI : (I.card : ℝ) ≤ M) (hpc : 0 < pc) (hwc : 0 < wc)
    (hθh : 0 < θh) (hr : 0 < r) (hU : 0 < U) (hθ : 0 < θ) (hΛ : 0 < Λ) :
    switchVolumeBound D cNorm I (censusWidth pc wc θh) r U θ Λ ≤
      ENNReal.ofReal (Λ⁻¹ + 9216 * ((D : ℝ) + 2) * M * pc ^ 3 * θh * wc * U ^ 4 *
        Λ ^ cNorm / (θ * r ^ 9)) := by
  have hM : 0 ≤ M := (Nat.cast_nonneg _).trans hI
  have hw0 : censusWidth pc wc θh 0 = θh * wc / 2 := rfl
  have hws (a : Fin 3) : censusWidth pc wc θh a.succ = pc / 2 := rfl
  have hskew : r ^ 3 * switchSkewScale r U θ / Λ ^ cNorm = θ * r ^ 9 / (72 * U ^ 4 * Λ ^ cNorm) := by
    unfold switchSkewScale
    field_simp
    push_cast
    ring
  have hprod : ∏ a : Fin 3, ENNReal.ofReal (4 * censusWidth pc wc θh a.succ) =
      ENNReal.ofReal ((2 * pc) ^ 3) := by
    simp only [hws]
    rw [Fin.prod_univ_three, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hlast : 4 * (((D + 1 : ℕ) : ℝ) + 1) * (2 * censusWidth pc wc θh 0) /
      (r ^ 3 * switchSkewScale r U θ / Λ ^ cNorm) =
      288 * ((D : ℝ) + 2) * θh * wc * U ^ 4 * Λ ^ cNorm / (θ * r ^ 9) := by
    rw [hskew, hw0]
    push_cast
    field_simp
    ring
  unfold switchVolumeBound
  rw [hprod, hlast, ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr
  have hcard : (I.card : ENNReal) ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hI
  calc
    ((I.card : ENNReal) * ENNReal.ofReal ((2 * pc) ^ 3)) * 4 *
        ENNReal.ofReal (288 * ((D : ℝ) + 2) * θh * wc * U ^ 4 * Λ ^ cNorm / (θ * r ^ 9)) ≤
      (ENNReal.ofReal M * ENNReal.ofReal ((2 * pc) ^ 3)) * ENNReal.ofReal 4 *
        ENNReal.ofReal (288 * ((D : ℝ) + 2) * θh * wc * U ^ 4 * Λ ^ cNorm / (θ * r ^ 9)) := by
      rw [ENNReal.ofReal_ofNat]
      gcongr
    _ = ENNReal.ofReal (9216 * ((D : ℝ) + 2) * M * pc ^ 3 * θh * wc * U ^ 4 * Λ ^ cNorm /
        (θ * r ^ 9)) := by
      rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- **Curl bound of one old packet from its clauses, real budget.** The
target boxes are the census boxes themselves. -/
theorem packet_curl_from_clauses_real (D : ℕ) : ∃ cNorm cCurl : ℕ,
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
      (εfit : ℝ) (hεfit : 0 ≤ εfit)
      (hfit : ∀ z ∈ S, |ParentSignal.rate P z.1 z.2 -
        ∑ i, direction z.1 i * MvPolynomial.eval (fun k => packetBase T j c u z k) (Tf i)| ≤
          εfit)
      (q : ℝ) (hq : 0 < q) (hqh : q ≤ clock T)
      (hwidthH : simHeightError D (clock T / q) εfit (εs + εs * K) (pv / 2)
          (a / clock T * εs + εs * (40 * K))
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
          Kc * K ^ 3 / ((ν₀.prod volume).real S * Λ') < 1),
      ∀ i k m, |(pderiv k (Tf i) - pderiv i (Tf k)).coeff m| ≤ Λ' ^ cCurl * θ := by
  obtain ⟨cNorm, cCurl, hcurl⟩ := packet_curl_from_clauses D
  refine ⟨cNorm, cCurl, ?_⟩
  intro T j c u P hP ν₀ _ S hS hSunit htime hpos a K ha hK hbaseK hvK hPK εs hεs σ _ _ _ _ st hstm
    hrefine pv hpv π _ Kr
    hKr hrect wstrip ps hps hstrip r hr hrw hr4 Kc hKc hceil pc wc hpc hwc hfin M hM Tf hT AT
    hAT hcoeffT εfit hεfit hfit q hq hqh hwidthH hwidthB θ Λ Λ' hθ hΛ hΛ' hbudget
  have hh := clock_pos T
  have hK0 : 0 ≤ K := by linarith
  have hmass0 : 0 < (ν₀.prod volume) S := by
    rw [measureReal_def] at hpos
    exact ENNReal.toReal_pos_iff.mp hpos |>.1
  have hmassTop : (ν₀.prod volume) S ≠ ⊤ := by
    rw [measureReal_def] at hpos
    exact (ENNReal.toReal_pos_iff.mp hpos).2.ne
  have hmassEq : (ν₀.prod volume) S = ENNReal.ofReal ((ν₀.prod volume).real S) := by
    rw [measureReal_def, ENNReal.ofReal_toReal hmassTop]
  have hνEq : ν₀ univ = ENNReal.ofReal (ν₀.real univ) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hcard : (hfin.toFinset.card : ℝ) ≤ M := by
    rw [card_census_boxes]
    exact hM
  have hU : 0 < max 1 (K + pv) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hΛ0 : 0 < Λ := by linarith
  have hΛ'0 : 0 < Λ' := by linarith
  have hvol := switchVolumeBound_census_le D cNorm hfin.toFinset hcard hpc hwc
    (div_pos ha hh) hr hU hθ hΛ0
  apply hcurl T j c u P hP ν₀ S hS hSunit htime hmass0 a K ha hK hbaseK hvK hPK εs hεs st hstm
    hrefine pv hpv
    π (ENNReal.ofReal Kr) hrect wstrip (ENNReal.ofReal ps) hstrip r hr hrw hr4 (ENNReal.ofReal Kc)
    hceil pc wc hpc hwc hfin Tf hT AT hAT hcoeffT εfit hεfit hfit q hq hqh
    (censusWidth pc wc (a / clock T)) ⟨le_rfl, hwidthH⟩ (fun k => ⟨le_rfl, hwidthB⟩)
    θ Λ Λ' hθ hΛ hΛ'
  -- the ENNReal budget from the real one
  set m := (ν₀.prod volume).real S with hm
  set X := Λ⁻¹ + 9216 * ((D : ℝ) + 2) * M * pc ^ 3 * (a / clock T) * wc *
    (max 1 (K + pv)) ^ 4 * Λ ^ cNorm / (θ * r ^ 9) with hX
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hcard
  have hX0 : 0 ≤ X := by positivity
  have hm0 : 0 < m := hpos
  have h1 : (ENNReal.ofReal Kr * ENNReal.ofReal (clock T / q)) ^ 6 *
      switchVolumeBound D cNorm hfin.toFinset (censusWidth pc wc (a / clock T)) r
        (max 1 (K + pv)) θ Λ ≤ ENNReal.ofReal ((Kr * (clock T / q)) ^ 6 * X) := by
    rw [← ENNReal.ofReal_mul hKr, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    gcongr
  have h2 : 6 * ((ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal q * ENNReal.ofReal (ν₀.real univ)) +
      ENNReal.ofReal ps) = ENNReal.ofReal (6 * (q * ν₀.real univ / m + ps)) := by
    rw [← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_mul hq.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) hps,
      ← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  have h3 : (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal Kc * ENNReal.ofReal (K ^ 3)) *
      ENNReal.ofReal Λ'⁻¹ = ENNReal.ofReal (Kc * K ^ 3 / (m * Λ')) := by
    rw [← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_mul hKc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hmassEq, hνEq, h2, h3]
  calc
    _ ≤ ENNReal.ofReal ((Kr * (clock T / q)) ^ 6 * X) +
        ENNReal.ofReal (6 * (q * ν₀.real univ / m + ps)) +
        ENNReal.ofReal (Kc * K ^ 3 / (m * Λ')) := by gcongr
    _ = ENNReal.ofReal ((Kr * (clock T / q)) ^ 6 * X +
        6 * (q * ν₀.real univ / m + ps) + Kc * K ^ 3 / (m * Λ')) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hbudget
    _ = 1 := ENNReal.ofReal_one

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
