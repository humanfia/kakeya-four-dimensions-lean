import Submission.Obl.k4_raw_localized_native_systems.C.ScalarCandidates
import Submission.Obl.k4_raw_localized_native_systems.C.PredictorBounds
import Submission.Obl.k4_profile_density_bounds.Common

/-
Adapted from this LOT tree, o178, session x0596, `RecoveredCharts.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory MvPolynomial
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def recoveredAssignment {p : Data} {k : ℕ} (a : Atlas p k)
    (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (b : Fin a.C) (S : Set (Fin 5 → ℝ)) : Set (ℕ × (Fin 6 → ℝ)) :=
  a.A b ∩ scalarCoeff (p.P k (a.γ b)) (packetStart a b) (packetTimeLength a)
    (offset b) (tangent b) ⁻¹' S

def recoveredIncidence {p : Data} {k : ℕ} (a : Atlas p k)
    (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (b : Fin a.C) (S : Set (Fin 5 → ℝ)) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  a.F b ∩ Prod.fst ⁻¹' recoveredAssignment a offset tangent b S

def recoveredTest {p : Data} {k : ℕ} (a : Atlas p k)
    (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (b : Fin a.C) (R : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 4) ℝ :=
  nativeCorrection (p.P k (a.γ b))
    (scalarPredictor (packetStart a b) (packetTimeLength a) (offset b) (tangent b) R)

/-- A scalar predictor changes only the native test and restricts the original
assignment.  All frame geometry and both hidden derivatives are inherited. -/
theorem ProjectedPackets.recovered_chart
    {p : Data} {k Mp Dp Mq Dq Mo Do : ℕ} {loss h η d s m S U c ε : ℝ}
    (hp : Valid p) (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (out : ScalarCandidates (p.N k) d s c Mq Dq)
    (b : Fin a.atlas.C) (i : Fin out.count)
    (hc : 0 ≤ c) (hε : 0 ≤ ε) (hloss : loss ≤ ε)
    (hM : Mp ≤ Mo) (hD : Dp ≤ Do) (hDq : 2 * Dq ≤ Do)
    (hformat : p.N k ^ Mp + p.N k ^ Mq ≤ p.N k ^ Mo)
    (hcoeff : 81 * p.N k ^ Mp + 144 * p.N k * (p.N k ^ Mp) ^ 2 ≤ p.N k ^ Mo) :
    gchart (p.N k) Mo Do (p.N k ^ ε) a.atlas.T ((a.atlas.j b : ℕ) : ℝ) (c / 2)
      (p.B k (a.atlas.γ b)) (p.E k (a.atlas.γ b)) (a.atlas.c b) (a.atlas.u b)
      (a.atlas.Q b) (recoveredTest a.atlas a.offset a.tangent b (out.poly i))
      (recoveredAssignment a.atlas a.offset a.tangent b (out.assignment i))
      (recoveredIncidence a.atlas a.offset a.tangent b (out.assignment i)) True := by
  have hbase := a.known.1.2.2.1 b
  change gchart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ at hbase
  rw [a.native b] at hbase
  have horig := hbase
  obtain ⟨hQ, hcu, hQi, hQs, hP, hPc, hA, hF, hfmt, hlines, hpoints, hlist⟩ := hbase
  obtain ⟨hdeg, hco, hAm, hAf, hfit⟩ := out.tests i
  have hmA : MeasurableSet
      (recoveredAssignment a.atlas a.offset a.tangent b (out.assignment i)) :=
    hA.inter (hAm.preimage (scalarCoeff_measurable _ _ _ _ _))
  have hmF : MeasurableSet
      (recoveredIncidence a.atlas a.offset a.tangent b (out.assignment i)) :=
    hF.inter (hmA.preimage measurable_fst)
  have hnewfmt : ∀ n, gfmt 6 (p.N k ^ Mo) Do
        {z | (n, z) ∈ recoveredAssignment a.atlas a.offset a.tangent b (out.assignment i)} ∧
      gfmt 7 (p.N k ^ Mo) Do
        {z : Fin 7 → ℝ | ((n, fun j : Fin 6 => z j.castSucc), z 6) ∈
          recoveredIncidence a.atlas a.offset a.tangent b (out.assignment i)} := by
    intro n
    have hline := scalar_assignment_format _ hP (packetStart a.atlas b)
      (packetTimeLength a.atlas) (a.offset b) (a.tangent b) hAf n
    have hinc := scalar_assignment_incidence_format _ hP (packetStart a.atlas b)
      (packetTimeLength a.atlas) (a.offset b) (a.tangent b) hAf n
    refine ⟨gfmt_mono hformat (max_le hD hDq) (gfmt_inter (hfmt n).1 hline), ?_⟩
    have heq : {z : Fin 7 → ℝ | ((n, fun j : Fin 6 => z j.castSucc), z 6) ∈
          recoveredIncidence a.atlas a.offset a.tangent b (out.assignment i)} =
        {z : Fin 7 → ℝ | ((n, fun j : Fin 6 => z j.castSucc), z 6) ∈ a.atlas.F b} ∩
          {z : Fin 7 → ℝ | scalarCoeff (p.P k (a.atlas.γ b)) (packetStart a.atlas b)
            (packetTimeLength a.atlas) (a.offset b) (a.tangent b)
            (n, fun j : Fin 6 => z j.castSucc) ∈ out.assignment i} := by
      ext z
      constructor
      · rintro ⟨hz, _, hs⟩
        exact ⟨hz, hs⟩
      · rintro ⟨hz, hs⟩
        exact ⟨hz, (hpoints _ hz).2.1, hs⟩
    rw [heq]
    exact gfmt_mono hformat (max_le hD hDq) (gfmt_inter (hfmt n).2 hinc)
  have hmono := gchart_mono horig (hp.scale_ge_one k) hM hD
    (Real.rpow_pos_of_pos (hp.scale_pos k) loss)
    (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) hloss)
    (hp.B_pos k _).le (fun _ => True.intro)
  have hrestrict := gchart_restrict hmono
    (fun _ hz => hz.1) (fun _ hz => hz.1) (fun _ hz => hz.2) hmA hmF hnewfmt True.intro
  apply gchart_nativeCorrection hrestrict ((scalarPredictor_degree _ _ _ _ _).trans hdeg)
  · intro e
    apply (nativeCorrection_coefficient_bound _ hP (packetStart a.atlas b)
      (packetTimeLength a.atlas) (a.offset b) (a.tangent b) (out.poly i) hdeg
      (one_le_pow₀ (hp.scale_ge_one k))
      (by rw [abs_of_nonneg (packetStart_mem_unit a.atlas b).1]
          exact (packetStart_mem_unit a.atlas b).2)
      (a.coordinate_bound b).2.2 (a.coordinate_bound b).1 (a.coordinate_bound b).2.1
      (hp.scale_pos k).le (pow_nonneg (hp.scale_pos k).le _) hPc hco e).trans hcoeff
  · change gδ (p.N k) (c / 2) ≤ gδ (p.N k) 0
    have hn : 0 ≤ c / 2 * Real.log (p.N k) / Real.log 2 := by
      exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (hp.scale_ge_one k)))
        (Real.log_pos (by norm_num)).le
    have hflo : (0 : ℤ) ≤ ⌊c / 2 * Real.log (p.N k) / Real.log 2⌋ :=
      Int.floor_nonneg.mpr hn
    simp only [gδ, zero_mul, zero_div, Int.floor_zero, neg_zero, zpow_zero]
    simpa only [zpow_zero] using
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (show -(⌊c / 2 * Real.log (p.N k) / Real.log 2⌋ : ℤ) ≤ 0 by omega))
  · intro l hl t ht
    have ht' : t ∈ Set.Icc (packetStart a.atlas b)
        (packetStart a.atlas b + packetTimeLength a.atlas) := by
      simpa only [packetStart, packetTimeLength, add_div] using ht
    have hraw := scalar_fit_nativeCorrection _ hP (packetStart a.atlas b)
      (packetTimeLength a.atlas) (a.offset b) (a.tangent b) (out.poly i) l
      (packetTimeLength_pos a.atlas)
      (fun u hu => hfit _ hl.2 u hu) ht'
    rw [eval_nativeCorrection] at hraw
    apply hraw.trans
    have hscale : p.N k ^ (-c) ≤ gδ (p.N k) (c / 2) :=
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)).trans
        (Submission.Obl.k4_profile_density_bounds.width_bounds (hp.scale_pos k) (c / 2)).1
    exact hscale.trans (le_mul_of_one_le_left (gδ_pos _ _).le
      (Real.one_le_rpow (hp.scale_ge_one k) hε))

end
end Submission.Obl.k4_raw_localized_native_systems.C
