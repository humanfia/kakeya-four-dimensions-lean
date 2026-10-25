-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/UniformReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.SourceCoordinates
import Submission.Obl.k4_finite_affine_candidate_return.ReturnLosses
import Submission.Obl.k4_finite_affine_candidate_return.ReturnMassNumerics
import Submission.Obl.k4_finite_affine_candidate_return.NoCandidateFrames
import Submission.Obl.k4_finite_affine_candidate_return.RelativeBlocks
import Submission.Obl.k4_finite_affine_candidate_return.CenteredStripReturn
import Submission.Obl.k4_finite_affine_candidate_return.DominatedMassReturn
import Submission.Obl.k4_finite_affine_candidate_return.DominatedQuadraticReturn
import Submission.Obl.k4_finite_affine_candidate_return.PathMass
import Submission.Obl.k4_finite_affine_candidate_return.ReturnThickness
import Submission.Obl.k4_finite_affine_candidate_return.StripWidthReturn

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4XInterface
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

/-- Every candidate in an explicit affine native source returns to the original
full-prior path, with an output format fixed before every actual loss. -/
theorem uniform_source_return : SourceReturn := by
  intro n M
  refine ⟨sourceOutputExponent n M, ?_⟩
  intro d₁ κ₁ ℓ ρ gain ε unit Nk L W ω ν E B f m sgrid δ₀ Mp Dp σ p H st
    hp hH hsource R hR hRn ε' hε' hε'max hcand
  rcases hsource with ⟨hn, hM, hNk, hL, hd₁, hℓ, hρ, hρmax, hε, hunit,
    hunitn, hgain, hgainmax, h100, hNt, hNt2, hK1, hKmax,
    parent, J, t₀, q₀, c₀, u₀, D₀, correction, old,
    hJ1, hJmax, hκJ, hν, hAparent, hAprior, hB, ht₀, hq₀, hD₀,
    hb, hνst, hρst, hbase, hbudget, hPbudget, hlabels⟩
  letI : IsProbabilityMeasure (ν (p.world parent)) := hν
  have hNk0 : 0 < Nk := by linarith only [hNk]
  have hNk1 : 1 ≤ Nk := by linarith only [hNk]
  have hJ0 : 0 < J := by linarith only [hJ1]
  have hq₀pos : 0 < q₀ := by rw [hq₀]; positivity
  have hδparent : 0 < δ Nk (p.r (p.lev parent)) := by exact gδ_pos _ _
  let Φ := affineSourceFrame t₀ q₀ (B (p.world parent) / δ Nk (p.r (p.lev parent))) c₀ u₀ D₀
  have hΦq : Φ.F.q = q₀ := rfl
  have hΦb : st.b = hiddenShear Φ.eb correction :=
    hb.trans (affineCoefficients_eq_hiddenShear _ _ _ _ _ _ _)
  have hνE : st.ν = nuE (ν (p.world parent)) (p.assigned parent) := hνst
  let source := H (p.world parent) ∩ (p.assigned parent ×ˢ Icc t₀ (t₀ + q₀))
  have hρE : st.ρ ≤ ENNReal.ofReal J •
      muE (ν (p.world parent)) (p.assigned parent) t₀ q₀ source := hρst
  rcases hcand with ⟨s, v, i, hsR, hsmax, hvR, hvmax, hsv, hcand⟩
  have hvpos : 0 < v := (inv_pos.mpr (by linarith only [hR])).trans_le hvR
  have hsone : s ≤ 1 := by linarith only [hsv, hvpos]
  have hsn : (n : ℝ)⁻¹ ≤ s := (inv_anti₀ (by linarith only [hR]) hRn).trans hsR
  obtain ⟨hworld, hA, hAsub, hBmeas, hBsub, hAprior', hI, hdepth, hchild,
    hdet, hfloorH, hQbudget, hFbudget⟩ := hlabels s hsn hsone i
  have hgainbounds := return_gain_bounds n hn unit ρ gain R v L
    (p.r (p.lev (old s i))) hunit hunitn hρ hρmax hgainmax hR hRn hvR hvmax hL hchild
  have htime := relative_time_length t₀ q₀ hq₀pos (p.T (p.lev (old s i))) (st.T s)
    (p.bin (old s i)) (st.j s i) hI
  have hlosses := return_relative_losses n hn unit L ρ R v ε' hunit hL hρ hR hRn hvR hε'max
  let A := ρ * unit * v * L
  let e := ρ * unit * L / (1000000 * ((n : ℝ) + 1))
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hepos : 0 < e := by dsimp only [e]; positivity
  have hJpow : J ≤ Nk ^ (ε / 1000000) := hJmax
  have hKpow : st.K ≤ Nk ^ e := by
    apply hKmax.trans_eq
    rw [hNt, ← Real.rpow_mul hNk0.le]
    congr 1
    dsimp only [e]
    ring
  have hfitpow : st.N ^ ε' ≤ Nk ^ (A / 4) := by
    rw [hNt, ← Real.rpow_mul hNk0.le]
    exact Real.rpow_le_rpow_of_exponent_le hNk1 hlosses.2
  have hgainL : gain * L ≤ e := by
    have h := mul_le_mul_of_nonneg_right hgainmax hL.le
    convert h using 1 <;> dsimp only [e] <;> ring
  have hallow := return_loss_absorption Nk ε A e (gain * L) J st.K (st.N ^ ε') hNk1 hε
    hApos.le hlosses.1 hgainL hJ0.le (zero_le_one.trans hK1) (by positivity)
    hJpow hKpow hfitpow (by linarith only [h100])
  have htimeΦ : Φ.F.q / (2 : ℝ) ^ st.T s = ((2 : ℝ) ^ p.T (p.lev (old s i)))⁻¹ := htime
  have hmassQuad := native_mass_coefficient_return Nk st.N (unit * L) d₁ v ε' (A + ε) J q₀
    hNk0 hNt hJ0 hq₀pos (p.T (p.lev (old s i))) (st.T s) htime hallow.2.1
  have hmassStrip := native_mass_coefficient_return Nk st.N (unit * L) 0 v ε' (A + ε) J q₀
    hNk0 hNt hJ0 hq₀pos (p.T (p.lev (old s i))) (st.T s) htime hallow.2.1
  have hsizeParts : J ≤ Nk ^ M ∧ st.N ≤ Nk ^ M ∧
      |δ Nk (p.r (p.lev parent))| ≤ Nk ^ M ∧
      (∑ e : Fin 4, |correction e|) ≤ Nk ^ M ∧
      |B (p.world parent)| ≤ Nk ^ M ∧ |(δ Nk (p.r (p.lev parent)))⁻¹| ≤ Nk ^ M ∧
      |q₀⁻¹| + |t₀| + ‖c₀‖ + ‖u₀‖ + (∑ e : Fin 2, ∑ f : Fin 2, |D₀⁻¹ e f|) ≤ Nk ^ M := by
    have hNell₀ : 0 ≤ st.N ^ ℓ := Real.rpow_nonneg (by linarith only [hNt2]) _
    have hδ₀ := abs_nonneg (δ Nk (p.r (p.lev parent)))
    have hδi₀ := abs_nonneg (δ Nk (p.r (p.lev parent)))⁻¹
    have hB₀ := abs_nonneg (B (p.world parent))
    have hBi₀ := abs_nonneg (B (p.world parent))⁻¹
    have ht₀' := abs_nonneg t₀
    have hq₀' := abs_nonneg q₀
    have hqi₀ := abs_nonneg q₀⁻¹
    have hc₀' := norm_nonneg c₀
    have hu₀' := norm_nonneg u₀
    have hc₀sum : 0 ≤ ∑ e : Fin 4, |correction e| := by positivity
    have hD₀sum : 0 ≤ ∑ e : Fin 2, ∑ f : Fin 2, (|D₀ e f| + |D₀⁻¹ e f|) := by positivity
    have hDi : (∑ e : Fin 2, ∑ f : Fin 2, |D₀⁻¹ e f|) ≤
        ∑ e : Fin 2, ∑ f : Fin 2, (|D₀ e f| + |D₀⁻¹ e f|) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      exact le_add_of_nonneg_left (abs_nonneg _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hbudget, hNt2, hJ1, hNell₀, hδ₀, hδi₀, hB₀, hBi₀,
        ht₀', hq₀', hqi₀, hc₀', hu₀', hc₀sum, hD₀sum, hDi]
  rcases hsizeParts with ⟨hJH, hNtH, hδH, hcorrH, hBH, hδinvH, hframeH⟩
  have hHfmt : 1 ≤ Nk ^ M := one_le_pow₀ hNk1
  have hsubst : Φ.substBudget ≤ 6 * (Nk ^ M) ^ 2 := by
    apply Φ.source_substBudget_le (Nk ^ M) hHfmt hframeH
    change |B (p.world parent) / δ Nk (p.r (p.lev parent))| ≤ (Nk ^ M) ^ 2
    rw [div_eq_mul_inv, abs_mul]
    exact (mul_le_mul hBH hδinvH (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hApriorOld : 0 < ν (p.world (old s i)) (p.assigned (old s i)) := by
    simpa only [hworld] using hAprior'
  rcases hcand with hquad | hstrip
  · obtain ⟨Q, hQ, hQcoeff, hQmass⟩ := hquad
    let δp := δ Nk (p.r (p.lev parent))
    let anew := δ Nk (p.r (p.lev (old s i)) + (unit * v) * L)
    let C := Nk ^ (A + ε)
    have hC : C = Nk ^ (ρ * (unit * v) * L + ε) := by
      dsimp only [C, A]
      congr 1
      ring
    have hthick := tangent_thickness_comparison hNk1 (p.r (p.lev parent))
      (p.r (p.lev (old s i))) (unit * L) s v e hdepth
    have hshift : p.r (p.lev (old s i)) + (unit * L) * v =
        p.r (p.lev (old s i)) + (unit * v) * L := by ring
    rw [← hNt, hshift] at hthick
    have hfitAllow := return_fit_allowances (by positivity : 0 ≤ st.N ^ ε')
      (gδ_pos Nk (p.r (p.lev (old s i)) + (unit * v) * L)).le
      (by positivity : 0 ≤ δp * st.N ^ (-s - v)) hthick.1 hthick.2 hallow.1
    have hfirst : st.N ^ ε' ≤ C := hfitpow.trans
      (Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith only [hApos, hε]))
    have hcoeffOut := source_output_coefficient_bound Nk hNk n M Φ correction δp st.N R
      (∑ e ∈ (st.F s i).support, |(st.F s i).coeff e|)
      (∑ e ∈ st.P.support, |st.P.coeff e|) hδH hcorrH hsubst
      (by linarith only [hNt2]) hNtH hRn (by positivity) (by positivity) hFbudget hPbudget Q hQ hQcoeff
    refine ⟨old s i, unit * v, hgainbounds.1, hgainbounds.2.1, hgainbounds.2.2,
      hApriorOld, Or.inl ⟨Φ.affineLift correction δp Q,
        (Φ.totalDegree_affineLift_le correction δp Q).trans hQ, hcoeffOut, ?_⟩⟩
    have hExp : -((d₁ + ρ) * (unit * v) * L) - ε =
        -(d₁ * (unit * L) * v) - (A + ε) := by dsimp only [A]; ring
    have hcoef : ENNReal.ofReal (Nk ^ (-((d₁ + ρ) * (unit * v) * L) - ε) /
        (2 : ℝ) ^ p.T (p.lev (old s i))) ≤ ENNReal.ofReal Φ.F.q *
        ((ENNReal.ofReal J)⁻¹ * ENNReal.ofReal (st.N ^ (-d₁ * v - ε') / (2 : ℝ) ^ st.T s)) := by
      simpa only [hExp, hΦq] using hmassQuad
    have hInv : (st.N ^ ε')⁻¹ = st.N ^ (-ε') := (Real.rpow_neg (by linarith only [hNt2]) ε').symm
    have hQmass' : ENNReal.ofReal (st.N ^ (-d₁ * v - ε') / (2 : ℝ) ^ st.T s) *
        nuE (ν (p.world parent)) (p.assigned parent) (p.assigned (old s i)) ≤ st.ρ
        {z | z.1 ∈ st.B s i ∧ z.2 ∈ IS (st.T s) (st.j s i) ∧
          fitS (hiddenShear Φ.eb correction) (st.N ^ ε') (st.N ^ (-s - v)) Q z.1
            (IS (st.T s) (st.j s i)) ∧
          (st.N ^ ε')⁻¹ ≤ |eval (exS (hiddenShear Φ.eb correction) z.1 z.2) (pderiv 3 Q)|} := by
      simpa only [hνE, hA, hΦb, hInv] using hQmass
    have hout := dominated_affine_quadratic_return (ν (p.world parent))
      (p.assigned parent) (p.assigned (old s i)) (st.B s i)
      (hp.assigned_measurable _) hBmeas hAsub (by simpa only [hA] using hBsub)
      hAprior.ne' (measure_ne_top _ _) Φ hq₀pos correction δp (B (p.world parent))
      (st.N ^ (-s - v)) anew (st.N ^ ε') C hδparent hB.le (by positivity)
      (gδ_pos _ _) (by positivity) rfl (st.T s) (st.j s i) _ hI Q source
      (H (p.world parent)) Set.inter_subset_left st.ρ (ENNReal.ofReal J)
      (ENNReal.ofReal_ne_zero_iff.mpr hJ0) ENNReal.ofReal_ne_top hρE
      hfitAllow.1 hfirst hfitAllow.2 _ _ hcoef hQmass'
    simpa only [hworld, hC] using hout
  · obtain ⟨z, hz, hzMass⟩ := hstrip
    by_contra hno
    have hMc : M + 1 ≤ sourceOutputExponent n M := by
      have h := Nat.mul_le_mul_left M (by omega : 1 ≤ 2 * n + 20)
      simp only [mul_one] at h
      dsimp only [sourceOutputExponent]
      omega
    have hbias : 2 * p.κ ≤ Nk ^ sourceOutputExponent n M := by
      calc
        _ ≤ 2 * J := mul_le_mul_of_nonneg_left hκJ (by norm_num)
        _ ≤ 2 * Nk ^ M := mul_le_mul_of_nonneg_left hJH (by norm_num)
        _ ≤ Nk * Nk ^ M := mul_le_mul_of_nonneg_right hNk (by positivity)
        _ = Nk ^ (M + 1) := by rw [pow_succ]; ring
        _ ≤ _ := pow_le_pow_right₀ hNk1 hMc
    have hb3 (l : Trajectory) : st.b l 3 = Φ.eb l 3 := by
      rw [hΦb]
      exact (hiddenShear_base Φ.eb correction l).2.2.1
    have hb4 (l : Trajectory) : st.b l 4 = Φ.eb l 4 := by
      rw [hΦb]
      exact (hiddenShear_base Φ.eb correction l).2.2.2
    let V : Set Incidence := {z | z ∈ H (p.world parent) ∧ z.1 ∈ p.assigned (old s i) ∧
      z.2 ∈ Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
        (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i)))}
    have hV (z : Incidence) (hz : z ∈ V) : z ∈ H (p.world (old s i)) ∧
        z.1 ∈ p.assigned (old s i) ∧
        z.2 ∈ Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
          (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i))) := by
      change z ∈ H (p.world parent) ∧ z.1 ∈ p.assigned (old s i) ∧
        z.2 ∈ Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
          (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i))) at hz
      simpa only [hworld] using hz
    have hAuxFloor : ENNReal.ofReal (Nk ^ (-ρ * gain * L - ε) /
        (2 : ℝ) ^ p.T (p.lev (old s i))) * ν (p.world (old s i)) (p.assigned (old s i)) ≤
        (ν (p.world (old s i))).prod volume V := by
      rw [hworld]
      apply (mul_le_mul' (auxiliary_strip_coefficient_bound Nk ρ gain L ε J
        (p.T (p.lev (old s i))) hNk1 hρ.le hgain.le hL.le hε hJ0 hJmax) le_rfl).trans hfloorH
    have hVpos : 0 < ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev (old s i)))⁻¹ / J) *
        ν (p.world parent) (p.assigned (old s i)) := by positivity
    have hVne : V.Nonempty := by
      by_contra he
      have hF : (ν (p.world parent)).prod volume V = 0 := by rw [Set.not_nonempty_iff_eq_empty.mp he]; simp
      exact (not_le_of_gt hVpos) (hfloorH.trans_eq hF)
    have hparent (z : Incidence) (hz : z ∈ V) (e : Fin 2) :
        |(WithLp.toLp 2 ![Φ.eb z.1 3, Φ.eb z.1 4]) e| ≤ J := by
      have h := hbase z.1 (hAsub hz.2.1)
      have ha₀ := abs_nonneg (st.b z.1 0)
      have ha₁ := abs_nonneg (st.b z.1 1)
      have ha₃ := abs_nonneg (st.b z.1 3)
      have ha₄ := abs_nonneg (st.b z.1 4)
      fin_cases e
      · change |Φ.eb z.1 3| ≤ J
        rw [← hb3]
        linarith only [h, ha₀, ha₁, ha₃, ha₄]
      · change |Φ.eb z.1 4| ≤ J
        rw [← hb4]
        linarith only [h, ha₀, ha₁, ha₃, ha₄]
    have hauxupper : gain ≤ 1 / 8 := hgainbounds.1.trans hgainbounds.2.1
    have hauxroom : p.r (p.lev (old s i)) + 2 * gain * L ≤ L := by
      have h := mul_le_mul_of_nonneg_right hgainbounds.1 hL.le
      linarith only [h, hgainbounds.2.2]
    let Mrel := relativeVelocityFrame q₀ (((2 : ℝ) ^ p.T (p.lev (old s i)))⁻¹) D₀ (p.frame (old s i))
    have hrows := relative_rows_of_no_original_candidate hp hNk0 (sourceOutputExponent n M)
      d₁ ρ gain ε H hno (old s i) gain le_rfl hauxupper hauxroom hApriorOld hbias
      V hVne hV hAuxFloor Φ J hJ0.le hparent
    have hrowBound : ‖WithLp.toLp 2 (fun f => Mrel 0 f)‖ ≤ 2 * J * Nk ^ (gain * L) := by
      apply (hrows 0).trans
      have hInv : (Nk ^ (ρ * gain * L + ε) * Nk ^ (-gain * L))⁻¹ =
          Nk ^ (gain * L - (ρ * gain * L + ε)) := by
        rw [← Real.rpow_add hNk0, ← Real.rpow_neg hNk0.le]
        congr 1
        ring
      rw [div_eq_mul_inv, hInv]
      have hprod : 0 ≤ ρ * gain * L := by positivity
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNk1 (by linarith only [hprod, hε])) (by positivity)
    have hcoord (f : Fin 2) : |Mrel 0 f| ≤ ‖WithLp.toLp 2 (fun f => Mrel 0 f)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp 2 (fun f => Mrel 0 f)) f
    have hrowSum : |Mrel 0 0| + |Mrel 0 1| ≤ 4 * J * Nk ^ (gain * L) := by
      linarith only [hcoord 0, hcoord 1, hrowBound]
    have hdetM : st.N ^ (-ℓ * s) / st.K ≤ |Mrel.det| := hdet
    have hMrel : Mrel.det ≠ 0 := abs_pos.mp
      ((by positivity : 0 < st.N ^ (-ℓ * s) / st.K).trans_le hdetM)
    let width := st.N ^ ε' * st.N ^ (-ℓ * s - v)
    have hwidth₀ := strip_width_return_bound Mrel hMrel (z 1) Nk st.N (unit * L) ℓ s v ε'
      (gain * L) J st.K (A + ε) hNk0 hNt (by linarith only [hK1]) hrowSum hdetM hallow.2.2
    have hwidth : 2 * (width / stripRowLength Mrel (z 1)) ≤
        Nk ^ (ρ * (unit * v) * L + ε) * Nk ^ (-(unit * v) * L) := by
      have hleft : -(unit * L * v) = -(unit * v) * L := by ring
      have hright : A + ε = ρ * (unit * v) * L + ε := by dsimp only [A]; ring
      simpa only [width, hleft, hright] using hwidth₀
    obtain ⟨a, bias, ha, _, hstripOld⟩ := Φ.strip_return hq₀pos.ne' hD₀
      (p.T (p.lev (old s i))) (p.velocity (old s i)) (p.frame (old s i))
      (hp.chart (old s i)).1 z width
    let X : Set Incidence := {p | p.1 ∈ st.B s i ∧ p.2 ∈ IS (st.T s) (st.j s i) ∧
      |Φ.eb p.1 4 - z 0 - z 1 * Φ.eb p.1 3| ≤ width}
    have hXm : MeasurableSet X := measurableSet_stripEvent Φ.measurable_eb (st.B s i) hBmeas
      (st.T s) (st.j s i) z width
    have hXfloor : ENNReal.ofReal (st.N ^ (-ε') / (2 : ℝ) ^ st.T s) *
        nuE (ν (p.world parent)) (p.assigned parent) (p.assigned (old s i)) ≤ st.ρ X := by
      simpa only [hνE, hA, hb3, hb4] using hzMass
    let Y : Set Incidence := {zz | zz ∈ H (p.world parent) ∧ zz.1 ∈ p.assigned (old s i) ∧
      zz.2 ∈ Icc ((p.bin (old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (old s i)))
        (((p.bin (old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (old s i))) ∧
      InStrip (p.T (p.lev (old s i))) (p.velocity (old s i)) (p.frame (old s i)) a bias
        (width / stripRowLength Mrel (z 1)) zz.1}
    have hpre : tnorm t₀ q₀ ⁻¹' X ∩ source ⊆ Y := by
      rintro p ⟨hpX, hpS⟩
      change p.1 ∈ st.B s i ∧ (p.2 - t₀) / q₀ ∈ IS (st.T s) (st.j s i) ∧
        |Φ.eb p.1 4 - z 0 - z 1 * Φ.eb p.1 3| ≤ width at hpX
      exact ⟨hpS.1, by simpa only [hA] using hBsub hpX.1,
        (hI p.2).mpr hpX.2.1, hstripOld p.1 hpX.2.2⟩
    have hreturned := dominated_muE_floor_return_mono (ν (p.world parent))
      (p.assigned parent) (p.assigned (old s i)) (hp.assigned_measurable _) hAsub
      hAprior.ne' (measure_ne_top _ _) t₀ q₀ hq₀pos source X Y hXm hpre st.ρ (ENNReal.ofReal J)
      (ENNReal.ofReal (st.N ^ (-ε') / (2 : ℝ) ^ st.T s))
      (ENNReal.ofReal_ne_zero_iff.mpr hJ0) ENNReal.ofReal_ne_top hρE hXfloor
    have hExpStrip : -ρ * (unit * v) * L - ε = -(A + ε) := by dsimp only [A]; ring
    have hcoef : ENNReal.ofReal (Nk ^ (-ρ * (unit * v) * L - ε) /
        (2 : ℝ) ^ p.T (p.lev (old s i))) ≤ ENNReal.ofReal q₀ *
        ((ENNReal.ofReal J)⁻¹ * ENNReal.ofReal (st.N ^ (-ε') / (2 : ℝ) ^ st.T s)) := by
      simpa only [zero_mul, neg_zero, zero_sub, hExpStrip] using hmassStrip
    have hYfloor : ENNReal.ofReal (Nk ^ (-ρ * (unit * v) * L - ε) /
        (2 : ℝ) ^ p.T (p.lev (old s i))) * ν (p.world (old s i)) (p.assigned (old s i)) ≤
        (ν (p.world (old s i))).prod volume Y := by
      rw [hworld]
      exact (mul_le_mul' hcoef le_rfl).trans hreturned
    apply hno
    apply original_candidate_of_narrow_strip hp hNk0 (sourceOutputExponent n M) d₁ ρ gain ε H
      (old s i) (unit * v) hgainbounds.1 hgainbounds.2.1 hgainbounds.2.2 hApriorOld hbias
      Y _ hYfloor a ha bias (width / stripRowLength Mrel (z 1)) _ hwidth
    · intro p hp
      exact ⟨by simpa only [hworld] using hp.1, hp.2.1, hp.2.2.1⟩
    · intro p hp
      exact hp.2.2.2

end

end Submission.Obl.k4_finite_affine_candidate_return
