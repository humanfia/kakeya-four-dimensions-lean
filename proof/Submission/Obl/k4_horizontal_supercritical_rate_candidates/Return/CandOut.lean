import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.ScalarApply
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Candidate
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CoreStatement

/-!
# The candidate from Scalar's output

`X3 - L_anc - a₀ P((t - t_Q)/q_c, (x1 - Z_Q)/q_c)` fits every kept line of one output piece at
accuracy `N^εS a₁` on the whole block, with hidden derivative one.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The candidate's value along a line. -/
theorem eval_cand_traj (D : CoreData α) (hN0 : 0 < D.N) (Q : Fin D.fc.n)
    (P : MvPolynomial (Fin 2) ℝ) (l : α) (t : ℝ) :
    eval (trajV D.b l t) (candPoly (D.Lanc Q) D.a₀ (D.tQ Q) D.fc.q (D.ZQ Q) P) =
      D.a₀ * (blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) (l, t) -
        eval ![tau (D.tQ Q) D.fc.q t, D.ny0 Q l + tau (D.tQ Q) D.fc.q t * D.ny1 Q l] P) := by
  have hq : D.fc.q ≠ 0 := by unfold Fam.q; positivity
  have ha0 : D.a₀ ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [eval_candPoly, D.blockVal_eq Q (l, t) hq]
  have hy := D.blockY_eq Q (l, t) hq
  simp only at hy
  rw [hy]
  simp only [trajV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  unfold tau x1 x2 x3
  field_simp

/-- Coefficients of a Scalar output polynomial. -/
theorem output_coeffL1 {C₀ εS β N : ℝ} (hC₀ : StripBound C₀) (hC₀pos : 0 < C₀) (hN : 1 ≤ N)
    (hεS : 0 ≤ εS) (hβ : N ^ (-εS) ≤ β) {P : MvPolynomial (Fin 2) ℝ} (hP : P.totalDegree ≤ 2)
    {u v : ℝ} (huv : |u| + |v| ≤ N ^ εS)
    (hev : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1, |eval ![τ, u + τ * v + β * w] P| ≤ N ^ εS) :
    Submission.Lib.K4ChartLifting.coeffL1 P ≤ 9 * (C₀ * N ^ εS * (N ^ εS) ^ 2 * (N ^ εS) ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hE : 1 ≤ N ^ εS := Real.one_le_rpow hN hεS
  have hβ0 : 0 < β := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hβ
  set β' := min β 1 with hβ'
  have hβ'0 : 0 < β' := lt_min hβ0 one_pos
  have hβ'1 : β' ≤ 1 := min_le_right _ _
  have hβ'2 : N ^ (-εS) ≤ β' := le_min hβ (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith))
  have hstrip : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![τ, u + τ * v + β' * w] P| ≤ N ^ εS := by
    intro τ hτ w hw
    have hw' : β' * w / β ∈ Icc (-1 : ℝ) 1 := by
      have hle : β' ≤ β := min_le_left _ _
      constructor
      · rw [le_div_iff₀ hβ0]; nlinarith [hw.1, hw.2]
      · rw [div_le_iff₀ hβ0]; nlinarith [hw.1, hw.2]
    have := hev τ hτ _ hw'
    rwa [mul_div_cancel₀ _ hβ0.ne'] at this
  have hcoef := hC₀ P hP u v β' (N ^ εS) (N ^ εS) hβ'0 hβ'1 hE
    (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv)
    (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv) (by linarith) hstrip
  have hinv : 1 / β' ^ 2 ≤ (N ^ εS) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ N ^ εS * β' := by
      calc (1 : ℝ) = N ^ εS * N ^ (-εS) := by
            rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
        _ ≤ N ^ εS * β' := mul_le_mul_of_nonneg_left hβ'2 (by linarith)
    nlinarith
  have hm : ∀ m, |P.coeff m| ≤ C₀ * N ^ εS * (N ^ εS) ^ 2 * (N ^ εS) ^ 2 := by
    intro m
    refine (hcoef m).trans ?_
    have hX : 0 ≤ C₀ * N ^ εS * (N ^ εS) ^ 2 := by positivity
    calc C₀ * N ^ εS * (N ^ εS) ^ 2 / β' ^ 2 = C₀ * N ^ εS * (N ^ εS) ^ 2 * (1 / β' ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hX
  have hcard : (P.support.card : ℝ) ≤ 9 := by
    have := Submission.Lib.K4ChartLifting.card_support_le (D := 2) P hP
    exact_mod_cast this
  unfold Submission.Lib.K4ChartLifting.coeffL1
  calc ∑ m ∈ P.support, |P.coeff m| ≤ ∑ _m ∈ P.support, C₀ * N ^ εS * (N ^ εS) ^ 2 * (N ^ εS) ^ 2 :=
        Finset.sum_le_sum (fun m _ => hm m)
    _ = (P.support.card : ℝ) * (C₀ * N ^ εS * (N ^ εS) ^ 2 * (N ^ εS) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- The single-sample supercritical return, under explicit numerical conditions. -/
theorem core_sample (D : CoreData α) (H : CoreHyp D)
    {s m Csc U εS ηS N₀S K₁ C₀ ε Rout : ℝ} (hSA : ScalarAt D.d s m Csc D.S U εS ηS N₀S)
    (hNS : N₀S ≤ D.N) (hC₀ : StripBound C₀) (hC₀pos : 0 < C₀) (hK₁ : 1 ≤ K₁)
    (hok : CrossOK D D.M D.Dw K₁ (D.Bnat C₀))
    (hs : 0 < s) (hU : 0 < U) (hUR : U ≤ D.Rcap) (hS0 : 0 < D.S) (hRpos : 0 < D.Rcap)
    (hεS : 0 ≤ εS) (hε : 0 ≤ ε)
    -- the prunings
    (hχq : D.N ^ (-D.M) ≤ D.f₀.q * D.N ^ (-D.κ * D.s₀))
    (hDwq : D.Dw ≤ D.K * D.f₀.q * D.N ^ (-D.κ * D.s₀)) (hg1 : D.N ^ (-D.κ * D.s₀) ≤ 1)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hχ1 : D.N ^ (-D.M) ≤ 1)
    (hh3χ : D.N ^ (-m) * D.fc.q ≤ D.N ^ (-D.M)) (hh3D : D.N ^ (-m) * D.fc.q ≤ D.Dw)
    (hb3D : D.cellδ2 (D.N ^ (-m)) ≤ D.Dw) (hh31 : D.N ^ (-m) * D.fc.q ≤ 1)
    (hb3pos : 0 < D.cellδ2 (D.N ^ (-m))) (hW3pos : 0 < D.W3 K₁ C₀ (D.N ^ (-m)))
    (hqe1 : D.fe.q / D.fc.q ≤ D.N ^ (-m)) (hqe2 : 3 * D.K * D.fe.q / D.fc.q ≤ D.N ^ (-m))
    (hds : D.deepSpread ≤ D.N ^ (-s))
    (hloss : (810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) + 27) / K₁ ≤
      D.N ^ (-D.εL) / 2)
    -- Scalar
    (hKη : 2 * D.K ≤ D.N ^ ηS)
    (hc1 : D.N ^ (-Csc) ≤ (D.a₀ / D.ac) ^ D.d) (hc2 : (D.a₀ / D.ac) ^ D.d ≤ D.N ^ Csc)
    (hmassη : D.N ^ (-ηS) ≤ D.N ^ (-D.εL) / 2)
    (hr31 : D.Rcap⁻¹ ≤ D.r3 (D.N ^ (-m))) (hr32 : D.r3 (D.N ^ (-m)) ≤ D.Rcap)
    (hΛ : 6 * D.Λa * (D.N ^ (-m) * D.fc.q) ≤ D.a₀ * D.N ^ (-s))
    (h2a0 : 2 * D.a₀ ≤ 1) (h2a0s : -Real.logb D.N (2 * (D.a₀ * D.N ^ (-s))) ≤ D.Rcap)
    (hcapnum : D.capLHS (D.N ^ (-m)) ≤ D.capRHS (D.N ^ (-m)) ηS)
    (hW1 : D.W3 K₁ C₀ (D.N ^ (-m)) ≤ 1) (hWs : -Real.logb D.N (D.W3 K₁ C₀ (D.N ^ (-m))) ≤ D.Rcap)
    (hδH : D.cellδ2 (D.N ^ (-m)) ≤ D.Dw)
    (hsuppnum : (2 * ((⌊(2 * D.K + 1) / D.N ^ (-m)⌋₊ : ℝ) + 1) + 1) ^ 2 *
        (D.K * K₁ * (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 (D.N ^ (-m))) (D.cellδ2 (D.N ^ (-m)))
          (D.W3 K₁ C₀ (D.N ^ (-m))) (D.N ^ (-m)) (D.N ^ (-s)) : ℝ)) * (D.N ^ (-m)) ^ 2 ≤
      D.N ^ ηS * ((D.a₀ / D.ac) ^ D.d)⁻¹ * (D.N ^ (-s)) ^ (-D.d))
    -- the candidate
    (hfinal : D.N ^ (-D.d * D.vc - ε) ≤ (D.a₀ / D.ac) ^ D.d * (D.N ^ (-s)) ^ D.d * D.N ^ (-εS) /
      D.N ^ εS)
    (hfit : D.a₀ * (D.N ^ εS * D.N ^ (-s)) ≤ D.N ^ ε * D.N ^ (-(D.s₁ - D.vc) - D.vc))
    (hcoef : 1 + (6 * D.K + 3 * D.K * D.Λa + 3 * D.Λa) + D.a₀ *
      (9 * (C₀ * D.N ^ εS * (D.N ^ εS) ^ 2 * (D.N ^ εS) ^ 2) *
        (1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K)) ^ 2) ≤ D.N ^ Rout) :
    ∃ (i : Fin D.fc.n) (Qp : MvPolynomial (Fin 4) ℝ), Qp.totalDegree ≤ 2 ∧
      (∀ e, |Qp.coeff e| ≤ D.N ^ Rout) ∧
      ENNReal.ofReal (D.N ^ (-D.d * D.vc - ε) * D.fc.q) * D.ν (D.fc.A i) ≤
        D.ρ {p | p.1 ∈ D.fc.B i ∧ p.2 ∈ D.fc.I i ∧
          candFit D.b (D.N ^ ε) (D.N ^ (-(D.s₁ - D.vc) - D.vc)) Qp p.1 (D.fc.I i) ∧
          D.N ^ (-ε) ≤ |MvPolynomial.eval (trajV D.b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Qp)|} := by
  classical
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hσ : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hat : 0 < D.N ^ (-s) := Real.rpow_pos_of_pos hN0 _
  -- mass and a dense label
  have hmass := S4_mass D H hK₁ hok hσ hat hχq hDwq hg1 hχD hχ1 hh3χ hh3D hb3D hh31 hb3pos hW3pos
    hqe1 hqe2 hds hloss
  obtain ⟨Q, hQ⟩ := exists_dense_label D H hmass
  -- Scalar
  obtain ⟨n, β, A', u, v, P, hβ1, hβ2, hA'm, hA'd, hpieces, htot⟩ := scalar_apply D H hSA hNS hK₁ hok
    hs hU hUR hS0 hRpos hKη hc1 hc2 hmassη hr31 hr32 hΛ h2a0 h2a0s hcapnum hW1 hWs hh3χ hδH hb3pos
    hW3pos hsuppnum hQ
  set S4 := D.S4 K₁ C₀ (D.N ^ (-m)) (D.N ^ (-s)) with hS4
  set Blk := D.fc.B Q ×ˢ D.fc.I Q with hBlk
  have hS4m : MeasurableSet S4 := measurableSet_S4 D H _ _ _ _
  have hI : MeasurableSet (D.fc.I Q) := by unfold Fam.I blk; exact measurableSet_Icc
  have hBlkm : MeasurableSet Blk := (H.fcgood.measB Q).prod hI
  -- a piece exists
  have hνA : D.ν (D.fc.A Q) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (H.fcgood.floorA Q))
    rw [ENNReal.ofReal_pos]
    have : 0 < (D.N ^ (-D.sc)) ^ D.d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
    have : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
    have : 0 < D.K := by linarith [H.K1]
    positivity
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (D.N ^ (-εS)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
    refine ENNReal.mul_pos ?_ (ENNReal.mul_pos ?_ hνA).ne'
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hN0 _)).ne'
    · exact (ENNReal.ofReal_pos.mpr hqc).ne'
  have hn : Nonempty (Fin n) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : {p : α × ℝ | ∃ i, p.1 ∈ A' i} = ∅ := by
      ext p; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨i, -⟩; exact IsEmpty.false i
    rw [this, measure_empty] at htot
    exact absurd htot (not_le.mpr hpos)
  obtain ⟨i₀⟩ := hn
  obtain ⟨huv, hdeg, hev, hfitP, hmassP⟩ := hpieces i₀
  -- a witness point for the ancestor bounds
  have hwit : ∃ p, p ∈ S4 ∩ Blk := by
    by_contra hne
    push Not at hne
    have : (D.ρs.restrict (S4 ∩ Blk)) = 0 := by
      rw [Measure.restrict_eq_zero]
      rw [Set.eq_empty_iff_forall_notMem.mpr hne, measure_empty]
    have h0 : (D.ρs.restrict (S4 ∩ Blk)) {p | ∃ i, p.1 ∈ A' i} = 0 := by rw [this]; rfl
    rw [h0] at htot
    exact absurd htot (not_le.mpr hpos)
  obtain ⟨p₀, hp₀S, hp₀B⟩ := hwit
  have hp₀0 : p₀ ∈ D.G0 := S4_subset_G0 D _ _ _ _ hp₀S
  -- the candidate
  set Qp := candPoly (D.Lanc Q) D.a₀ (D.tQ Q) D.fc.q (D.ZQ Q) (P i₀) with hQp
  refine ⟨Q, Qp, candPoly_totalDegree _ _ _ _ _ _ hdeg, ?_, ?_⟩
  · -- coefficients
    intro e
    refine (coeff_candPoly_le _ _ _ _ _ _ hdeg e).trans (le_trans ?_ hcoef)
    obtain ⟨c1, c2, c3⟩ := Lanc_coeff D H hp₀0 hp₀B
    have c0 := Lanc0_bound D H hok.s₀0 hp₀0 hp₀B
    have hL1 := output_coeffL1 hC₀ hC₀pos hN.le hεS hβ1 hdeg huv hev
    have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
    have hqinv : |D.fc.q⁻¹| ≤ D.K * D.N ^ (D.κ * D.sc) := by
      have hT := H.fcgood.Thi
      unfold Fam.q
      rw [inv_inv, abs_of_pos (by positivity)]
      exact hT
    have htQ : |D.tQ Q| ≤ 1 := by
      unfold CoreData.tQ
      have hj := (D.fc.j Q).isLt
      have hpos : (0 : ℝ) < 2 ^ D.fc.T := by positivity
      rw [abs_of_nonneg (by positivity), div_le_one hpos]
      have : ((D.fc.j Q : ℕ) : ℝ) < ((2 ^ D.fc.T : ℕ) : ℝ) := by exact_mod_cast hj
      push_cast at this; linarith
    have hZQ : |D.ZQ Q| ≤ 2 * D.K := by
      unfold CoreData.ZQ
      have := H.fcgood.cbd Q 0; have := H.fcgood.cbd Q 1
      calc |D.fc.c Q 0 + D.tQ Q * D.fc.c Q 1| ≤ |D.fc.c Q 0| + |D.tQ Q| * |D.fc.c Q 1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ D.K + 1 * D.K := by gcongr
        _ = 2 * D.K := by ring
    have hΛ0 : 0 ≤ D.Λa := (abs_nonneg _).trans c1
    have hsum : |D.Lanc Q 0| + |D.Lanc Q 1| + |D.Lanc Q 2| + |D.Lanc Q 3| ≤
        6 * D.K + 3 * D.K * D.Λa + 3 * D.Λa := by
      unfold CoreData.Λa at c0 ⊢; linarith
    have hfac : 1 + |D.fc.q⁻¹| * (1 + |D.tQ Q| + |D.ZQ Q|) ≤
        1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K) := by
      gcongr
    have hL10 : 0 ≤ Submission.Lib.K4ChartLifting.coeffL1 (P i₀) :=
      Submission.Lib.K4ChartLifting.coeffL1_nonneg _
    rw [abs_of_pos ha0]
    gcongr
  · -- mass
    calc ENNReal.ofReal (D.N ^ (-D.d * D.vc - ε) * D.fc.q) * D.ν (D.fc.A Q)
        = ENNReal.ofReal (D.N ^ (-D.d * D.vc - ε)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hN0.le _), mul_assoc]
      _ ≤ ENNReal.ofReal ((D.a₀ / D.ac) ^ D.d * (D.N ^ (-s)) ^ D.d * β / D.N ^ εS) *
            (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
          gcongr
          refine hfinal.trans ?_
          have hac : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
          have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
          have hX : 0 ≤ (D.a₀ / D.ac) ^ D.d * (D.N ^ (-s)) ^ D.d := by positivity
          gcongr
      _ ≤ (D.ρs.restrict (S4 ∩ Blk)) (A' i₀ ×ˢ univ) := hmassP
      _ ≤ D.ρs ((A' i₀ ×ˢ univ) ∩ (S4 ∩ Blk)) := by
          rw [Measure.restrict_apply' (hS4m.inter hBlkm)]
      _ ≤ D.ρ ((A' i₀ ×ˢ univ) ∩ (S4 ∩ Blk)) := H.ρsρ _
      _ ≤ _ := by
          refine measure_mono (fun p hp => ?_)
          obtain ⟨⟨hpA, -⟩, hpS, hpB, hpI⟩ := hp
          have hp0 : p ∈ D.G0 := S4_subset_G0 D _ _ _ _ hpS
          have hgood := good_line D H hp0 ⟨hpB, hpI⟩
          refine ⟨hpB, hpI, ?_, ?_⟩
          · intro t ht
            have hτ : tau (D.tQ Q) D.fc.q t ∈ Icc (0 : ℝ) 1 := by
              rw [I_eq_Icc] at ht
              unfold tau
              constructor
              · exact div_nonneg (by linarith [ht.1]) hqc.le
              · rw [div_le_one hqc]; linarith [ht.2]
            have hf := (hfitP p.1 hpA hgood _ hτ).2
            refine ⟨?_, ?_, ?_⟩
            · have ha0' : (0 : ℝ) < D.a₀ := Real.rpow_pos_of_pos hN0 _
              rw [eval_cand_traj D hN0, abs_mul, abs_of_pos ha0']
              refine le_trans ?_ hfit
              unfold blockVal
              exact mul_le_mul_of_nonneg_left hf ha0'.le
            · rw [hQp, pderiv_candPoly, map_one, abs_one]
              exact Real.one_le_rpow hN.le hε
            · rw [hQp, pderiv_candPoly]
              simp only [map_one, Derivation.map_one_eq_zero, map_zero, abs_zero]
              positivity
          · rw [hQp, pderiv_candPoly, map_one, abs_one]
            exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
