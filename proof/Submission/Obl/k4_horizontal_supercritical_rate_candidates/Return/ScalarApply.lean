import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.GoodLine

/-!
# Scalar on the dense candidate label

All hypotheses of `scalar_on_block` hold for the kept incidences of a dense candidate label,
under explicit numerical conditions on the scales.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The cap numerics, with room for a palette factor and a small angular exponent. -/
def CoreData.capLHS (D : CoreData α) (σ : ℝ) : ℝ :=
  36 * (2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (σ * D.fc.q)) / (σ * D.fc.q) + 5) *
    (2 * (D.K * (σ * D.fc.q) ^ 3 * (2 * D.a₀ ^ D.d))) * (D.K * D.N ^ (D.S / D.Rcap))

def CoreData.capRHS (D : CoreData α) (σ ηS : ℝ) : ℝ :=
  D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d *
    (D.fc.q * ((D.N ^ (-D.sc)) ^ D.d * D.fc.q ^ 2 * D.N ^ (-D.κ * D.sc) / D.K))

/-- A cap bound with the label's reference weight. -/
theorem cap_to_scalar (D : CoreData α) (H : CoreHyp D) {σ ηS w : ℝ} (hσ : 0 < σ) (hw : 0 < w)
    (hd1 : D.d ≤ 1) (hd0 : 0 ≤ D.d) (Q : Fin D.fc.n) (extra : ℝ) (hextra : 0 ≤ extra)
    (hex : extra ≤ D.K * D.N ^ (D.S / D.Rcap))
    (hnum : D.capLHS σ ≤ D.capRHS σ ηS) :
    ∀ z : Fin 2 → ℤ, ((D.cellCubes σ Q z).card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) *
          ENNReal.ofReal extra ≤
        ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * w ^ D.d) *
          (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
  intro z
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hK0 : 0 < D.K := by linarith [H.K1]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hac : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
  have hh : 0 < σ * D.fc.q := mul_pos hσ hqc
  have hcard := card_cellCubes D H hσ Q z
  have hfloor := H.fcgood.floorA Q
  have hpow : (2 * (D.a₀ * w)) ^ D.d ≤ 2 * D.a₀ ^ D.d * w ^ D.d := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow ha0.le hw.le]
    have : (2 : ℝ) ^ D.d ≤ 2 := by
      calc (2 : ℝ) ^ D.d ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1
        _ = 2 := Real.rpow_one 2
    have hpos : 0 ≤ D.a₀ ^ D.d * w ^ D.d := by positivity
    nlinarith
  set cb := 36 * (2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (σ * D.fc.q)) /
    (σ * D.fc.q) + 5) with hcb
  have hcb0 : 0 ≤ cb := by rw [hcb]; positivity
  have hreal : ((D.cellCubes σ Q z).card : ℝ) *
      (2 * (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) * extra ≤
      D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * w ^ D.d *
        (D.fc.q * ((D.N ^ (-D.sc)) ^ D.d * D.fc.q ^ 2 * D.N ^ (-D.κ * D.sc) / D.K)) := by
    have hw0 : 0 < w ^ D.d := Real.rpow_pos_of_pos hw _
    calc ((D.cellCubes σ Q z).card : ℝ) *
          (2 * (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) * extra
        ≤ cb * (2 * (D.K * ((σ * D.fc.q) ^ 3 * (2 * D.a₀ ^ D.d * w ^ D.d)))) *
            (D.K * D.N ^ (D.S / D.Rcap)) := by
          gcongr
      _ = D.capLHS σ * w ^ D.d := by unfold CoreData.capLHS; rw [← hcb]; ring
      _ ≤ D.capRHS σ ηS * w ^ D.d := mul_le_mul_of_nonneg_right hnum hw0.le
      _ = _ := by unfold CoreData.capRHS; ring
  have hν : ENNReal.ofReal ((D.N ^ (-D.sc)) ^ D.d * D.fc.q ^ 2 * D.N ^ (-D.κ * D.sc) / D.K) ≤
      D.ν (D.fc.A Q) := hfloor
  calc ((D.cellCubes σ Q z).card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) *
          ENNReal.ofReal extra
      = ENNReal.ofReal (((D.cellCubes σ Q z).card : ℝ) *
          (2 * (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d))) * extra) := by
        rw [eq_comm, ENNReal.ofReal_mul (p := ((D.cellCubes σ Q z).card : ℝ) *
          (2 * (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * w)) ^ D.d)))) (by positivity),
          ENNReal.ofReal_mul (p := ((D.cellCubes σ Q z).card : ℝ)) (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * w ^ D.d *
          (D.fc.q * ((D.N ^ (-D.sc)) ^ D.d * D.fc.q ^ 2 * D.N ^ (-D.κ * D.sc) / D.K))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * w ^ D.d) *
          (ENNReal.ofReal D.fc.q *
            ENNReal.ofReal ((D.N ^ (-D.sc)) ^ D.d * D.fc.q ^ 2 * D.N ^ (-D.κ * D.sc) / D.K)) := by
        rw [ENNReal.ofReal_mul (p := D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * w ^ D.d)
          (by positivity), ENNReal.ofReal_mul (p := D.fc.q) hqc.le]
    _ ≤ _ := by gcongr

/-- Scalar's conclusion on the kept incidences of a dense candidate label. -/
theorem scalar_apply (D : CoreData α) (H : CoreHyp D)
    {s m Csc U εS ηS N₀S K₁ C₀ : ℝ} (hSA : ScalarAt D.d s m Csc D.S U εS ηS N₀S)
    (hNS : N₀S ≤ D.N) (hK₁ : 1 ≤ K₁) (hok : CrossOK D D.M D.Dw K₁ (D.Bnat C₀))
    (hs : 0 < s) (hU : 0 < U) (hUR : U ≤ D.Rcap) (hS0 : 0 < D.S) (hRpos : 0 < D.Rcap)
    (hKη : 2 * D.K ≤ D.N ^ ηS)
    (hc1 : D.N ^ (-Csc) ≤ (D.a₀ / D.ac) ^ D.d) (hc2 : (D.a₀ / D.ac) ^ D.d ≤ D.N ^ Csc)
    (hmassη : D.N ^ (-ηS) ≤ D.N ^ (-D.εL) / 2)
    (hr31 : D.Rcap⁻¹ ≤ D.r3 (D.N ^ (-m))) (hr32 : D.r3 (D.N ^ (-m)) ≤ D.Rcap)
    (hΛ : 6 * D.Λa * (D.N ^ (-m) * D.fc.q) ≤ D.a₀ * D.N ^ (-s))
    (h2a0 : 2 * D.a₀ ≤ 1) (h2a0s : -Real.logb D.N (2 * (D.a₀ * D.N ^ (-s))) ≤ D.Rcap)
    (hcapnum : D.capLHS (D.N ^ (-m)) ≤ D.capRHS (D.N ^ (-m)) ηS)
    (hW1 : D.W3 K₁ C₀ (D.N ^ (-m)) ≤ 1) (hWs : -Real.logb D.N (D.W3 K₁ C₀ (D.N ^ (-m))) ≤ D.Rcap)
    (hσr : D.N ^ (-m) * D.fc.q ≤ D.N ^ (-D.M)) (hδH : D.cellδ2 (D.N ^ (-m)) ≤ D.Dw)
    (hb3pos : 0 < D.cellδ2 (D.N ^ (-m))) (hW3pos : 0 < D.W3 K₁ C₀ (D.N ^ (-m)))
    (hsuppnum : (2 * ((⌊(2 * D.K + 1) / D.N ^ (-m)⌋₊ : ℝ) + 1) + 1) ^ 2 *
        (D.K * K₁ * (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 (D.N ^ (-m))) (D.cellδ2 (D.N ^ (-m)))
          (D.W3 K₁ C₀ (D.N ^ (-m))) (D.N ^ (-m)) (D.N ^ (-s)) : ℝ)) * (D.N ^ (-m)) ^ 2 ≤
      D.N ^ ηS * ((D.a₀ / D.ac) ^ D.d)⁻¹ * (D.N ^ (-s)) ^ (-D.d))
    {Q : Fin D.fc.n}
    (hQ : ENNReal.ofReal (D.N ^ (-D.εL) / 2) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) ≤
      D.ρs (D.S4 K₁ C₀ (D.N ^ (-m)) (D.N ^ (-s)) ∩ (D.fc.B Q ×ˢ D.fc.I Q))) :
    ∃ (n : ℕ) (β : ℝ) (A' : Fin n → Set α) (u v : Fin n → ℝ)
      (P : Fin n → MvPolynomial (Fin 2) ℝ),
      D.N ^ (-εS) ≤ β ∧ β ≤ D.N ^ εS ∧ (∀ i, MeasurableSet (A' i)) ∧
      (∀ i j, i ≠ j → Disjoint (A' i) (A' j)) ∧
      (∀ i, |u i| + |v i| ≤ D.N ^ εS ∧ (P i).totalDegree ≤ 2 ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
          |MvPolynomial.eval ![τ, u i + τ * v i + β * w] (P i)| ≤ D.N ^ εS) ∧
        (∀ l ∈ A' i, l ∈ D.goodLines Q → ∀ τ ∈ Icc (0 : ℝ) 1,
          |D.ny0 Q l + τ * D.ny1 Q l - u i - τ * v i| ≤ D.N ^ εS * β ∧
          |D.nx0 Q l + τ * D.nx1 Q l - MvPolynomial.eval ![τ, D.ny0 Q l + τ * D.ny1 Q l] (P i)| ≤
            D.N ^ εS * D.N ^ (-s)) ∧
        ENNReal.ofReal ((D.a₀ / D.ac) ^ D.d * (D.N ^ (-s)) ^ D.d * β / D.N ^ εS) *
            (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) ≤
          (D.ρs.restrict (D.S4 K₁ C₀ (D.N ^ (-m)) (D.N ^ (-s)) ∩ (D.fc.B Q ×ˢ D.fc.I Q)))
            (A' i ×ˢ univ)) ∧
      ENNReal.ofReal (D.N ^ (-εS)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) ≤
        (D.ρs.restrict (D.S4 K₁ C₀ (D.N ^ (-m)) (D.N ^ (-s)) ∩ (D.fc.B Q ×ˢ D.fc.I Q)))
          {p | ∃ i, p.1 ∈ A' i} := by
  classical
  haveI := H.νprob
  have hN : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hK₁0 : 0 < K₁ := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hac : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
  set σ := D.N ^ (-m) with hσdef
  have hσ : 0 < σ := Real.rpow_pos_of_pos hN0 _
  set at' := D.N ^ (-s) with hatdef
  have hat : 0 < at' := Real.rpow_pos_of_pos hN0 _
  set S4 := D.S4 K₁ C₀ σ at' with hS4
  set Blk := D.fc.B Q ×ˢ D.fc.I Q with hBlk
  have hS4m : MeasurableSet S4 := measurableSet_S4 D H _ _ _ _
  have hI : MeasurableSet (D.fc.I Q) := by unfold Fam.I blk; exact measurableSet_Icc
  have hBlkm : MeasurableSet Blk := (H.fcgood.measB Q).prod hI
  set mm := D.ρs.restrict (S4 ∩ Blk) with hmm
  have hmmS : ∀ E, mm E ≤ D.ρs (E ∩ (S4 ∩ Blk)) := fun E => by
    rw [hmm, Measure.restrict_apply' (hS4m.inter hBlkm)]
  have hfloor := H.fcgood.floorA Q
  have hνA : D.ν (D.fc.A Q) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ hfloor)
    rw [ENNReal.ofReal_pos]
    have : 0 < (D.N ^ (-D.sc)) ^ D.d := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN0 _) _
    have : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
    have : 0 < D.K := by linarith [H.K1]
    positivity
  have hd0 := hok.d0
  have hd1 : D.d ≤ 1 := hok.d1.le
  have hr3eq : D.N ^ (-D.r3 σ) = σ * D.fc.q := N_r3 D H hσ
  have hS4G0 : S4 ⊆ D.G0 := S4_subset_G0 D _ _ _ _
  have hS3G0 : D.S3 K₁ C₀ σ ⊆ D.G0 := S3_subset_G0 D _ _ _
  -- the window exponent of a value bin of width `w ≥ at'`
  have hwin : ∀ w : ℝ, at' ≤ w → w ≤ 1 →
      D.N ^ (-(-Real.logb D.N (2 * (D.a₀ * w)))) = 2 * (D.a₀ * w) ∧
      0 ≤ -Real.logb D.N (2 * (D.a₀ * w)) ∧ -Real.logb D.N (2 * (D.a₀ * w)) ≤ D.Rcap := by
    intro w hw1 hw2
    have hw0 : 0 < w := hat.trans_le hw1
    have hpos : 0 < 2 * (D.a₀ * w) := by positivity
    refine ⟨by rw [neg_neg, Real.rpow_logb hN0 hN.ne' hpos], ?_, ?_⟩
    · rw [neg_nonneg]
      apply Real.logb_nonpos hN hpos.le
      nlinarith
    · refine le_trans ?_ h2a0s
      have : Real.logb D.N (2 * (D.a₀ * at')) ≤ Real.logb D.N (2 * (D.a₀ * w)) :=
        Real.logb_le_logb_of_le hN (by positivity) (by nlinarith)
      linarith
  have hΛw : ∀ w : ℝ, at' ≤ w → 6 * D.Λa * (σ * D.fc.q) ≤ D.a₀ * w := fun w hw =>
    hΛ.trans (mul_le_mul_of_nonneg_left hw ha0.le)
  have hNSR : 1 ≤ D.N ^ (D.S / D.Rcap) := Real.one_le_rpow hN.le (div_nonneg hS0.le hRpos.le)
  have hKR : (1 : ℝ) ≤ D.K * D.N ^ (D.S / D.Rcap) := one_le_mul_of_one_le_of_one_le H.K1 hNSR
  -- Scalar
  refine scalar_on_block hSA hNS hN.le D.ν mm (D.fc.A Q) (D.goodLines Q) (H.fcgood.measA Q)
    (measurableSet_goodLines D H Q) (D.tQ Q) D.fc.q D.K ((D.a₀ / D.ac) ^ D.d) hqc hK0
    (by linarith) (D.ny0 Q) (D.ny1 Q) (D.nx0 Q) (D.nx1 Q) (D.measurable_ny0 H.bmeas)
    (D.measurable_ny1 H.bmeas) (D.measurable_nx0 H.bmeas) (D.measurable_nx1 H.bmeas) hνA
    ?_ ?_ ?_ ?_ hc1 hc2 ?_ ?_ ?_ ?_
  · -- domination
    exact (Measure.restrict_le_self).trans ((H.ρsρ.trans H.ρμ).trans H.μdom)
  · -- support
    refine le_antisymm ((hmmS _).trans (le_of_eq ?_)) zero_le
    have hempty : (D.fc.A Q ×ˢ Icc (D.tQ Q) (D.tQ Q + D.fc.q))ᶜ ∩ (S4 ∩ Blk) = ∅ := by
      refine Set.subset_empty_iff.mp (fun p hp => ?_)
      obtain ⟨hpc, -, hpB, hpI⟩ := hp
      refine hpc ⟨H.fcgood.BA Q hpB, ?_⟩
      rw [I_eq_Icc] at hpI; exact hpI
    rw [hempty, measure_empty]
  · -- good lines
    rw [hmm, ae_restrict_iff' (hS4m.inter hBlkm)]
    exact Filter.Eventually.of_forall (fun p hp => good_line D H (hS4G0 hp.1) hp.2)
  · -- bounded coefficients
    intro l hl
    exact ⟨hl.1.trans hKη, hl.2.1.trans hKη, hl.2.2.1.trans hKη, hl.2.2.2.trans hKη⟩
  · -- mass
    calc ENNReal.ofReal (D.N ^ (-ηS)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q))
        ≤ ENNReal.ofReal (D.N ^ (-D.εL) / 2) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
          gcongr
      _ ≤ D.ρs (S4 ∩ Blk) := hQ
      _ = mm univ := by rw [hmm, Measure.restrict_apply_univ]
  · -- caps
    intro r cell jj hr0 hrs
    set w := D.N ^ (-r)
    have hw1 : at' ≤ w := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    have hw2 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
    have hw0 : 0 < w := hat.trans_le hw1
    obtain ⟨hσ'e, hσ'0, hσ'1⟩ := hwin w hw1 hw2
    have hsub : {p : α × ℝ | blockCell (D.tQ Q) D.fc.q σ (D.ny0 Q) (D.ny1 Q) p = cell ∧
        ⌊blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) p / w⌋ = jj} ∩ (S4 ∩ Blk) ⊆
        S4 ∩ Blk ∩ {p | D.zc σ Q p = cell ∧ ⌊D.xv Q p / w⌋ = jj} :=
      fun p hp => ⟨hp.2, hp.1⟩
    have hcap := scalar_value_cap D H hσ hw0 (hΛw w hw1) hr3eq hr31 hr32 hσ'e hσ'0 hσ'1
      hS4G0 (Q := Q) cell jj
    have hconv := cap_to_scalar D H hσ hw0 hd1 hd0 Q 1 zero_le_one hKR hcapnum cell
    rw [ENNReal.ofReal_one, mul_one] at hconv
    exact (hmmS _).trans ((measure_mono hsub).trans (hcap.trans hconv))
  · -- support count
    have hW0 : D.cellW0 σ ≤ D.W3 K₁ C₀ σ := by
      unfold CoreData.W3
      have hLip := crossLip_nonneg D H hok
      have hB0 := hok.B0
      have hE : 0 ≤ D.N ^ D.εL := Real.rpow_nonneg hN0.le _
      have ha1 : 0 ≤ D.a₁ := Real.rpow_nonneg hN0.le _
      have hr3 : 0 ≤ D.N ^ (-D.r3 σ) := Real.rpow_nonneg hN0.le _
      have : 0 ≤ 2 * (D.N ^ D.εL * D.a₁) + D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 σ +
          9 * D.Bnat C₀ * (2 * D.N ^ (-D.r3 σ)) * (1 + D.K + D.K ^ 2) := by positivity
      linarith
    obtain ⟨F, hFc, hFm⟩ := support_count D H hok hK₁0 hb3pos hW3pos hW1 hWs hr31 hr32 hσ hat
      (le_of_eq hr3eq.symm) hσr le_rfl hδH hW0 Q
    refine ⟨F, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right hFc (by positivity)).trans hsuppnum
    · rw [hmm, ae_restrict_iff' (hS4m.inter hBlkm)]
      exact Filter.Eventually.of_forall (fun p hp => hFm p hp.1 hp.2.1 hp.2.2)
  · -- angular caps
    intro r cell jj kk hr0 hrU
    have hat1 : at' ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
    obtain ⟨hσ'e, hσ'0, hσ'1⟩ := hwin at' le_rfl hat1
    have hNr : 0 < D.N ^ (-D.S * r) := Real.rpow_pos_of_pos hN0 _
    by_cases hrR : D.Rcap⁻¹ ≤ r
    · have hsub : {p : α × ℝ | blockCell (D.tQ Q) D.fc.q σ (D.ny0 Q) (D.ny1 Q) p = cell ∧
          ⌊blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) p / at'⌋ = jj ∧
          ⌊D.ny1 Q p.1 / D.N ^ (-r)⌋ = kk} ∩ (S4 ∩ Blk) ⊆
          S4 ∩ Blk ∩ {p | D.zc σ Q p = cell ∧ ⌊D.xv Q p / at'⌋ = jj} ∩
            {p | ⌊D.b p.1 3 / D.N ^ (-r)⌋ = kk} :=
        fun p hp => ⟨⟨hp.2, hp.1.1, hp.1.2.1⟩, hp.1.2.2⟩
      have hcap := scalar_angle_cap D H hσ hat (hΛw at' le_rfl) hr3eq hr31 hr32 hσ'e hσ'0 hσ'1
        hrR (hrU.trans hUR) hS4G0 (Q := Q) cell jj kk
      have hpal := H.caps.pal r hrR (hrU.trans hUR) kk
      have hconv := cap_to_scalar D H hσ hat hd1 hd0 Q D.K hK0
        (le_mul_of_one_le_right hK0 hNSR) hcapnum cell
      refine (hmmS _).trans ((measure_mono hsub).trans (hcap.trans ?_))
      calc ((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d)) *
              D.π {u : ℝ | ⌊u / D.N ^ (-r)⌋ = kk})
          ≤ ((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d)) *
              (ENNReal.ofReal D.K * ENNReal.ofReal (D.N ^ (-D.S * r)))) := by
            gcongr
            rw [← ENNReal.ofReal_mul hK0]; exact hpal
        _ = (((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d))) *
              ENNReal.ofReal D.K) * ENNReal.ofReal (D.N ^ (-D.S * r)) := by ring
        _ ≤ (ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d) *
              (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q))) * ENNReal.ofReal (D.N ^ (-D.S * r)) := by
            gcongr
        _ = ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d *
              D.N ^ (-D.S * r)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
            rw [ENNReal.ofReal_mul (p := D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d)
              (by positivity)]
            ring
    · push Not at hrR
      have hsub : {p : α × ℝ | blockCell (D.tQ Q) D.fc.q σ (D.ny0 Q) (D.ny1 Q) p = cell ∧
          ⌊blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) p / at'⌋ = jj ∧
          ⌊D.ny1 Q p.1 / D.N ^ (-r)⌋ = kk} ∩ (S4 ∩ Blk) ⊆
          S4 ∩ Blk ∩ {p | D.zc σ Q p = cell ∧ ⌊D.xv Q p / at'⌋ = jj} :=
        fun p hp => ⟨hp.2, hp.1.1, hp.1.2.1⟩
      have hcap := scalar_value_cap D H hσ hat (hΛw at' le_rfl) hr3eq hr31 hr32 hσ'e hσ'0 hσ'1
        hS4G0 (Q := Q) cell jj
      have hconv := cap_to_scalar D H hσ hat hd1 hd0 Q (D.N ^ (D.S / D.Rcap)) (by positivity)
        (le_mul_of_one_le_left (by positivity) H.K1) hcapnum cell
      have hexp : D.N ^ (D.S / D.Rcap) * D.N ^ (-D.S * r) ≥ 1 := by
        rw [← Real.rpow_add hN0]
        apply Real.one_le_rpow hN.le
        have : D.S * r ≤ D.S * D.Rcap⁻¹ := mul_le_mul_of_nonneg_left hrR.le hS0.le
        rw [div_eq_mul_inv]; linarith
      refine (hmmS _).trans ((measure_mono hsub).trans (hcap.trans ?_))
      calc ((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d)))
          ≤ ((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d))) *
              (ENNReal.ofReal (D.N ^ (D.S / D.Rcap)) * ENNReal.ofReal (D.N ^ (-D.S * r))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact le_mul_of_one_le_right zero_le (by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hexp)
        _ = (((D.cellCubes σ Q cell).card : ℝ≥0∞) *
            (2 * ENNReal.ofReal (D.K * ((σ * D.fc.q) ^ 3 * (2 * (D.a₀ * at')) ^ D.d))) *
              ENNReal.ofReal (D.N ^ (D.S / D.Rcap))) * ENNReal.ofReal (D.N ^ (-D.S * r)) := by ring
        _ ≤ (ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d) *
              (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q))) * ENNReal.ofReal (D.N ^ (-D.S * r)) := by
            gcongr
        _ = ENNReal.ofReal (D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d *
              D.N ^ (-D.S * r)) * (ENNReal.ofReal D.fc.q * D.ν (D.fc.A Q)) := by
            rw [ENNReal.ofReal_mul (p := D.N ^ ηS * σ ^ 2 * (D.a₀ / D.ac) ^ D.d * at' ^ D.d)
              (by positivity)]
            ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
