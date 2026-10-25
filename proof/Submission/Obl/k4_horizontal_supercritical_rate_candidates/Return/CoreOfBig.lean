import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CoreAssembly

/-!
# One sample, from the exponent relations and the large-`N` inequalities

All numerical hypotheses of `core_sample` hold at one sample with `K ≤ N^η`, `0 < εL ≤ η`,
crossing cells of side `χ`, Scalar mesh `N^(-(M+4s₀))`, terminal width `N^(-(s₁-s₀))` and
`K₁ = N^η₁`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem core_of_big (D : CoreData α) (H : CoreHyp D) {εS ηS N₀S C₀ η η₁ ε Rout : ℝ}
    (hSA : ScalarAt D.d (D.s₁ - D.s₀) (D.M + 4 * D.s₀) (D.s₁ + 1) D.S (D.s₁ - D.s₀) εS ηS N₀S)
    (hNS : N₀S ≤ D.N) (hC₀ : StripBound C₀) (hC₀pos : 0 < C₀)
    (hE : ExpOK D.d D.κ D.S D.s₀ D.s₁ D.vc D.M ε Rout η η₁ ηS εS D.Rcap)
    (hB : BigN D.N D.d D.κ D.S D.s₀ D.s₁ D.vc D.M Rout η η₁ ηS εS D.Rcap C₀)
    (hKη : D.K ≤ D.N ^ η) (hεL0 : 0 < D.εL) (hεLη : D.εL ≤ η) :
    ∃ (i : Fin D.fc.n) (Qp : MvPolynomial (Fin 4) ℝ), Qp.totalDegree ≤ 2 ∧
      (∀ e, |Qp.coeff e| ≤ D.N ^ Rout) ∧
      ENNReal.ofReal (D.N ^ (-D.d * D.vc - ε) * D.fc.q) * D.ν (D.fc.A i) ≤
        D.ρ {p | p.1 ∈ D.fc.B i ∧ p.2 ∈ D.fc.I i ∧
          candFit D.b (D.N ^ ε) (D.N ^ (-(D.s₁ - D.vc) - D.vc)) Qp p.1 (D.fc.I i) ∧
          D.N ^ (-ε) ≤ |MvPolynomial.eval (trajV D.b p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) Qp)|} := by
  have hE' := hE
  obtain ⟨d0, d1, κ2, κ1, S0, S1, s₀0, s₀₁, s₁lt, vc0, vcle, hM, hRout, ε0, η0, ηη₁, η₁0, η₁S,
    η₁s₀, η₁1, η₁m, ηS0, εS0, εSε, εS1, Rinv, Rbig, RS⟩ := hE'
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN1' : 1 < D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hκ0 : 0 < D.κ := by linarith
  have hRpos : 0 < D.Rcap := by
    have : 0 < D.M + 4 * D.s₀ + D.s₁ + 10 := by rw [hM]; linarith
    linarith
  set m := D.M + 4 * D.s₀ with hmdef
  set σ := D.N ^ (-m) with hσdef
  set s := D.s₁ - D.s₀ with hsdef
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos hN0 _
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hqc1 : D.fc.q ≤ 1 := by unfold Fam.q; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- exponent comparisons
  have hsc : D.sc = D.s₁ - D.vc := rfl
  have hvcs : D.vc ≤ (D.s₁ - D.s₀) / 4 := by
    have h4κ : 0 < 4 * D.κ := by linarith
    have h := (le_div_iff₀ h4κ).mp vcle
    have h2 : (2 * D.κ - 1) * (D.s₁ - D.s₀) ≤ D.κ * (D.s₁ - D.s₀) := by nlinarith only [κ1, s₀₁]
    by_contra hc
    push Not at hc
    have h3 : 0 < D.κ * (4 * D.vc - (D.s₁ - D.s₀)) := mul_pos hκ0 (by linarith only [hc])
    nlinarith only [h, h2, h3]
  have hsc0 : D.s₀ ≤ D.sc := by rw [hsc]; linarith only [hvcs, s₀₁]
  have hsc1 : D.sc ≤ D.s₁ := by rw [hsc]; linarith only [vc0]
  have hηs₀ : η ≤ D.s₀ / 100000 := by rw [ηη₁]; linarith only [η₁s₀]
  have hκs : D.κ * D.sc ≤ D.sc := by nlinarith only [κ1, hsc0, s₀0]
  have hκs0 : 0 ≤ D.κ * D.sc := by nlinarith only [hκ0, hsc0, s₀0]
  have hmM : D.M ≤ m := by rw [hmdef]; linarith only [s₀0]
  have hM2κ : 2 * D.κ * D.s₀ + η ≤ D.M := by rw [hM]; nlinarith only [κ1, s₀0, hηs₀]
  have hm2κ : 2 * D.κ * D.s₀ ≤ m := by linarith only [hM2κ, hmM, η0]
  have hmκsc : D.κ * D.sc ≤ m := by rw [hmdef, hM]; linarith only [hκs, hsc1, s₁lt, s₀0]
  -- basic comparisons of the scales
  have hχD : D.N ^ (-D.M) ≤ D.Dw := by
    unfold CoreData.Dw; exact rpow_le_rpow_exp hN1 (by linarith only [hM2κ, η0])
  have hDw1 : D.Dw ≤ 1 := by
    unfold CoreData.Dw
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith only [hκ0, s₀0])
  have hDa : D.Dw ≤ D.a₀ := by
    unfold CoreData.Dw CoreData.a₀; exact rpow_le_rpow_exp hN1 (by nlinarith only [κ2, s₀0])
  have ha10 : D.a₁ ≤ D.a₀ := by
    unfold CoreData.a₁ CoreData.a₀; exact rpow_le_rpow_exp hN1 (by linarith only [s₀₁])
  have ha1c : D.a₁ ≤ D.N ^ (-D.sc) := rpow_le_rpow_exp hN1 (by linarith only [hsc1])
  have hσgc : σ ≤ D.N ^ (-D.κ * D.sc) := rpow_le_rpow_exp hN1 (by linarith only [hmκsc])
  have hσ1 : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith only [hmM, hM, s₀0])
  have hacgc : D.N ^ (-D.sc) ≤ D.N ^ (-D.κ * D.sc) := rpow_le_rpow_exp hN1 (by linarith only [hκs])
  have hgcac : (D.N ^ (-D.κ * D.sc)) ^ 2 ≤ D.N ^ (-D.sc) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    exact rpow_le_rpow_exp hN1 (by push_cast; nlinarith only [κ2, hsc0, s₀0])
  have hgc1 : D.N ^ (-D.κ * D.sc) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith only [hκs0])
  obtain ⟨-, hq0⟩ := fam_q_bounds H.f₀good hN0 hK0
  have hσM : σ * D.fc.q ≤ D.N ^ (-D.M) :=
    (mul_le_of_le_one_right hσ0.le hqc1).trans (rpow_le_rpow_exp hN1 (by linarith only [hmM]))
  have hr3eq : D.N ^ (-D.r3 σ) = σ * D.fc.q := N_r3 D H hσ0
  -- the crossing
  have hF1 := num_F1 D H hC₀pos hεL0.le hεLη hKη hB.b1
  have hF2 := num_F2 D H hC₀pos hεL0.le hεLη hKη hχD hDw1 hB.b2
  obtain ⟨-, hWlo, hW⟩ := cross_W D H hC₀pos hεL0.le hF1 hF2
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow hN1 hεL0.le
  have hEη : D.N ^ D.εL ≤ D.N ^ η := rpow_le_rpow_exp hN1 hεLη
  have ha1pos : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hw1 : D.crossW D.M D.Dw (D.Bnat C₀) ≤ 1 := by
    refine hW.trans ?_
    have h1 : 5 * D.N ^ D.εL * D.a₁ ≤ 5 * D.N ^ η * D.N ^ (-D.s₁) := by
      have := mul_le_mul_of_nonneg_right hEη ha1pos.le
      unfold CoreData.a₁ at this ⊢; linarith only [this]
    have h2 : D.N ^ η * D.N ^ (-D.s₁) = D.N ^ (η - D.s₁) := by
      rw [rpow_mul_rpow hN0, ← sub_eq_add_neg]
    have h3 : 5 * D.N ^ η * D.N ^ (-D.s₁) = 5 * D.N ^ (η - D.s₁) := by rw [mul_assoc, h2]
    linarith only [h1, h3, hB.b3]
  have hw1s : -Real.logb D.N (D.crossW D.M D.Dw (D.Bnat C₀)) ≤ D.Rcap := by
    refine (neg_logb_le (s := D.s₁) hN1' ?_).trans (by linarith only [Rbig, hM, s₀0])
    have : D.a₁ ≤ 2 * D.N ^ D.εL * D.a₁ := by nlinarith only [hE1, ha1pos]
    exact this.trans hWlo
  have hok : CrossOK D D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) := by
    have hRM : D.Rcap⁻¹ ≤ D.M := Rinv.trans (by rw [hM]; linarith only [s₀0])
    have hMR : D.M ≤ D.Rcap := by linarith only [Rbig, s₀0, s₀₁]
    exact {
      r1 := hRM
      r2 := hMR
      Hx0 := Real.rpow_pos_of_pos hN0 _
      K₁1 := Real.one_le_rpow hN1 η₁0.le
      M1 := hRM
      M2 := hMR
      s₀0 := s₀0.le
      s₀R := by linarith only [Rbig, s₀0, s₀₁, hM]
      d0 := d0
      d1 := d1
      εL0 := hεL0.le
      coef := fun i => layer_coeff_bound D H hC₀ hεL0.le hDw1 i
      B0 := by unfold CoreData.Bnat; positivity
      w1 := hw1
      w1s := hw1s }
  -- powers of the base
  have hNinvK : D.N ^ (-η) ≤ D.K⁻¹ := by
    rw [Real.rpow_neg hN0.le]; exact inv_anti₀ hK0 hKη
  have hg0 : 0 < D.N ^ (-D.κ * D.s₀) := Real.rpow_pos_of_pos hN0 _
  have hgc0 : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  -- the first pruning
  have hχq : D.N ^ (-D.M) ≤ D.f₀.q * D.N ^ (-D.κ * D.s₀) := by
    have h1 : D.N ^ (-D.κ * D.s₀) * D.N ^ (-η) ≤ D.f₀.q := by
      have := mul_le_mul_of_nonneg_left hNinvK hg0.le
      have h2 : D.N ^ (-D.κ * D.s₀) * D.K⁻¹ ≤ D.f₀.q := by
        rw [← div_eq_mul_inv, div_le_iff₀ hK0]; linarith only [hq0]
      linarith only [this, h2]
    have h3 : D.N ^ (-D.M) ≤ D.N ^ (-D.κ * D.s₀) * D.N ^ (-η) * D.N ^ (-D.κ * D.s₀) := by
      rw [rpow_mul_rpow hN0, rpow_mul_rpow hN0]
      exact rpow_le_rpow_exp hN1 (by linarith only [hM2κ])
    calc D.N ^ (-D.M) ≤ D.N ^ (-D.κ * D.s₀) * D.N ^ (-η) * D.N ^ (-D.κ * D.s₀) := h3
      _ ≤ D.f₀.q * D.N ^ (-D.κ * D.s₀) := mul_le_mul_of_nonneg_right h1 hg0.le
  have hDwq : D.Dw ≤ D.K * D.f₀.q * D.N ^ (-D.κ * D.s₀) := by
    rw [Dw_eq_sq D H, sq]; exact mul_le_mul_of_nonneg_right hq0 hg0.le
  have hg1 : D.N ^ (-D.κ * D.s₀) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith only [hκ0, s₀0])
  have hχ1 : D.N ^ (-D.M) ≤ 1 := hχD.trans hDw1
  have hh3D : σ * D.fc.q ≤ D.Dw :=
    (mul_le_of_le_one_right hσ0.le hqc1).trans (by
      unfold CoreData.Dw; exact rpow_le_rpow_exp hN1 (by linarith only [hm2κ]))
  have hh31 : σ * D.fc.q ≤ 1 := (mul_le_of_le_one_right hσ0.le hqc1).trans hσ1
  -- the cell spread
  have hK2 : D.K ^ 2 ≤ D.N ^ (2 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 2; simpa using this
  have hgc2 : (D.N ^ (-D.κ * D.sc)) ^ 2 = D.N ^ (-2 * D.κ * D.sc) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hb3D : D.cellδ2 σ ≤ D.Dw := by
    refine (cellδ2_le D H hσgc).trans ?_
    rw [hgc2]
    have h1 : 4 * D.K ^ 2 * D.N ^ (-2 * D.κ * D.sc) ≤ 4 * D.N ^ (2 * η) * D.N ^ (-2 * D.κ * D.sc) := by
      gcongr
    have hb := le_rpow_of_big hN0 (C := 4) (x := 2 * η + -2 * D.κ * D.sc) (y := -2 * D.κ * D.s₀)
      (by
        have e : 2 * η + -2 * D.κ * D.sc - -2 * D.κ * D.s₀ = 2 * η - 2 * D.κ * (D.s₁ - D.vc) +
          2 * D.κ * D.s₀ := by rw [hsc]; ring
        rw [e]; exact hB.b4)
    rw [← rpow_mul_rpow hN0] at hb
    unfold CoreData.Dw
    linarith only [h1, hb]
  have hb3pos : 0 < D.cellδ2 σ := by
    unfold CoreData.cellδ2; positivity
  -- the deep labels and the fourth pruning
  obtain ⟨hqe1, hqe2⟩ := num_qe D H (m := m) hKη hB.b5
  have hds := num_deep D H (s := s) hKη κ1 (by unfold CoreData.se; linarith only [s₀0]) hκ0.le
    hDa hq0 hB.b6
  have hloss := num_loss D H hεL0.le hεLη hKη η0 hB.b7
  obtain ⟨hKηS, hmassη⟩ := num_Kη D H hεLη hKη hB.b8
  -- Scalar's density constant
  have ha0pos : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hacpos : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
  have hratio : D.a₀ / D.ac = D.N ^ (D.sc - D.s₀) := by
    unfold CoreData.a₀ CoreData.ac
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have hratio1 : 1 ≤ D.a₀ / D.ac := by
    rw [hratio]; exact Real.one_le_rpow hN1 (by linarith only [hsc0])
  have hc1 : D.N ^ (-(D.s₁ + 1)) ≤ (D.a₀ / D.ac) ^ D.d :=
    (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith only [s₀₁, s₀0])).trans
      (Real.one_le_rpow hratio1 d0)
  have hc2 : (D.a₀ / D.ac) ^ D.d ≤ D.N ^ (D.s₁ + 1) := by
    refine (Real.rpow_le_self_of_one_le hratio1 d1.le).trans ?_
    rw [hratio]; exact rpow_le_rpow_exp hN1 (by linarith only [hsc1, s₀0])
  -- the count cells
  have hr31 : D.Rcap⁻¹ ≤ D.r3 σ := by
    have h1 : Real.logb D.N (σ * D.fc.q) ≤ Real.logb D.N σ :=
      Real.logb_le_logb_of_le hN1' (by positivity) (mul_le_of_le_one_right hσ0.le hqc1)
    have h2 : Real.logb D.N σ = -m := by rw [hσdef, Real.logb_rpow hN0 hN1'.ne']
    unfold CoreData.r3
    rw [hmdef] at h2
    linarith only [h1, h2, Rinv, s₀0, hM]
  have hr32 : D.r3 σ ≤ D.Rcap := by
    unfold CoreData.r3
    refine (neg_logb_le (s := m + D.κ * D.sc + η) hN1' ?_).trans ?_
    · obtain ⟨-, hc2'⟩ := fc_scales D H
      have hq1 : D.N ^ (-D.κ * D.sc) * D.N ^ (-η) ≤ D.fc.q := by
        have := mul_le_mul_of_nonneg_left hNinvK hgc0.le
        have h2 : D.N ^ (-D.κ * D.sc) * D.K⁻¹ ≤ D.fc.q := by
          rw [← div_eq_mul_inv, div_le_iff₀ hK0]; linarith only [hc2']
        linarith only [this, h2]
      calc D.N ^ (-(m + D.κ * D.sc + η)) = σ * (D.N ^ (-D.κ * D.sc) * D.N ^ (-η)) := by
            rw [hσdef, rpow_mul_rpow hN0, rpow_mul_rpow hN0]; congr 1; ring
        _ ≤ σ * D.fc.q := mul_le_mul_of_nonneg_left hq1 hσ0.le
    · have hη1 : η ≤ 1 := by rw [ηη₁]; linarith only [η₁1]
      rw [hmdef]; linarith only [Rbig, hκs, hsc1, hη1, s₀0]
  have hΛ := num_Λ D H (m := m) (s := s) hKη hDa hq0 hgc1 hB.b9
  have h2a0 := num_2a0 D H hB.b10
  have h2a0s : -Real.logb D.N (2 * (D.a₀ * D.N ^ (-s))) ≤ D.Rcap := by
    refine (neg_logb_le (s := D.s₁) hN1' ?_).trans (by linarith only [Rbig, hM, s₀0])
    have e : D.a₀ * D.N ^ (-s) = D.a₁ := by
      unfold CoreData.a₀ CoreData.a₁; rw [hsdef, rpow_mul_rpow hN0]; congr 1; ring
    rw [e]; show D.a₁ ≤ 2 * D.a₁; linarith only [ha1pos]
  have hcapnum := num_cap D H (m := m) hKη hσgc hB.b11
  -- the key crossing estimate and the hidden widths
  have hlip := num_lip D H (m := m) hC₀pos hεL0.le hεLη hKη η₁0.le d0 d1 hχD hDa ha10 hq0 hF1 hF2
    hσgc (by
      have e : (15 * η + 3 * η₁) * (1 / (1 - D.d)) + 2 * η - D.s₀ + 2 * D.κ * D.s₀ -
          2 * D.κ * D.sc + D.s₁ = (15 * η + 3 * η₁) * (1 / (1 - D.d)) + 2 * η - D.s₀ +
          2 * D.κ * D.s₀ - 2 * D.κ * (D.s₁ - D.vc) + D.s₁ := by rw [hsc]
      rw [e]; exact hB.b12)
    (by rw [hsc]; exact hB.b13)
  have hW0 := num_W0 D H (m := m) hσgc hσ1 hacgc hgcac
  have hr3M : D.N ^ (-D.r3 σ) ≤ D.N ^ (-D.M) := by rw [hr3eq]; exact hσM
  obtain ⟨hW3lo, hW3⟩ := num_W3 D H (K₁ := D.N ^ η₁) (C₀ := C₀) (m := m) hεL0.le hW0 hlip hF1 hr3M
    ha1c hC₀pos
  have hW3pos : 0 < D.W3 (D.N ^ η₁) C₀ σ := lt_of_lt_of_le (by positivity) hW3lo
  have hW1 : D.W3 (D.N ^ η₁) C₀ σ ≤ 1 := by
    refine hW3.trans ?_
    have hK5 : D.K ^ 5 ≤ D.N ^ (5 * η) := by
      have := pow_le_rpow_mul hK1 hKη hN0 5; simpa using this
    have h1 : 22 * D.K ^ 5 * D.N ^ D.εL * D.N ^ (-D.sc) ≤
        22 * D.N ^ (5 * η) * D.N ^ η * D.N ^ (-D.sc) := by gcongr
    have h2 : D.N ^ (5 * η) * D.N ^ η * D.N ^ (-D.sc) = D.N ^ (6 * η - (D.s₁ - D.vc)) := by
      rw [rpow_mul_rpow hN0, rpow_mul_rpow hN0, hsc]; congr 1; ring
    have h3 : 22 * D.N ^ (5 * η) * D.N ^ η * D.N ^ (-D.sc) = 22 * D.N ^ (6 * η - (D.s₁ - D.vc)) := by
      rw [← h2]; ring
    linarith only [h1, h3, hB.b15]
  have hWs : -Real.logb D.N (D.W3 (D.N ^ η₁) C₀ σ) ≤ D.Rcap := by
    refine (neg_logb_le (s := D.s₁) hN1' ?_).trans (by linarith only [Rbig, hM, s₀0])
    have : D.a₁ ≤ 2 * D.N ^ D.εL * D.a₁ := by nlinarith only [hE1, ha1pos]
    unfold CoreData.a₁ at this; exact this.trans hW3lo
  have hΛδ := num_Λδ D H (m := m) hKη hDa hq0 hσgc (by
    have e : 6 * η - D.s₀ + 2 * D.κ * D.s₀ - 2 * D.κ * D.sc + D.s₁ =
        6 * η - D.s₀ + 2 * D.κ * D.s₀ - 2 * D.κ * (D.s₁ - D.vc) + D.s₁ := by rw [hsc]
    rw [e]; exact hB.b14)
  have hbs := num_bs D H (K₁ := D.N ^ η₁) (C₀ := C₀) (m := m) (s := s) hεL0.le rfl hlip hF1 hσM hΛδ
    hC₀pos
  have hsupp := num_supp D H (η := η) (η₁ := η₁) (ηS := ηS) (C₀ := C₀) (m := m) (s := s) rfl hεL0.le
    hεLη hKη η₁0.le d0 d1 hσ1 hr3eq hW3 hW3pos hbs hB.b16 hC₀pos
  -- the candidate
  have hfinal : D.N ^ (-D.d * D.vc - ε) ≤ (D.a₀ / D.ac) ^ D.d * (D.N ^ (-s)) ^ D.d *
      D.N ^ (-εS) / D.N ^ εS := by
    rw [hratio, ← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le, rpow_mul_rpow hN0,
      div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0, rpow_mul_rpow hN0]
    exact rpow_le_rpow_exp hN1 (by rw [hsdef, hsc]; nlinarith only [εSε])
  have hfit : D.a₀ * (D.N ^ εS * D.N ^ (-s)) ≤ D.N ^ ε * D.N ^ (-(D.s₁ - D.vc) - D.vc) := by
    unfold CoreData.a₀
    rw [rpow_mul_rpow hN0, rpow_mul_rpow hN0, rpow_mul_rpow hN0]
    exact rpow_le_rpow_exp hN1 (by rw [hsdef]; linarith only [εSε, εS0])
  have hcoef := num_coef D H (η := η) (C₀ := C₀) (εS := εS) (Rout := Rout) hKη η0 hC₀pos εS0 hDa hq0
    hκs0 hB.b17 hB.b18 (by rw [hsc]; exact hB.b19)
  -- conclusion
  exact core_sample D H hSA hNS hC₀ hC₀pos (Real.one_le_rpow hN1 η₁0.le) hok
    (by rw [hsdef]; linarith only [s₀₁]) (by linarith only [s₀₁])
    (by linarith only [Rbig, s₀0, s₀₁, hM]) S0 hRpos εS0 ε0.le hχq hDwq hg1 hχD hχ1 hσM hh3D
    hb3D hh31 hb3pos hW3pos hqe1 hqe2 hds hloss hKηS hc1 hc2 hmassη hr31 hr32 hΛ h2a0 h2a0s
    hcapnum hW1 hWs hb3D hsupp hfinal hfit hcoef

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
