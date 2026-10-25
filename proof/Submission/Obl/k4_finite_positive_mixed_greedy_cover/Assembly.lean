import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Rounding
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Format
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Output

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- A fixed group of mixed priority pieces gives the final cover certificate. -/
theorem assemble_cover {W C Mc Mp Dp Mg Dg m : ℕ}
    (Nk L d₁ ρ gain e ε h : ℝ) (i : ℕ) (time : Bool)
    (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence)
    (S U : Finset (Piece C))
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd : 0 ≤ d₁) (hd' : d₁ ≤ 1)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1 / 4) (hgain : 0 < gain)
    (he : 0 ≤ e) (he' : e ≤ ε) (habsorb : 2 ≤ Nk ^ ε)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hB : ∀ w, 0 < B w)
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b))
    (hAfmt : ∀ b q, fmt 6 (Nk ^ Mp) Dp {w | (q,w) ∈ A b})
    (hHm : ∀ w, MeasurableSet (termInc W C m lev γ F w))
    (hHfin : ∀ w, (ν w).prod volume (termInc W C m lev γ F w) ≠ ∞)
    (hS : ∀ a ∈ S, PieceGood Nk L Mc d₁ ρ gain e ν B r T lev j γ u Q A (termInc W C m lev γ F) a)
    (hpriority : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent → Disjoint a.trajectories a'.trajectories)
    (hrep : ∀ a ∈ S, ∃ P : Finset (Piece C), P ⊆ S ∧ a.trajectories =
      envelope Nk L ρ e B r T lev j γ u Q A a.toTest \
        Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion P pieceParent
          (fun a => envelope Nk L ρ e B r T lev j γ u Q A a.toTest) a.parent)
    (hold : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hi : i < m) (hUS : U ⊆ S) (hUn : U.Nonempty)
    (hUi : ∀ a ∈ U, lev a.parent = i) (hUt : ∀ a ∈ U, a.time = time)
    (hgainh : gain ≤ h) (hmenu : ∃ z : ℕ, h = gain * (1 + ρ) ^ z)
    (hUg : ∀ a ∈ U, h ≤ a.gain ∧ a.gain ≤ (1 + ρ) * h)
    (hDg : max Dp 4 ≤ Dg) (hMc : Mc ≤ Mg) (hScard : (S.card : ℝ) ≤ Nk ^ Mg)
    (hformat : ((S.card : ℝ) + 1) * (Nk ^ Mp + 96) ≤ Nk ^ Mg)
    (hK : 2 ≤ Nk ^ (2 * ρ * h * L + 2 * e))
    (hmass : Nk ^ (-ε) ≤ ∑ a ∈ U, ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
      (Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket
        (termInc W C m lev γ F (γ a.parent)) a.trajectories
        (if time then a.poly else MvPolynomial.X (3 : Fin 4))
        ((if time then B (γ a.parent) else 1) / (Nk ^ (2 * ρ * h * L + 2 * e)) ^ 2) (T i) (j a.parent))) :
    cover Nk L W ω ν B d₁ ρ gain m r T C lev γ j u Q A F Mg Dg ε := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  have hNp : 0 < Nk := lt_of_lt_of_le zero_lt_one hN
  have hh : 0 ≤ h := hgain.le.trans hgainh
  have hε : 0 ≤ ε := he.trans he'
  let K := Nk ^ (2 * ρ * h * L + 2 * e)
  let slack := Nk ^ (4 * ρ * h * L + 4 * ε)
  let H := termInc W C m lev γ F
  let R := fun a : Piece C => if time then a.poly else MvPolynomial.X (3 : Fin 4)
  let BB := fun w : Fin W => if time then B w else 1
  let V := fun a : Piece C => Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket
    (H (γ a.parent)) a.trajectories (R a) (BB (γ a.parent) / K ^ 2) (T i) (j a.parent)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hKone : 1 ≤ K := by dsimp [K]; linarith
  obtain ⟨a₀,ha₀⟩ := hUn
  have hcap : h ≤ 1 / 8 := (hUg a₀ ha₀).1.trans (hS a₀ (hUS ha₀)).1.2.1
  have hroom : r i + 2 * h * L ≤ L := by
    have hr := (hS a₀ (hUS ha₀)).1.2.2.1
    rw [hUi a₀ ha₀] at hr
    nlinarith [mul_le_mul_of_nonneg_right (hUg a₀ ha₀).1 hL]
  have hsub (a : Piece C) (ha : a ∈ U) : a.trajectories ⊆ A a.parent :=
    (hS a (hUS ha)).2.2.1.trans (envelope_subset Nk L ρ e B r T lev j γ u Q A a.toTest)
  have hdisj : ∀ a ∈ U, ∀ a' ∈ U, a ≠ a' → γ a.parent = γ a'.parent → j a.parent = j a'.parent →
      Disjoint a.trajectories a'.trajectories := by
    intro a ha a' ha' hne hw hj
    by_cases hp : a.parent = a'.parent
    · exact hpriority a (hUS ha) a' (hUS ha') hne hp
    · exact (hold _ _ hp ((hUi a ha).trans (hUi a' ha').symm) hw hj).mono (hsub a ha) (hsub a' ha')
  have hpoint (a : Piece C) (ha : a ∈ U) :
      OutputPiece Nk L d₁ ρ h ε Mg Dg i ν B r T lev j γ u Q A H time a (V a) := by
    have hgood := hS a (hUS ha)
    have hbuf := mixed_buffers Nk ρ h a.gain L e ε hN hρ hρ' hh hL (hUg a ha).1 (hUg a ha).2 he he' habsorb
    have hKsq : K ≤ K ^ 2 := le_self_pow₀ hKone (by norm_num)
    have hfloorV : ENNReal.ofReal (relativeFloor Nk L d₁ ρ e a.toTest / (2 : ℝ) ^ T i) *
        ν (γ a.parent) (A a.parent) ≤ (ν (γ a.parent)).prod volume (V a) := by
      have hf := hgood.2.2.2
      rw [hUi a ha] at hf
      apply hf.trans
      apply Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket_measure_ge_witness
      intro p hp
      refine ⟨hp.1,hp.2.1,by simpa only [block,hUi a ha] using hp.2.2.1,?_⟩
      cases ht : time
      · simpa [R,BB,ht] using (div_le_one (by positivity : 0 < K ^ 2)).mpr (one_le_pow₀ hKone (n := 2))
      · have hta : a.time = true := (hUt a ha).trans ht
        have hb : B (γ a.parent) / K ^ 2 ≤ B (γ a.parent) / allowance Nk L ρ e a.toTest :=
          div_le_div_of_nonneg_left (hB _).le
            (Real.rpow_pos_of_pos hNp _) (hbuf.1.trans hKsq)
        have hd : B (γ a.parent) / allowance Nk L ρ e a.toTest ≤
            |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) a.poly)| := by
          simpa [derivativeTest,hta] using hp.2.2.2
        simpa [R,BB,ht] using hb.trans hd
    have hexp := rounded_exponents d₁ ρ a.gain h L e ε hd hd' hρ hρ' hh hL (hUg a ha).2 he' hε
    have hfloor : ENNReal.ofReal (Nk ^ (-((if time then d₁ + 4 * ρ else 4 * ρ) * h * L) - 4 * ε) / (2 : ℝ) ^ T i) *
        ν (γ a.parent) (A a.parent) ≤ (ν (γ a.parent)).prod volume (V a) := by
      apply le_trans (b := ENNReal.ofReal (relativeFloor Nk L d₁ ρ e a.toTest / (2 : ℝ) ^ T i) * ν (γ a.parent) (A a.parent)) _ hfloorV
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hN
      rw [hUt a ha]
      cases time <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith
    refine ⟨hUi a ha,hgood.1.2.2.2.1,hgood.2.1,hsub a ha,?_,?_,?_,?_⟩
    · intro q
      obtain ⟨P,hP,hPa⟩ := hrep a (hUS ha)
      have hf := mixed_priority_format S pieceParent Piece.trajectories
        (fun a => envelope Nk L ρ e B r T lev j γ u Q A a.toTest)
        (Nk ^ Mp + 96) (max Dp 4) (by positivity)
        (fun a ha q => envelope_format Nk L ρ e B r T lev j γ u Q A a.toTest
          (Nk ^ Mp) Dp q (hAfmt _ q) (by
            intro ht
            have hc : a.poly.totalDegree ≤ 2 ∧ ∀ b, |a.poly.coeff b| ≤ Nk ^ Mc := by
              simpa only [ht,ite_true] using (hS a ha).1.2.2.2.2
            exact hc.1)) a (hUS ha) P hP hPa q
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono hf hformat hDg
    · exact Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket_measurable _ _ (hHm _) hgood.2.1 _ _ _ _
    · intro p hp
      exact ⟨hp.1,hp.2.1,hp.2.2.1.1,hp.2.2.1.2.le⟩
    · cases ht : time
      · have hta : a.time = false := (hUt a ha).trans ht
        have hc : (∑ e, a.normal e ^ 2) = 1 ∧ |a.bias| ≤ Nk ^ Mc := by
          simpa [hta] using hgood.1.2.2.2.2
        refine ⟨hc.1,hc.2.trans (pow_le_pow_right₀ hN hMc),?_,?_⟩
        · intro l hl
          have hel := hgood.2.2.1 hl
          simp [envelope,hta] at hel
          have hw : allowance Nk L ρ e a.toTest * Nk ^ (-(a.gain * L)) ≤
              Nk ^ (4 * ρ * h * L + 4 * ε) * Nk ^ (-h * L) := by
            simpa only [allowance,neg_mul] using hbuf.2.2.2
          simpa only [InStrip,hUi a ha] using hel.2.trans hw
        · simpa [ht,neg_mul] using hfloor
      · have hta : a.time = true := (hUt a ha).trans ht
        have hc : a.poly.totalDegree ≤ 2 ∧ ∀ b, |a.poly.coeff b| ≤ Nk ^ Mc := by
          simpa only [hta,ite_true] using hgood.1.2.2.2.2
        refine ⟨hc.1,(fun b => (hc.2 b).trans (pow_le_pow_right₀ hN hMc)),?_,?_,?_⟩
        · have hf := rounded_time_fit Nk L d₁ ρ gain e ε h ν B r T lev j γ u Q A H a
            hgood hta hN hL hρ hρ' hh (hUg a ha).1 (hUg a ha).2 he he' habsorb (hB _).le
          simpa only [block,hUi a ha] using hf
        · intro p hp
          exact (div_le_div_of_nonneg_left (hB _).le (pow_pos hKpos _) hbuf.2.1).trans
            (by simpa only [R,BB,ht,ite_true] using hp.2.2.2)
        · simpa only [ht,ite_true] using hfloor
  apply cover_of_finite Nk L d₁ ρ gain h ε Mg Dg m i ν ω B r T lev j γ u Q A F time
    (fun a : U => a.val) (fun a : U => V a) hNp hν hω hApos hi hgainh hcap hmenu hroom
  · have hc : (U.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hUS
    simpa only [Fintype.card_coe] using hc.trans hScard
  · exact fun a => hpoint a a.property
  · intro a a' hne hp
    exact hpriority a (hUS a.property) a' (hUS a'.property) (fun heq => hne (Subtype.ext heq)) hp
  · intro a a' hne hw
    apply Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket_disjoint Piece.trajectories R
      (fun a => BB (γ a.parent) / K ^ 2) (fun a => j a.parent) (T i)
      (fun a => H (γ a.parent)) a.val a'.val
    exact fun hj => hdisj a a.property a' a'.property (fun heq => hne (Subtype.ext heq)) hw hj
  · rw [Finset.sum_coe_sort U (fun a => ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real (V a))]
    exact hmass

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
