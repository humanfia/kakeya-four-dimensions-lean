import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Assembly
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Grouping
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Recovery
import Submission.Obl.k4_quadratic_finite_greedy_cover.CoverageNumerics

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- The deterministic sample argument, with all asymptotic losses explicit. -/
theorem sample_cover {W C Mc Mp Dp Mg Dg m M : ℕ}
    (Nk L d₁ ρ gain εin ε κ : ℝ)
    (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence)
    (hNlarge : 194 ≤ Nk) (hL : 0 < L) (hd : 0 ≤ d₁) (hd' : d₁ ≤ 1)
    (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 4) (hgain : 0 < gain)
    (hein : 0 ≤ εin) (hein' : εin ≤ ε) (hε' : ε ≤ 1) (hκ : 0 < κ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hωsum : (∑ w,ω w) = 1)
    (hB : ∀ w, 0 < B w) (hm : 0 < m) (hM : 0 < M)
    (hmenu : ∀ h : ℝ, gain ≤ h → h ≤ 1 / 8 → ∃ e : Fin M,
      gain ≤ gain * (1 + ρ) ^ (e : ℕ) ∧ gain * (1 + ρ) ^ (e : ℕ) ≤ h ∧
      h ≤ (1 + ρ) * (gain * (1 + ρ) ^ (e : ℕ)))
    (hAm : ∀ b, MeasurableSet (A b)) (hApos : ∀ b, 0 < (ν (γ b)).real (A b))
    (hAfmt : ∀ b q, fmt 6 (Nk ^ Mp) Dp {w | (q,w) ∈ A b})
    (hlev : ∀ b, lev b < m) (hj : ∀ b, j b < 2 ^ T (lev b))
    (hold : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b'))
    (hHm : ∀ w, MeasurableSet (termInc W C m lev γ F w))
    (hHfin : ∀ w, (ν w).prod volume (termInc W C m lev γ F w) ≠ ∞)
    (hHmass : κ⁻¹ ≤ ∑ w,ω w * ((ν w).prod volume).real (termInc W C m lev γ F w))
    (hdisc : ∀ H : Fin W → Set Incidence,
      (∀ w, MeasurableSet (H w) ∧ H w ⊆ termInc W C m lev γ F w) →
      (∑ w,ω w * ((ν w).prod volume).real (termInc W C m lev γ F w)) / 2 ≤
        ∑ w,ω w * ((ν w).prod volume).real (H w) →
      cand Nk L W ν B Mc d₁ ρ gain εin r T C lev γ j u Q A H)
    (hC : (C : ℝ) ≤ Nk ^ Mp) (hMc : Mc ≤ Mg) (hDg : max Dp 4 ≤ Dg)
    (hMg : 2 * (Mp : ℝ) + (d₁ + ρ) / 8 * L + 3 ≤ (Mg : ℝ))
    (hbase : 2 ≤ Nk ^ (ρ * gain * L / 3)) (habsorb : 2 ≤ Nk ^ ε)
    (hbudget : Nk ^ (-ε) ≤ (κ⁻¹ / 2) / ((m * M * 2 : ℕ) : ℝ) -
      8 / (Nk ^ (ρ * gain * L / 3)) ^ 3) :
    cover Nk L W ω ν B d₁ ρ gain m r T C lev γ j u Q A F Mg Dg ε := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  have hN : 1 ≤ Nk := by linarith
  have hNp : 0 < Nk := by linarith
  let H := termInc W C m lev γ F
  obtain ⟨S,hS,hpriority,hrep,hcard,hcov⟩ := select_mixed_family Nk L d₁ ρ gain εin ν ω B r T lev j γ u Q A H
    hN hL.le hd hρ.le hAm hApos (fun b => by finiteness) hHm hHfin hdisc
  let mass := fun a : Piece C => ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
    (H (γ a.parent) ∩ (a.trajectories ×ˢ block T lev j a.parent))
  have hmassS : κ⁻¹ / 2 ≤ ∑ a ∈ S,mass a := by
    apply le_trans (by linarith : κ⁻¹ / 2 ≤ (∑ w,ω w * ((ν w).prod volume).real (H w)) / 2)
    exact hcov.trans (Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion_weighted_le_sum
      (fun w => (ν w).prod volume) ω hω H S (fun a => γ a.parent)
      (fun a => a.trajectories ×ˢ block T lev j a.parent))
  obtain ⟨i,z,time,U,hUS,hUn,hUi,hgroup⟩ := fixed_group S lev gain ρ (κ⁻¹ / 2) mass hm hM
    (fun a ha => hlev _) (fun a ha => hmenu a.gain (hS a ha).1.1 (hS a ha).1.2.1)
    (by positivity) hmassS
  let h := gain * (1 + ρ) ^ (z : ℕ)
  obtain ⟨a₀,ha₀⟩ := hUn
  have hgainh : gain ≤ h := (hUi a₀ ha₀).2.2.1
  have hh : 0 ≤ h := hgain.le.trans hgainh
  have hlevel (a : Piece C) (ha : a ∈ U) : lev a.parent = (i : ℕ) := (hUi a ha).1
  have htype (a : Piece C) (ha : a ∈ U) : a.time = time := (hUi a ha).2.1
  have hround (a : Piece C) (ha : a ∈ U) : h ≤ a.gain ∧ a.gain ≤ (1 + ρ) * h := (hUi a ha).2.2.2
  let K := Nk ^ (2 * ρ * h * L + 2 * εin)
  let RR := fun a : Piece C => if time then a.poly else MvPolynomial.X (3 : Fin 4)
  let BB := fun w : Fin W => if time then B w else 1
  let V := fun a : Piece C => Submission.Obl.k4_quadratic_finite_greedy_cover.countedPacket
    (H (γ a.parent)) a.trajectories (RR a) (BB (γ a.parent) / K ^ 2) (T i) (j a.parent)
  have hstep : 0 ≤ ρ * gain * L := by positivity
  have hbig : ρ * gain * L ≤ 2 * ρ * h * L + 2 * εin := by
    have hm := mul_le_mul_of_nonneg_left hgainh hρ.le
    have hmL := mul_le_mul_of_nonneg_right hm hL.le
    nlinarith
  have hK : 2 ≤ K := hbase.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hbig,hstep]))
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  have hloss : 8 / K ≤ 8 / (Nk ^ (ρ * gain * L / 3)) ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    rw [← Real.rpow_natCast,← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num
    linarith only [hbig]
  have hsub (a : Piece C) (ha : a ∈ U) : a.trajectories ⊆ A a.parent :=
    (hS a (hUS ha)).2.2.1.trans (envelope_subset Nk L ρ εin B r T lev j γ u Q A a.toTest)
  have hdisj : ∀ a ∈ U, ∀ a' ∈ U, a ≠ a' → γ a.parent = γ a'.parent → j a.parent = j a'.parent →
      Disjoint a.trajectories a'.trajectories := by
    intro a ha a' ha' hne hw hj'
    by_cases hp : a.parent = a'.parent
    · exact hpriority a (hUS ha) a' (hUS ha') hne hp
    · exact (hold _ _ hp ((hlevel a ha).trans (hlevel a' ha').symm) hw hj').mono (hsub a ha) (hsub a' ha')
  have hdegree (a : Piece C) (ha : a ∈ U) : (RR a).totalDegree ≤ 2 := by
    cases ht : time
    · simp [RR,ht]
    · have hta : a.time = true := (htype a ha).trans ht
      have hc : a.poly.totalDegree ≤ 2 ∧ ∀ b,|a.poly.coeff b| ≤ Nk ^ Mc := by
        simpa only [hta,ite_true] using (hS a (hUS ha)).1.2.2.2.2
      simpa only [RR,ht,ite_true] using hc.1
  have hBB (w : Fin W) : 0 < BB w := by cases ht : time <;> simp [BB,ht,hB]
  have hlarge (a : Piece C) (ha : a ∈ U) : ∀ l ∈ a.trajectories,
      ∃ t ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i),
      BB (γ a.parent) / K ≤ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (RR a))| := by
    intro l hl
    cases ht : time
    · refine ⟨(j a.parent : ℝ) / (2 : ℝ) ^ T i,⟨le_rfl,?_⟩,?_⟩
      · apply div_le_div_of_nonneg_right (by linarith) (by positivity)
      · simpa [BB,RR,ht,MvPolynomial.pderiv_X_self] using ((div_le_one hKpos).mpr hKone)
    · have hta : a.time = true := (htype a ha).trans ht
      have hen := (hS a (hUS ha)).2.2.1 hl
      simp only [envelope,hta,ite_true] at hen
      obtain ⟨t,hit,hlo⟩ := hen.2.2.2.2
      refine ⟨t,by simpa only [hlevel a ha] using hit,?_⟩
      have hb := (mixed_buffers Nk ρ h a.gain L εin ε hN hρ.le hρ' hh hL.le
        (hround a ha).1 (hround a ha).2 hein hein' habsorb).1
      have hlower : B (γ a.parent) / Nk ^ (ρ * a.gain * L + εin) ≤
          |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) a.poly)| := by
        simpa only [allowance,x,Submission.Obl.k4_quadratic_finite_greedy_cover.x] using hlo
      simpa [BB,RR,ht,K] using
        (div_le_div_of_nonneg_left (hB _).le (Real.rpow_pos_of_pos hNp _) hb).trans hlower
  have hr := square_counted_recovery W ν ω (fun a : U => γ a.val.parent) (fun a : U => j a.val.parent)
    (T i) (fun a : U => a.val.trajectories) (fun a : U => RR a.val) BB K H hν hω hωsum
    (fun a => (hS a (hUS a.property)).2.1) (fun a => hdegree a a.property) hBB hK
    (fun a => by simpa only [hlevel a a.property] using hj a.val.parent) hHfin
    (fun a a' hne hw hj' => hdisj a a.property a' a'.property (fun heq => hne (Subtype.ext heq)) hw hj')
    (fun a => hlarge a a.property)
  rw [Finset.sum_coe_sort U (fun a : Piece C => ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real
      (H (γ a.parent) ∩ (a.trajectories ×ˢ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i)
        (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i)))),
    Finset.sum_coe_sort U (fun a : Piece C => ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real (V a))] at hr
  have hg' : (κ⁻¹ / 2) / ((m * M * 2 : ℕ) : ℝ) ≤ ∑ a ∈ U,ω (γ a.parent) *
      ((ν (γ a.parent)).prod volume).real (H (γ a.parent) ∩ (a.trajectories ×ˢ
        Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i))) := by
    convert hgroup using 1
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mass,block,hlevel a ha]
  have hVmass : Nk ^ (-ε) ≤ ∑ a ∈ U,ω (γ a.parent) * ((ν (γ a.parent)).prod volume).real (V a) := by
    linarith only [hbudget,hloss,hg',hr]
  have hcomplex := Submission.Obl.k4_quadratic_finite_greedy_cover.priority_polynomial_complexity
    Nk ((d₁ + ρ) / 8 * L) εin (C : ℝ) (S.card : ℝ) Mp Mg hNlarge (by positivity)
    (hein'.trans hε') hC hcard hMg
  exact assemble_cover Nk L d₁ ρ gain εin ε h i time ν ω B r T lev j γ u Q A F S U
    hN hL.le hd hd' hρ.le hρ' hgain hein hein' habsorb hν hω hB hApos hAfmt hHm hHfin
    hS hpriority hrep hold i.isLt hUS ⟨a₀,ha₀⟩ hlevel htype hgainh ⟨z,rfl⟩ hround hDg hMc
    hcomplex.1 hcomplex.2 hK hVmass

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
