import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Candidates
import Submission.Obl.k4_quadratic_finite_greedy_cover.FixedLevel

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

def OutputPiece {W C : ℕ} (Nk L d₁ ρ h ε : ℝ) (Mg Dg i : ℕ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) (time : Bool)
    (a : Piece C) (V : Set Incidence) : Prop :=
  lev a.parent = i ∧ 0 < ν (γ a.parent) (A a.parent) ∧ MeasurableSet a.trajectories ∧
    a.trajectories ⊆ A a.parent ∧
    (∀ q, fmt 6 (Nk ^ Mg) Dg {w | (q,w) ∈ a.trajectories}) ∧
    MeasurableSet V ∧ V ⊆ {p | p ∈ H (γ a.parent) ∧ p.1 ∈ a.trajectories ∧
      p.2 ∈ Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i)} ∧
    if time then a.poly.totalDegree ≤ 2 ∧ (∀ e, |a.poly.coeff e| ≤ Nk ^ Mg) ∧
      (∀ l ∈ a.trajectories, Fits (Nk ^ (4 * ρ * h * L + 4 * ε))
        (δ Nk (r i + h * L)) (B (γ a.parent)) a.poly l
        (Icc ((j a.parent : ℝ) / (2 : ℝ) ^ T i) (((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T i))) ∧
      (∀ p ∈ V, B (γ a.parent) / Nk ^ (4 * ρ * h * L + 4 * ε) ≤
        |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) a.poly)|) ∧
      ENNReal.ofReal (Nk ^ (-((d₁ + 4 * ρ) * h * L) - 4 * ε) / (2 : ℝ) ^ T i) *
        ν (γ a.parent) (A a.parent) ≤ (ν (γ a.parent)).prod volume V
    else (∑ e, (a.normal e) ^ 2) = 1 ∧ |a.bias| ≤ Nk ^ Mg ∧
      (∀ l ∈ a.trajectories, InStrip (T i) (u a.parent) (Q a.parent) a.normal a.bias
        (Nk ^ (4 * ρ * h * L + 4 * ε) * Nk ^ (-h * L)) l) ∧
      ENNReal.ofReal (Nk ^ (-4 * ρ * h * L - 4 * ε) / (2 : ℝ) ^ T i) *
        ν (γ a.parent) (A a.parent) ≤ (ν (γ a.parent)).prod volume V

/-- Finite original-law certificates yield the frozen array form. The sharp
parent count follows from their disjoint incidence floors. -/
theorem cover_of_finite {ι : Type*} [Fintype ι] {W C : ℕ}
    (Nk L d₁ ρ gain h ε : ℝ) (Mg Dg m i : ℕ)
    (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence)
    (time : Bool) (a : ι → Piece C) (V : ι → Set Incidence)
    (hN : 0 < Nk) (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b))
    (hi : i < m) (hg : gain ≤ h) (hh : h ≤ 1 / 8)
    (hmenu : ∃ e : ℕ, h = gain * (1 + ρ) ^ e) (hroom : r i + 2 * h * L ≤ L)
    (hcard : (Fintype.card ι : ℝ) ≤ Nk ^ Mg)
    (hpoint : ∀ b, OutputPiece Nk L d₁ ρ h ε Mg Dg i ν B r T lev j γ u Q A
      (termInc W C m lev γ F) time (a b) (V b))
    (hdisA : ∀ b b', b ≠ b' → (a b).parent = (a b').parent → Disjoint (a b).trajectories (a b').trajectories)
    (hdisV : ∀ b b', b ≠ b' → γ (a b).parent = γ (a b').parent → Disjoint (V b) (V b'))
    (hmass : Nk ^ (-ε) ≤ ∑ b, ω (γ (a b).parent) * ((ν (γ (a b).parent)).prod volume).real (V b)) :
    cover Nk L W ω ν B d₁ ρ gain m r T C lev γ j u Q A F Mg Dg ε := by
  classical
  have (w : Fin W) : IsProbabilityMeasure (ν w) := hν w
  let n := Fintype.card ι
  let e : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let datum := fun b : Fin n => a (e b)
  let VV := fun b : Fin n => V (e b)
  have hp (b : Fin n) : OutputPiece Nk L d₁ ρ h ε Mg Dg i ν B r T lev j γ u Q A
      (termInc W C m lev γ F) time (datum b) (VV b) := hpoint (e b)
  have hVfin (b : Fin n) : (ν (γ (datum b).parent)).prod volume (VV b) ≠ ∞ := by
    apply measure_ne_top_of_subset (s := A (datum b).parent ×ˢ
      Icc ((j (datum b).parent : ℝ) / (2 : ℝ) ^ T i) (((j (datum b).parent : ℝ) + 1) / (2 : ℝ) ^ T i))
    · intro p hpp
      have ht := (hp b).2.2.2.2.2.2.1 hpp
      exact ⟨(hp b).2.2.2.1 ht.2.1,ht.2.2⟩
    · rw [Measure.prod_prod,Real.volume_Icc]
      finiteness
  refine ⟨i,h,n,(fun b => (datum b).parent),(fun b => (datum b).poly),
    (fun b => (datum b).normal),(fun b => (datum b).bias),
    (fun b => (datum b).trajectories),VV,time,hi,hg,hh,hmenu,hroom,hcard,hp,?_,?_,?_,?_⟩
  · intro b b' hne hp'
    exact hdisA _ _ (fun heq => hne (e.injective heq)) hp'
  · intro old
    let U : Set Incidence := A old ×ˢ Icc ((j old : ℝ) / (2 : ℝ) ^ T i)
      (((j old : ℝ) + 1) / (2 : ℝ) ^ T i)
    let θ : ℝ := Nk ^ (-((if time then d₁ + 4 * ρ else 4 * ρ) * h * L) - 4 * ε)
    let s := Finset.univ.filter (fun b : Fin n => (datum b).parent = old)
    have hθ : 0 < θ := Real.rpow_pos_of_pos hN _
    have hUf : (ν (γ old)).prod volume U ≠ ∞ := by
      dsimp [U]
      rw [Measure.prod_prod, Real.volume_Icc]
      finiteness
    have hlen : ((j old : ℝ) + 1) / (2 : ℝ) ^ T i - (j old : ℝ) / (2 : ℝ) ^ T i = 1 / (2 : ℝ) ^ T i := by ring
    have hUp : 0 < ((ν (γ old)).prod volume).real U := by
      rw [measureReal_def, Measure.prod_prod, Real.volume_Icc, hlen,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 : ℝ) ^ T i)]
      exact mul_pos (hApos old) (by positivity)
    have hVs : ∀ b ∈ s, MeasurableSet (VV b) ∧ VV b ⊆ U := by
      intro b hb
      have hold := (Finset.mem_filter.mp hb).2
      refine ⟨(hp b).2.2.2.2.2.1,?_⟩
      intro p hpp
      have ht := (hp b).2.2.2.2.2.2.1 hpp
      simpa only [U,hold,mem_prod] using (show p.1 ∈ A (datum b).parent ∧
        p.2 ∈ Icc ((j (datum b).parent : ℝ) / (2 : ℝ) ^ T i)
          (((j (datum b).parent : ℝ) + 1) / (2 : ℝ) ^ T i) from ⟨(hp b).2.2.2.1 ht.2.1,ht.2.2⟩)
    have hfloor : ∀ b ∈ s, ENNReal.ofReal θ * (ν (γ old)).prod volume U ≤
        (ν (γ old)).prod volume (VV b) := by
      intro b hb
      have hold := (Finset.mem_filter.mp hb).2
      have hf : ENNReal.ofReal (θ / (2 : ℝ) ^ T i) * ν (γ old) (A old) ≤
          (ν (γ old)).prod volume (VV b) := by
        have hpp := (hp b).2.2.2.2.2.2.2
        cases ht : time <;> simp only [ht, Bool.false_eq_true, ite_false, ite_true] at hpp ⊢
        · simpa [θ, ht, hold, neg_mul] using hpp.2.2.2
        · simpa [θ, ht, hold] using hpp.2.2.2.2
      convert hf using 1
      rw [Measure.prod_prod, Real.volume_Icc]
      rw [hlen]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.ofReal_mul hθ.le]
      simp only [one_mul]
      ac_rfl
    have hd : (s : Set (Fin n)).PairwiseDisjoint VV := by
      intro b hb b' hb' hne
      apply hdisV _ _ (fun heq => hne (e.injective heq))
      exact congrArg γ ((Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hb').2.symm)
    have hc := Submission.Obl.k4_quadratic_finite_greedy_cover.card_le_inv_relative_floor
      ((ν (γ old)).prod volume) U VV s hθ hUp hUf hVs hd hfloor
    have hInv : θ⁻¹ = Nk ^ ((if time then d₁ + 4 * ρ else 4 * ρ) * h * L + 4 * ε) := by
      rw [← Real.rpow_neg hN.le]
      congr 1
      ring
    exact hc.trans_eq hInv
  · intro b b' hne hw
    exact hdisV _ _ (fun heq => hne (e.injective heq)) hw
  · have hm : Nk ^ (-ε) ≤ ∑ b : Fin n, ω (γ (datum b).parent) *
        ((ν (γ (datum b).parent)).prod volume).real (VV b) := by
      exact hmass.trans_eq (e.sum_comp (fun c => ω (γ (a c).parent) *
        ((ν (γ (a c).parent)).prod volume).real (V c))).symm
    have hh := ENNReal.ofReal_le_ofReal hm
    rw [Submission.Obl.k4_quadratic_finite_greedy_cover.ofReal_weighted_mass
      (fun b : Fin n => (ν (γ (datum b).parent)).prod volume)
      (fun b => ω (γ (datum b).parent)) VV (fun b => hω _) hVfin] at hh
    exact hh

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
