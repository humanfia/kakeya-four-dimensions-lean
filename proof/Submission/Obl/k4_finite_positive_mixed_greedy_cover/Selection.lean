import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Candidates
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Priority

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open scoped ENNReal
noncomputable section

def PieceGood {W C : ℕ} (Nk L : ℝ) (Mc : ℕ) (d₁ ρ gain ε : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) (a : Piece C) : Prop :=
  TestGood Nk L Mc gain ν r lev γ A a.toTest ∧
    MeasurableSet a.trajectories ∧
    a.trajectories ⊆ envelope Nk L ρ ε B r T lev j γ u Q A a.toTest ∧
    ENNReal.ofReal (relativeFloor Nk L d₁ ρ ε a.toTest / (2 : ℝ) ^ T (lev a.parent)) *
      ν (γ a.parent) (A a.parent) ≤
      (ν (γ a.parent)).prod volume (witness Nk L ρ ε B T lev j γ H a)

theorem piece_trajectory_floor {W C Mc : ℕ} (Nk L d₁ ρ gain ε : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence) (a : Piece C)
    (hN : 0 ≤ Nk) (ha : PieceGood Nk L Mc d₁ ρ gain ε ν B r T lev j γ u Q A H a) :
    ENNReal.ofReal (relativeFloor Nk L d₁ ρ ε a.toTest) * ν (γ a.parent) (A a.parent) ≤
      ν (γ a.parent) a.trajectories := by
  have hi : ((j a.parent : ℝ) + 1) / (2 : ℝ) ^ T (lev a.parent) =
      (j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent) + 1 / (2 : ℝ) ^ T (lev a.parent) := by ring
  apply Submission.Obl.k4_quadratic_finite_greedy_cover.trajectory_floor_of_product_floor
    (ν (γ a.parent)) (A a.parent) a.trajectories
    (witness Nk L ρ ε B T lev j γ H a)
    ((j a.parent : ℝ) / (2 : ℝ) ^ T (lev a.parent)) (1 / (2 : ℝ) ^ T (lev a.parent))
    (relativeFloor Nk L d₁ ρ ε a.toTest) (by positivity)
    (Real.rpow_nonneg hN _) (by
      intro p hp
      exact ⟨hp.2.1, by simpa only [block, hi] using hp.2.2.1⟩)
  simpa only [mul_one_div] using ha.2.2.2

theorem uniform_relative_floor {C : ℕ} (Nk L d₁ ρ ε : ℝ) (a : Test C)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hρ : 0 ≤ ρ)
    (hh : a.gain ≤ 1 / 8) :
    Nk ^ (-((d₁ + ρ) / 8 * L) - ε) ≤ relativeFloor Nk L d₁ ρ ε a := by
  apply Real.rpow_le_rpow_of_exponent_le hN
  split_ifs
  · have hx := mul_le_mul_of_nonneg_left hh (add_nonneg hd₁ hρ)
    nlinarith [mul_le_mul_of_nonneg_right hx hL]
  · have hx := mul_le_mul_of_nonneg_left hh hρ
    have hy : ρ * a.gain ≤ (d₁ + ρ) / 8 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hy hL]

/-- Mixed residual discovery gives a finite family of priority envelopes. -/
theorem select_mixed_family {W C Mc : ℕ} (Nk L d₁ ρ gain ε : ℝ)
    (ν : Fin W → Measure Trajectory) (ω : Fin W → ℝ) (B : Fin W → ℝ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (lev j : Fin C → ℕ) (γ : Fin C → Fin W)
    (u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set Trajectory) (H : Fin W → Set Incidence)
    (hN : 1 ≤ Nk) (hL : 0 ≤ L) (hd₁ : 0 ≤ d₁) (hρ : 0 ≤ ρ)
    (hAm : ∀ b, MeasurableSet (A b))
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b)) (hAfin : ∀ b, ν (γ b) (A b) ≠ ∞)
    (hHm : ∀ w, MeasurableSet (H w)) (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hdisc : ∀ R : Fin W → Set Incidence, (∀ w, MeasurableSet (R w) ∧ R w ⊆ H w) →
      (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (R w) →
      cand Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A R) :
    ∃ S : Finset (Piece C),
      (∀ a ∈ S, PieceGood Nk L Mc d₁ ρ gain ε ν B r T lev j γ u Q A H a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → a.parent = a'.parent → Disjoint a.trajectories a'.trajectories) ∧
      (∀ a ∈ S, ∃ P : Finset (Piece C), P ⊆ S ∧
        a.trajectories = envelope Nk L ρ ε B r T lev j γ u Q A a.toTest \
          Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion P pieceParent
            (fun a => envelope Nk L ρ ε B r T lev j γ u Q A a.toTest) a.parent) ∧
      (S.card : ℝ) ≤ (C : ℝ) * Nk ^ ((d₁ + ρ) / 8 * L + ε) ∧
      (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real
          (H w ∩ Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion S
            (fun a => γ a.parent) (fun a => a.trajectories ×ˢ block T lev j a.parent) w) := by
  classical
  let E := fun a : Piece C => envelope Nk L ρ ε B r T lev j γ u Q A a.toTest
  let Good := PieceGood Nk L Mc d₁ ρ gain ε ν B r T lev j γ u Q A H
  let θ := Nk ^ (-((d₁ + ρ) / 8 * L) - ε)
  have hθ : 0 < θ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hgood (a : Piece C) (ha : Good a) : MeasurableSet a.trajectories ∧
      a.trajectories ⊆ A a.parent ∧ MeasurableSet (block T lev j a.parent) ∧
      θ ≤ (ν (γ a.parent)).real a.trajectories / (ν (γ a.parent)).real (A a.parent) := by
    refine ⟨ha.2.1, ha.2.2.1.trans (envelope_subset Nk L ρ ε B r T lev j γ u Q A a.toTest),
      measurableSet_Icc, ?_⟩
    apply Submission.Obl.k4_quadratic_finite_greedy_cover.normalized_measure_floor
      (ν (γ a.parent)) (A a.parent) a.trajectories (hApos _) (hAfin _)
      (ha.2.2.1.trans (envelope_subset Nk L ρ ε B r T lev j γ u Q A a.toTest)) hθ.le
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (uniform_relative_floor Nk L d₁ ρ ε a.toTest hN hL hd₁ hρ ha.1.2.1)) le_rfl).trans
      (piece_trajectory_floor Nk L d₁ ρ gain ε ν B r T lev j γ u Q A H a
        (le_trans zero_le_one hN) ha)
  have hselect : ∀ S : Finset (Piece C), (∀ a ∈ S, Good a) →
      ∀ R : Fin W → Set Incidence, (∀ w, MeasurableSet (R w) ∧ R w ⊆ H w) →
      (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (R w) →
      (∀ w, R w = H w \ Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion S
        (fun a => γ a.parent) (fun a => a.trajectories ×ˢ block T lev j a.parent) w) →
      ∃ a, Good a ∧ a.trajectories = E a \
        Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion S pieceParent Piece.trajectories a.parent := by
    intro S hS R hR hmass hReq
    obtain ⟨a, ha, hf⟩ := candidate_piece Nk L d₁ ρ gain ε ν B r T lev j γ u Q A R
      (hdisc R hR hmass)
    let Prev := Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion S pieceParent Piece.trajectories a.parent
    let a' : Piece C := ⟨a, envelope Nk L ρ ε B r T lev j γ u Q A a \ Prev⟩
    have hEm : MeasurableSet (envelope Nk L ρ ε B r T lev j γ u Q A a) :=
      envelope_measurable Nk L ρ ε B r T lev j γ u Q A a (hAm _) (by
        intro ht
        have hh : a.poly.totalDegree ≤ 2 ∧ ∀ e, |a.poly.coeff e| ≤ Nk ^ Mc := by
          simpa only [ht, if_true] using ha.2.2.2.2
        exact hh.1)
    have hPm : MeasurableSet Prev := Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion_measurable
      S pieceParent Piece.trajectories (fun b hb => (hS b hb).2.1) a.parent
    refine ⟨a', ⟨ha, hEm.diff hPm, sdiff_subset, hf.trans (measure_mono ?_)⟩, rfl⟩
    intro p hp
    refine ⟨(hR _).2 hp.1, ⟨hp.2.1, ?_⟩, hp.2.2⟩
    intro hprev
    obtain ⟨b,hb,hba,hl⟩ := mem_iUnion₂.mp hprev
    have ht : p.2 ∈ block T lev j b.parent := by simpa only [hba] using hp.2.2.1
    have hc : p ∈ Submission.Obl.k4_quadratic_finite_greedy_cover.selectedUnion S
        (fun a => γ a.parent) (fun a => a.trajectories ×ˢ block T lev j a.parent) (γ a.parent) :=
      mem_iUnion₂.mpr ⟨b,hb,congrArg γ hba,hl,ht⟩
    exact ((hReq _ ▸ hp.1).2) hc
  obtain ⟨S,hS,hd,hrep,hcard,hcov⟩ := mixed_priority_selection ν ω H A γ pieceParent
    Piece.trajectories E (fun a => block T lev j a.parent) Good hθ hApos hAfin hHm hHfin hgood hselect
  refine ⟨S,hS,hd,hrep,?_,hcov⟩
  have hInv : θ⁻¹ = Nk ^ ((d₁ + ρ) / 8 * L + ε) := by
    rw [← Real.rpow_neg (le_trans zero_le_one hN)]
    congr 1
    ring
  simpa only [Fintype.card_fin, div_eq_mul_inv, hInv] using hcard

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
