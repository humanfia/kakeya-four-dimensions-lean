import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Candidates
import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Menu
import Submission.Obl.k4_quadratic_finite_greedy_cover.MenuSelection

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
noncomputable section

/-- One level, geometric gain entry and candidate type retain their fixed
share of any finite mixed family. -/
theorem fixed_group {C m M : ℕ} (S : Finset (Piece C)) (lev : Fin C → ℕ)
    (gain ρ c : ℝ) (mass : Piece C → ℝ) (hm : 0 < m) (hM : 0 < M)
    (hlev : ∀ a ∈ S, lev a.parent < m)
    (hmenu : ∀ a ∈ S, ∃ e : Fin M, gain ≤ gain * (1 + ρ) ^ (e : ℕ) ∧
      gain * (1 + ρ) ^ (e : ℕ) ≤ a.gain ∧ a.gain ≤ (1 + ρ) * (gain * (1 + ρ) ^ (e : ℕ)))
    (hc : 0 < c) (hmass : c ≤ ∑ a ∈ S, mass a) :
    ∃ i : Fin m, ∃ e : Fin M, ∃ time : Bool, ∃ U : Finset (Piece C),
      U ⊆ S ∧ U.Nonempty ∧
      (∀ a ∈ U, lev a.parent = i ∧ a.time = time ∧
        gain ≤ gain * (1 + ρ) ^ (e : ℕ) ∧ gain * (1 + ρ) ^ (e : ℕ) ≤ a.gain ∧
        a.gain ≤ (1 + ρ) * (gain * (1 + ρ) ^ (e : ℕ))) ∧
      c / ((m * M * 2 : ℕ) : ℝ) ≤ ∑ a ∈ U, mass a := by
  classical
  let label : Piece C → Fin m × Fin M × Bool := fun a =>
    if ha : a ∈ S then (⟨lev a.parent,hlev a ha⟩,(hmenu a ha).choose,a.time)
    else (⟨0,hm⟩,⟨0,hM⟩,false)
  let f : (Fin m × Fin M × Bool) → ℝ := fun p => ∑ a ∈ S, if label a = p then mass a else 0
  have hsum : ∑ p, f p = ∑ a ∈ S, mass a := by
    dsimp [f]
    rw [Finset.sum_comm]
    simp
  obtain ⟨⟨i,e,time⟩,_,havg⟩ := Submission.Obl.k4_finite_row_graph_assembly.exists_ge_avg
    Finset.univ f c (by exact ⟨(⟨0,hm⟩,⟨0,hM⟩,false),Finset.mem_univ _⟩)
    (by rw [hsum]; exact hmass)
  let U := S.filter (fun a => label a = (i,e,time))
  have hmU : c / ((m * M * 2 : ℕ) : ℝ) ≤ ∑ a ∈ U, mass a := by
    simpa [f, U, Finset.sum_filter, Nat.mul_assoc] using havg
  have hden : (0 : ℝ) < ((m * M * 2 : ℕ) : ℝ) := by positivity
  have hUn : U.Nonempty := by
    by_contra hn
    have hzero := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hzero,Finset.sum_empty] at hmU
    exact (not_le_of_gt (div_pos hc hden)) hmU
  refine ⟨i,e,time,U,Finset.filter_subset _ _,hUn,?_,hmU⟩
  intro a ha
  obtain ⟨has,heq⟩ := Finset.mem_filter.mp ha
  have heq' : (⟨lev a.parent,hlev a has⟩,(hmenu a has).choose,a.time) = (i,e,time) := by
    simpa only [label,dif_pos has] using heq
  have hi : lev a.parent = (i : ℕ) := congrArg (fun p : Fin m × Fin M × Bool => (p.1 : ℕ)) heq'
  have he : (hmenu a has).choose = e := congrArg (fun p : Fin m × Fin M × Bool => p.2.1) heq'
  have ht : a.time = time := congrArg (fun p : Fin m × Fin M × Bool => p.2.2) heq'
  exact ⟨hi,ht,by simpa only [he] using (hmenu a has).choose_spec⟩

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
