-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/DirectPackaging.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Interface
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.ChartGraph

/-!
# Packaging an intercept group as the direct candidate exit

For an old path packet `b`, a polynomial `Q` in the base coordinates `(t, y₁, y₂)` and an
intercept `c`, the *group test*

  `R* = R_b - Q(t, y₁, y₂) - c`

has the same hidden derivatives as the native test `R_b`.  Hence the hidden-derivative upper
bounds of the frozen chart, and its hidden-derivative lower bound on counted incidences, pass
to `R*` unchanged (the hidden curvature bound only improves at a finer width).  What remains
for the direct candidate exit is the value bound of `R*` along the group's trajectories and
the group's original mass; `direct_of_group_test` packages exactly that.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MvPolynomial MeasureTheory

noncomputable section

/-- A polynomial in the base coordinates `(t, y₁, y₂)`, as a polynomial in `(t, y₁, y₂, x₃)`. -/
def liftBase (Q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℝ := rename Fin.castSucc Q

lemma eval_liftBase (Q : MvPolynomial (Fin 3) ℝ) (z : Fin 4 → ℝ) :
    MvPolynomial.eval z (liftBase Q) = MvPolynomial.eval (fun i => z i.castSucc) Q := by
  rw [liftBase, eval_rename]
  rfl

lemma pderiv_three_liftBase (Q : MvPolynomial (Fin 3) ℝ) : pderiv 3 (liftBase Q) = 0 := by
  rw [liftBase]
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
      rw [map_mul, Derivation.leibniz, hp, rename_X, pderiv_X]
      have : (3 : Fin 4) ≠ Fin.castSucc i := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [this.symm]

lemma totalDegree_liftBase_le (Q : MvPolynomial (Fin 3) ℝ) :
    (liftBase Q).totalDegree ≤ Q.totalDegree :=
  totalDegree_rename_le _ _

/-- The group test `R_b - Q - c`. -/
def groupTest (Rb : MvPolynomial (Fin 4) ℝ) (Q : MvPolynomial (Fin 3) ℝ) (c : ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  Rb - liftBase Q - MvPolynomial.C c

lemma eval_groupTest (Rb : MvPolynomial (Fin 4) ℝ) (Q : MvPolynomial (Fin 3) ℝ) (c : ℝ)
    (z : Fin 4 → ℝ) :
    MvPolynomial.eval z (groupTest Rb Q c) =
      MvPolynomial.eval z Rb - MvPolynomial.eval (fun i => z i.castSucc) Q - c := by
  simp [groupTest, eval_liftBase]

lemma pderiv_three_groupTest (Rb : MvPolynomial (Fin 4) ℝ) (Q : MvPolynomial (Fin 3) ℝ)
    (c : ℝ) : pderiv 3 (groupTest Rb Q c) = pderiv 3 Rb := by
  simp [groupTest, pderiv_three_liftBase]

lemma totalDegree_groupTest_le {Rb : MvPolynomial (Fin 4) ℝ} {Q : MvPolynomial (Fin 3) ℝ}
    (c : ℝ) (hR : Rb.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2) :
    (groupTest Rb Q c).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
    (max_le hR ((totalDegree_liftBase_le Q).trans hQ))) ?_)
  simp

/-- The coefficient bound of a group test. -/
lemma abs_coeff_groupTest_le {Rb : MvPolynomial (Fin 4) ℝ} {Q : MvPolynomial (Fin 3) ℝ}
    {c V : ℝ} (hR : ∀ e, |Rb.coeff e| ≤ V) (hQ : ∀ e, |Q.coeff e| ≤ V) (hc : |c| ≤ V)
    (e : Fin 4 →₀ ℕ) : |(groupTest Rb Q c).coeff e| ≤ 3 * V := by
  have hlift : |(liftBase Q).coeff e| ≤ V := by
    classical
    rw [liftBase]
    by_cases h : ∃ d, Finsupp.mapDomain Fin.castSucc d = e
    · obtain ⟨d, rfl⟩ := h
      rw [coeff_rename_mapDomain _ (Fin.castSucc_injective 3)]
      exact hQ d
    · push Not at h
      rw [coeff_rename_eq_zero _ _ _ (fun d hd => absurd hd (h d)), abs_zero]
      exact (abs_nonneg _).trans (hR e)
  have hCc : |(MvPolynomial.C c : MvPolynomial (Fin 4) ℝ).coeff e| ≤ V := by
    rw [coeff_C]
    split_ifs
    · exact hc
    · rw [abs_zero]; exact (abs_nonneg _).trans hc
  rw [groupTest, coeff_sub, coeff_sub]
  calc |Rb.coeff e - (liftBase Q).coeff e - (MvPolynomial.C c).coeff e|
      ≤ |Rb.coeff e| + |(liftBase Q).coeff e| + |(MvPolynomial.C c).coeff e| := by
        have := abs_sub (Rb.coeff e - (liftBase Q).coeff e) ((MvPolynomial.C c).coeff e)
        have := abs_sub (Rb.coeff e) ((liftBase Q).coeff e)
        linarith
    _ ≤ 3 * V := by linarith [hR e]

/-- The frozen mesh is antitone in the depth. -/
lemma δ_antitone {N r r' : ℝ} (hN : 1 ≤ N) (hr : r ≤ r') :
    Submission.Obl.k4_physical_parent_potential_candidates.δ N r' ≤
      Submission.Obl.k4_physical_parent_potential_candidates.δ N r := by
  unfold Submission.Obl.k4_physical_parent_potential_candidates.δ
  apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  apply neg_le_neg
  apply Int.floor_mono
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr hlog) hlog2.le

/-- **Direct candidate from a group test.**  Let `b` be a packet whose frozen chart has slack
`κ ≤ N^(ρ gain L + ε)`, and let `R* = R_b - Q - c` with `Q` quadratic.  If `R*` is small at the
improved width along the group's trajectories throughout the block, and the group's counted
incidences carry the required original mass, the frozen direct exit holds. -/
theorem direct_of_group_test {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Ln} {B : Fin W → ℝ}
    {Mp Dp Mc : ℕ} {d₁ ρ gain ε κ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ} {lev : Fin C → ℕ}
    {γ : Fin C → Fin W} {j : Fin C → ℕ} {A : Fin C → Set Ln} {H : Fin W → Set Ev}
    (b : Fin C) {Evs : Set Ev} {c u : P2} {Qf : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ (T (lev b)) (j b : ℝ) (r (lev b)) (B (γ b)) Evs c u Qf Rb (A b) F ex)
    (hN : 1 ≤ Nk) (hB : 0 < B (γ b)) (hκ1 : 1 ≤ κ) (hκ : κ ≤ Nk ^ (ρ * gain * L + ε))
    (ag : ℝ) (hag : gain ≤ ag) (hag8 : ag ≤ 1 / 8) (hdepth : r (lev b) + 2 * ag * L ≤ L)
    (hagL : 0 ≤ ag * L)
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.totalDegree ≤ 2) (cstar : ℝ)
    (hcoeff : ∀ e, |(groupTest Rb Q cstar).coeff e| ≤ Nk ^ Mc)
    (A' : Set Ln) (hA'm : MeasurableSet A') (hA' : A' ⊆ A b)
    (hval : ∀ l ∈ A', ∀ t ∈ Set.Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b))
        (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b)),
      |MvPolynomial.eval (xp l t) (groupTest Rb Q cstar)| ≤
        Nk ^ (ρ * gain * L + ε) * δ Nk (r (lev b) + ag * L))
    (hmass : ENNReal.ofReal (Nk ^ (-((d₁ * ag + ρ * gain) * L) - ε) / (2:ℝ) ^ T (lev b)) *
        ν (γ b) (A b) ≤
      ((ν (γ b)).prod volume) {p | p ∈ H (γ b) ∧ p ∈ F ∧ p.1 ∈ A' ∧
        p.2 ∈ Set.Icc ((j b : ℝ) / (2:ℝ) ^ T (lev b)) (((j b : ℝ) + 1) / (2:ℝ) ^ T (lev b))}) :
    direct Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hA, hF, _⟩ := hch
  have hpow : 0 < Nk ^ (ρ * gain * L + ε) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hN) _
  have hδ' : 0 < δ Nk (r (lev b) + ag * L) := δ_pos _ _
  have hδle : δ Nk (r (lev b) + ag * L) ≤ δ Nk (r (lev b)) :=
    δ_antitone hN (by linarith)
  refine ⟨b, ag, hag, hag8, hdepth, groupTest Rb Q cstar, A',
    totalDegree_groupTest_le cstar hdeg hQ, hcoeff, hA'm, hA', ?_, ?_⟩
  · intro l hl t ht
    have hAl := (hA l (hA' hl)).2.2 t ht
    refine ⟨hval l hl t ht, ?_, ?_⟩
    · rw [pderiv_three_groupTest]
      calc |MvPolynomial.eval (xp l t) (pderiv 3 Rb)| ≤ κ * B (γ b) := hAl.2.2.1
        _ ≤ Nk ^ (ρ * gain * L + ε) * B (γ b) := mul_le_mul_of_nonneg_right hκ hB.le
    · rw [pderiv_three_groupTest]
      have h1 := hAl.2.2.2
      calc |MvPolynomial.eval (xp l t) (pderiv 3 (pderiv 3 Rb))|
          ≤ κ * B (γ b) ^ 2 / δ Nk (r (lev b)) := h1
        _ ≤ Nk ^ (ρ * gain * L + ε) * B (γ b) ^ 2 / δ Nk (r (lev b)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hκ (by positivity))
              (δ_pos _ _).le
        _ ≤ Nk ^ (ρ * gain * L + ε) * B (γ b) ^ 2 / δ Nk (r (lev b) + ag * L) := by
            apply div_le_div_of_nonneg_left (by positivity) hδ' hδle
  · refine hmass.trans (measure_mono ?_)
    intro p hp
    obtain ⟨hpH, hpF, hpA', hpt⟩ := hp
    refine ⟨hpH, hpA', hpt, ?_⟩
    rw [pderiv_three_groupTest]
    obtain ⟨_, _, _, hder⟩ := hF p hpF
    calc B (γ b) / Nk ^ (ρ * gain * L + ε) ≤ B (γ b) / κ := by
          apply div_le_div_of_nonneg_left hB.le (by linarith) hκ
      _ ≤ |MvPolynomial.eval (xp p.1 p.2) (pderiv 3 Rb)| := hder

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
