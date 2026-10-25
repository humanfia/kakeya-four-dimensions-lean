import Submission.Obl.k4_angular_normal_pair_preparation.NativeSample

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory
open scoped ENNReal BigOperators

namespace NativeSample

variable {aligned : Prop} {lam Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ} {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (q : NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

/-- A sample at a smaller asymptotic tolerance is also a sample at a larger one. -/
noncomputable def withSlack (εNew : ℝ) (hN : 1 ≤ Nk) (hε : ε ≤ εNew) :
    NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths εNew :=
  { q with
    κ_le := q.κ_le.trans (Real.rpow_le_rpow_of_exponent_le hN hε)
    hT := q.hT.trans (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl hε)) }

/-- The required relation between two old frames at the new analytic loss. -/
def Alignment (aNew : ℝ) (b b' : Fin q.C) : Prop :=
  q.R₁ ≤ 8 * Nk ^ aNew * q.R₂ ∨
    |wedge (nrm (q.Q b)) (nrm (q.Q b'))| ≤
      min (1 / 8 : ℝ) (Nk ^ aNew * q.R₂ / q.R₁)

/-- Keep the same pair event when its two frames satisfy the required relation. -/
def kept (aNew : ℝ) (b b' : Fin q.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) :=
  {p | p ∈ q.H b b' ∧ q.Alignment aNew b b'}

/-- A row is bad if it has a witness whose frame fails the required relation. -/
def badRow (aNew : ℝ) (b : Fin q.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)) :=
  {p | ∃ b', p ∈ q.H b b' ∧ ¬q.Alignment aNew b b'}

noncomputable def pairMass
    (H : Fin q.C → Fin q.C → Set ((ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))) : ENNReal :=
  ∑ b, ENNReal.ofReal (ωk (q.γ b) * (2 : ℝ) ^ q.T) *
    ((νk (q.γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ H b b'}

noncomputable def badMass (aNew : ℝ) : ENNReal :=
  ∑ b, ENNReal.ofReal (ωk (q.γ b) * (2 : ℝ) ^ q.T) *
    ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow aNew b)

theorem measurableSet_kept (aNew : ℝ) (b b' : Fin q.C) :
    MeasurableSet (q.kept aNew b b') := by
  classical
  by_cases hA : q.Alignment aNew b b'
  · simpa [kept, hA] using (q.pairs b b').1
  · simp only [kept, hA, and_false, Set.ofPred_false, MeasurableSet.empty]

theorem measurableSet_badRow (aNew : ℝ) (b : Fin q.C) :
    MeasurableSet (q.badRow aNew b) := by
  classical
  have heq : q.badRow aNew b = ⋃ b',
      {p | p ∈ q.H b b' ∧ ¬q.Alignment aNew b b'} := by
    ext p
    simp only [badRow, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro b'
  by_cases hA : q.Alignment aNew b b'
  · simp only [hA, not_true_eq_false, and_false, Set.ofPred_false, MeasurableSet.empty]
  · simpa [hA] using (q.pairs b b').1

/-- The unchanged row law is bounded by its retained part plus its bad part. -/
theorem pairMass_le_kept_add_bad (aNew : ℝ) :
    q.pairMass q.H ≤ q.pairMass (q.kept aNew) + q.badMass aNew := by
  classical
  have hrow (b : Fin q.C) :
      {p | ∃ b', p ∈ q.H b b'} ⊆
        {p | ∃ b', p ∈ q.kept aNew b b'} ∪ q.badRow aNew b := by
    rintro p ⟨b', hp⟩
    by_cases hA : q.Alignment aNew b b'
    · exact Or.inl ⟨b', hp, hA⟩
    · exact Or.inr ⟨b', hp, hA⟩
  calc
    q.pairMass q.H ≤ ∑ b, ENNReal.ofReal (ωk (q.γ b) * (2 : ℝ) ^ q.T) *
        (((νk (q.γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ q.kept aNew b b'} +
          ((νk (q.γ b)).prod (volume.prod volume)) (q.badRow aNew b)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul' le_rfl ((measure_mono (hrow b)).trans (measure_union_le _ _))
    _ = q.pairMass (q.kept aNew) + q.badMass aNew := by
      simp only [pairMass, badMass, mul_add, Finset.sum_add_distrib]

/-- Half of the original coverage remains after paying the bad-row budget. -/
theorem kept_coverage
    (q : NativeSample aligned 8 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)
    (aNew : ℝ) (hbad : q.badMass aNew ≤ ENNReal.ofReal (4 * q.κ⁻¹)) :
    ENNReal.ofReal (4 * q.κ⁻¹) ≤ q.pairMass (q.kept aNew) := by
  have hsplit := q.pairMass_le_kept_add_bad aNew
  have htotal : ENNReal.ofReal (8 * q.κ⁻¹) ≤
      q.pairMass (q.kept aNew) + ENNReal.ofReal (4 * q.κ⁻¹) :=
    q.coverage.trans (hsplit.trans (add_le_add le_rfl hbad))
  have hnonneg : 0 ≤ 4 * q.κ⁻¹ := mul_nonneg (by norm_num)
    (inv_nonneg.mpr (le_trans zero_le_one q.κ_one))
  have heq : ENNReal.ofReal (8 * q.κ⁻¹) =
      ENNReal.ofReal (4 * q.κ⁻¹) + ENNReal.ofReal (4 * q.κ⁻¹) := by
    rw [← ENNReal.ofReal_add hnonneg hnonneg]
    congr 1
    ring
  rw [heq] at htotal
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htotal

/-- Change only the pair masks and analytic loss. All original chart data survive. -/
noncomputable def prune
    (q : NativeSample aligned 8 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)
    (aNew : ℝ) (hN : 1 ≤ Nk) (ha : a ≤ aNew) (hB : ∀ γ₀, 0 ≤ Bk γ₀)
    (hbad : q.badMass aNew ≤ ENNReal.ofReal (4 * q.κ⁻¹)) :
    NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S aNew e u h M D depths ε where
  κ := q.κ
  κ_one := q.κ_one
  κ_le := q.κ_le
  T := q.T
  s := q.s
  C := q.C
  R₁ := q.R₁
  R₂ := q.R₂
  γ := q.γ
  j := q.j
  c := q.c
  v₀ := q.v₀
  Q := q.Q
  R := q.R
  A := q.A
  F := q.F
  lst := q.lst
  H := q.kept aNew
  Good := q.Good
  hT := q.hT
  hC := q.hC
  scale_lo := q.scale_lo
  scale_hi := q.scale_hi
  R₂_pos := q.R₂_pos
  R₂_le := q.R₂_le
  R₁_le := q.R₁_le
  R₂_inv := q.R₂_inv
  classes := q.classes
  disj := q.disj
  charts := q.charts
  halfopen := q.halfopen
  whole := by
    intro b l hl t ht
    obtain ⟨hbox, hval, hder⟩ := q.whole b l hl t ht
    refine ⟨hbox, hval.trans ?_, hder.trans ?_⟩
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN ha)
        (by dsimp [δ, Submission.Obl.k4_extremal_profile_setup.δ]; positivity)
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN ha) (hB _)
  list_card := q.list_card
  list_format := q.list_format
  good := by
    intro γ₀
    refine ⟨(q.good γ₀).1, (q.good γ₀).2.1, ?_⟩
    intro p hp
    obtain ⟨hvel, hval, hder, hpure, hang⟩ := (q.good γ₀).2.2 p hp
    refine ⟨hvel, hval, hder, ?_, hang.trans ?_⟩
    · intro r hr
      exact (hpure r hr).trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl ha)))
    · exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl ha))
  pairs := by
    intro b b'
    refine ⟨q.measurableSet_kept aNew b b', ?_⟩
    rintro p ⟨hp, hA⟩
    obtain ⟨hγ, hj, hF, hF', hG, hG', hder, _⟩ := (q.pairs b b').2 p hp
    refine ⟨hγ, hj, hF, hF', hG, hG', ?_, fun _ => hA⟩
    intro R' hR t ht
    refine le_trans ?_ (hder R' hR t ht)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg ha)) (hB _)
  coverage := q.kept_coverage aNew hbad

end NativeSample
end Submission.Obl.k4_angular_normal_pair_preparation
