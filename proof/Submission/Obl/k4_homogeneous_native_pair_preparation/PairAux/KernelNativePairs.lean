-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepNativePairs.lean. The data hypotheses are specialized to the native source facts.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelBoth
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.KernelMasks
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.CoverageDeletion

/-! Original-law native pairs, before the normal or common-frame construction. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set MvPolynomial
open scoped ENNReal BigOperators

namespace Data

/-- Native pairs with both selected incidences, both typical incidences, and
the two equations' derivative floors at both times. -/
def nativePairs (D : Data) (b b' : Fin D.C) : Set PairPoint :=
  {p | D.γ b = D.γ b' ∧ coarseIdx (D.j b) = coarseIdx (D.j b') ∧
    (p.1, p.2.1) ∈ D.Sb b ∧ (p.1, p.2.2) ∈ D.Sb b' ∧
    (p.1, p.2.1) ∈ D.Good (D.γ b) ∧ (p.1, p.2.2) ∈ D.Good (D.γ b) ∧
    D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b))| ∧
    D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))| ∧
    D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b'))| ∧
    D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b'))|}

def nativeRetained (D : Data) (b : Fin D.C) : Set PairPoint :=
  {p | ∃ b', p ∈ D.nativePairs b b'}

variable {D : Data} {E : Fin D.W → Set Incidence}

theorem Hyp.nativePairs_meas (h : D.Hyp E) (b b' : Fin D.C) :
    MeasurableSet (D.nativePairs b b') := by
  have hc (a : Fin D.C) (first : Bool) : Continuous (fun p : PairPoint =>
      |eval (x p.1 (if first then p.2.1 else p.2.2)) (pderiv (3 : Fin 4) (D.R a))|) := by
    apply Continuous.abs
    apply (pderiv (3 : Fin 4) (D.R a)).continuous_eval.comp
    apply continuous_pi
    intro i
    cases first <;> fin_cases i <;> simp [x] <;> fun_prop
  have hder (a : Fin D.C) (first : Bool) : MeasurableSet {p : PairPoint |
      D.dfl * D.B (D.γ b) ≤
        |eval (x p.1 (if first then p.2.1 else p.2.2)) (pderiv (3 : Fin 4) (D.R a))|} :=
    measurableSet_le measurable_const (hc a first).measurable
  have hs : MeasurableSet {p : PairPoint |
      (p.1, p.2.1) ∈ D.Sb b ∧ (p.1, p.2.2) ∈ D.Sb b' ∧
      (p.1, p.2.1) ∈ D.Good (D.γ b) ∧ (p.1, p.2.2) ∈ D.Good (D.γ b) ∧
      D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b))| ∧
      D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))| ∧
      D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b'))| ∧
      D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b'))|} := by
    exact ((h.Sb_meas b).preimage (measurable_fst.prodMk measurable_snd.fst)).inter
      (((h.Sb_meas b').preimage (measurable_fst.prodMk measurable_snd.snd)).inter
        (((h.Good_meas _).preimage (measurable_fst.prodMk measurable_snd.fst)).inter
          (((h.Good_meas _).preimage (measurable_fst.prodMk measurable_snd.snd)).inter
            ((hder b true).inter ((hder b false).inter
              ((hder b' true).inter (hder b' false)))))))
  by_cases hγ : D.γ b = D.γ b'
  · by_cases hj : coarseIdx (D.j b) = coarseIdx (D.j b')
    · simpa only [nativePairs, hγ, hj, true_and] using hs
    · simp only [nativePairs, hj, false_and, and_false, ofPred_false, MeasurableSet.empty]
  · simp only [nativePairs, hγ, false_and, ofPred_false, MeasurableSet.empty]

theorem Hyp.nativeRetained_meas (h : D.Hyp E) (b : Fin D.C) :
    MeasurableSet (D.nativeRetained b) := by
  simpa only [nativeRetained, ofPred_exists, ofPred_mem_eq] using
    MeasurableSet.iUnion (fun b' => h.nativePairs_meas b b')

/-- The old own-time floor dominates the chosen deletion threshold. -/
theorem Hyp.native_own_floor (h : D.Hyp E)
    (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) (b : Fin D.C) {p : Incidence}
    (hp : p ∈ D.Sb b) :
    D.dfl * D.B (D.γ b) ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) (D.R b))| := by
  have hK : 0 < D.κ₀ := zero_lt_one.trans_le h.κ₀one
  have hdfl : D.dfl ≤ 1 / D.κ₀ := hdflK.trans (half_le_self (by positivity))
  calc
    _ ≤ (1 / D.κ₀) * D.B (D.γ b) :=
      mul_le_mul_of_nonneg_right hdfl (h.Bpos _).le
    _ = D.B (D.γ b) / D.κ₀ := by ring
    _ ≤ _ := (h.sel b hp.1).2.2.2

theorem Hyp.native_pairs_of_floors (h : D.Hyp E)
    (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) (b b' : Fin D.C) {p : PairPoint}
    (hγ : D.γ b' = D.γ b) (hj : coarseIdx (D.j b') = coarseIdx (D.j b))
    (hp : (p.1, p.2.1) ∈ D.Sb b) (hp' : (p.1, p.2.2) ∈ D.Sb b')
    (hGood : (p.1, p.2.1) ∈ D.Good (D.γ b))
    (hGood' : (p.1, p.2.2) ∈ D.Good (D.γ b))
    (hown : D.dfl * D.B (D.γ b) ≤
      |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))|)
    (hwit : D.dfl * D.B (D.γ b) ≤
      |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b'))|) :
    p ∈ D.nativePairs b b' := by
  have hfirst := h.native_own_floor hdflK b (p := (p.1, p.2.1)) hp
  have hsecond := h.native_own_floor hdflK b' (p := (p.1, p.2.2)) hp'
  refine ⟨hγ.symm, hj.symm, hp, hp', hGood, hGood',
    hfirst, hown, hwit, ?_⟩
  simpa only [hγ] using hsecond

/-- Every raw pair survives or is charged to an actual one-time or cross-time
failure, apart from the null closed-block endpoint. -/
theorem Hyp.native_raw_cover (h : D.Hyp E)
    (hdflK : D.dfl ≤ (1 / D.κ₀) / 2) (b : Fin D.C) {p : PairPoint}
    (hp : p ∈ D.coverageRawPairs b) :
    p ∈ D.nativeRetained b ∨
      (p.1, p.2.1) ∈ E (D.γ b) \ D.Good (D.γ b) ∨
      (p.1, p.2.2) ∈ E (D.γ b) \ D.Good (D.γ b) ∨
      p ∈ D.coverageCrossDerivativeBad b ∨ p ∈ D.coverageEndpointBad b := by
  classical
  obtain ⟨b', hγ, hp'⟩ := hp.2.2
  by_cases hGood : (p.1, p.2.1) ∈ D.Good (D.γ b)
  · by_cases hGood' : (p.1, p.2.2) ∈ D.Good (D.γ b)
    · by_cases hend : p.2.2 = ((((coarseIdx (D.j b) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ D.T)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, hend⟩)))
      · have hj := h.coverage_witness_coarse b b' (p := (p.1, p.2.2)) hp' hp.2.1
          (lt_of_le_of_ne hp.2.1.2 hend)
        by_cases hown : |eval (x p.1 p.2.2) (pderiv (3 : Fin 4) (D.R b))| <
            D.dfl * D.B (D.γ b)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hp, hown⟩))))
        · by_cases hwit : |eval (x p.1 p.2.1) (pderiv (3 : Fin 4) (D.R b'))| <
              D.dfl * D.B (D.γ b)
          · right; right; right; left; right
            refine ⟨hp, b', Prod.ext hγ hj, ?_, hp', ?_⟩
            · rw [hj]
              exact Ico_subset_Icc_self (h.coverage_Sb_coarse b hp.1)
            · simpa only [hγ] using hwit
          · left
            exact ⟨b', h.native_pairs_of_floors hdflK b b' (p := p) hγ hj hp.1 hp'
              hGood hGood' (le_of_not_gt hown) (le_of_not_gt hwit)⟩
    · right; right; left
      refine ⟨?_, hGood'⟩
      simpa only [hγ] using (h.sel b' hp'.1).1
  · exact Or.inr (Or.inl ⟨(h.sel b hp.1.1).1, hGood⟩)

/-- Native masks retain `8/kappa` before any normal-angle deletion or common
frame construction, assuming the explicit original-law exception budgets. -/
theorem Hyp.native_coverage_of_budgets (h : D.Hyp E)
    (ν : Fin D.W → Measure Trajectory) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin D.W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (hEmeas : ∀ w, MeasurableSet (E w))
    (hEunit : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {m e κ : ℝ} (hm : 0 < m) (he : 0 ≤ e) (hκ : 0 < κ)
    (hdfl : 0 ≤ D.dfl) (hdflK : D.dfl ≤ (1 / D.κ₀) / 2)
    (hmass : ENNReal.ofReal m ≤ ∑ b, ENNReal.ofReal (ω (D.γ b)) *
      ((ν (D.γ b)).prod volume) (D.F b))
    (hQmass : (∑ w, ENNReal.ofReal (ω w) *
      ((ν w).prod volume) (E w \ D.Good w)) ≤ ENNReal.ofReal e)
    (hbudget : 2 * e + 8 * D.dfl * D.κ₀ ≤ m ^ 2 / 2)
    (hκmass : 16 ≤ κ * m ^ 2) :
    ENNReal.ofReal (8 * κ⁻¹) ≤ ∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) {p | ∃ b', p ∈ D.nativePairs b b'} := by
  classical
  let Del (b : Fin D.C) := D.coverageCrossDerivativeBad b ∪ D.coverageEndpointBad b
  have hDelmass : (∑ b, ENNReal.ofReal (ω (D.γ b) * (2 : ℝ) ^ D.T) *
      ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageRawPairs b ∩ Del b)) ≤
      ENNReal.ofReal (8 * D.dfl * D.κ₀) := by
    apply le_trans ?_ (h.coverage_cross_derivative_budget ν ω hω hωsum hEunit hdfl hdflK)
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul' le_rfl
    calc
      _ ≤ ((ν (D.γ b)).prod (volume.prod volume)) (Del b) := measure_mono inter_subset_right
      _ ≤ ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageCrossDerivativeBad b) +
          ((ν (D.γ b)).prod (volume.prod volume)) (D.coverageEndpointBad b) := measure_union_le _ _
      _ = _ := by rw [D.coverageEndpointBad_null, add_zero]
  have hmassSb : ENNReal.ofReal m ≤ ∑ b, ENNReal.ofReal (ω (D.γ b)) *
      ((ν (D.γ b)).prod volume) (D.Sb b) := by
    rw [h.coverage_weighted_Sb_mass ν (fun w => ENNReal.ofReal (ω w))]
    exact hmass
  have hκ₀ : 0 ≤ D.κ₀ := zero_le_one.trans h.κ₀one
  have hcov := source_pair_coverage_of_cover D.W D.T ν ω hω hωsum D.γ
    (fun b => coarseIdx (D.j b)) D.Sb h.Sb_meas
    (fun b b' hne hγ _ => h.Sb_disjoint hne hγ)
    (fun b p hp => Ico_subset_Icc_self (h.coverage_Sb_coarse b hp))
    D.selectedIncidences h.coverage_selected_meas (fun b p hp => ⟨b, rfl, hp⟩)
    (fun w => E w \ D.Good w) (fun w => (hEmeas w).diff (h.Good_meas w))
    D.nativeRetained Del hm he (by positivity) (by positivity : 0 < κ / 2) hmassSb
    (by
      intro b p hp
      rcases h.native_raw_cover hdflK b (p := p) hp with hr | hq | hq | hd | ht
      · exact Or.inl hr
      · exact Or.inr ⟨hp, Or.inl (Or.inl hq)⟩
      · exact Or.inr ⟨hp, Or.inl (Or.inr hq)⟩
      · exact Or.inr ⟨hp, Or.inr (Or.inl hd)⟩
      · exact Or.inr ⟨hp, Or.inr (Or.inr ht)⟩)
    hQmass hDelmass hbudget (by nlinarith only [hκmass])
  have hnum : (4 : ℝ) * (κ / 2)⁻¹ = 8 * κ⁻¹ := by
    rw [inv_div]
    ring
  rw [hnum] at hcov
  exact hcov

end Data
end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
