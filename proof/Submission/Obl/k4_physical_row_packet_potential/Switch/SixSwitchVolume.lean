-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SixSwitchVolume.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Large skew of a polynomial field forces small volume of the
six-leg switch parameters whose endpoints land in height windows over
finitely many base boxes.

Combines `Submission.Lib.K4CubicTests.exists_large_twoBasisEndpointMinor_coeff`
(skew -> large endpoint-minor coefficient) with polynomial norming
(`Submission.Lib.K4PolynomialNorming.finite_dimensional_real_polynomial_norming`)
and the six-parameter endpoint cell bound of this directory. This is the
three-dimensional analogue of the scalar
`exists_switching_endpoint_volume_constant` (`Submission.Lib.K4ScalarSwitching`).
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.SixEndpointVolume
import Submission.Lib.K4PolynomialNorming.GeneralPolynomialNorming

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial Matrix
open Submission.Lib.K4CubicTests

theorem switchedBasePrefix_totalDegree_le {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) (a : σ) :
    (switchedBasePrefix c v k a).totalDegree ≤ 1 := by
  classical
  unfold switchedBasePrefix
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  apply totalDegree_finsetSum_le
  intro l _
  split_ifs
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

theorem switchedLegIntegrand_totalDegree_le {σ κ : Type*} [Fintype σ] [Fintype κ]
    [LinearOrder κ] (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ)
    (D : ℕ) (hT : ∀ a, (T a).totalDegree ≤ D) :
    (switchedLegIntegrand T c v k).totalDegree ≤ D := by
  unfold switchedLegIntegrand
  apply totalDegree_finsetSum_le
  intro a _
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_C, zero_add]
  exact (Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le (T a) _
    (fun b => switchedBasePrefix_totalDegree_le c v k b)).trans (hT a)

theorem twoBasisEndpointHeight_totalDegree_le (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (c : Fin 3 → ℝ) (A B : Matrix (Fin 3) (Fin 3) ℝ) (D : ℕ)
    (hT : ∀ a, (T a).totalDegree ≤ D) :
    (twoBasisEndpointHeight T c A B).totalDegree ≤ D + 1 :=
  polynomialEndpointIntegral_totalDegree_le _ D
    (fun k => switchedLegIntegrand_totalDegree_le T c _ k D hT)

theorem endpointMinorPolynomial_totalDegree_le (H : MvPolynomial (Fin 6) ℝ)
    (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) :
    (endpointMinorPolynomial H A Ai B selI selJ j).totalDegree ≤ H.totalDegree := by
  classical
  have hp (q : Fin 6) : (pderiv q H).totalDegree ≤ H.totalDegree :=
    (Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le H q).trans (Nat.sub_le _ _)
  unfold endpointMinorPolynomial endpointKernelPolynomial
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans (max_le (hp _) ?_)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa using hp _)

/-- The five-coordinate box over a base box, with the two unselected
last-block durations in `[-1, 1]`. -/
def baseBox5 (lo hi : Fin 3 → ℝ) : Set (Fin 5 → ℝ) :=
  Icc (fun k => if h : k.val < 3 then lo ⟨k, h⟩ else -1)
    (fun k => if h : k.val < 3 then hi ⟨k, h⟩ else 1)

theorem volume_baseBox5 (lo hi : Fin 3 → ℝ) :
    volume (baseBox5 lo hi) = (∏ a, ENNReal.ofReal (hi a - lo a)) * 4 := by
  rw [baseBox5, Real.volume_Icc_pi, Fin.prod_univ_five, Fin.prod_univ_three]
  have h2 : ENNReal.ofReal (1 - -1) = 2 := by norm_num
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl, lt_irrefl, dite_false,
    show ¬ (4 < 3) from by norm_num, show (0 < 3) from by norm_num,
    show (1 < 3) from by norm_num, show (2 < 3) from by norm_num, dite_true, h2]
  rw [show (4 : ENNReal) = 2 * 2 by norm_num]
  ring_nf
  rfl

/-- Coordinates of the sheared vector after removing a last-block duration:
the first three are the base endpoint. -/
theorem removeNth_shear_lt (A B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) (δ : Fin 6 → ℝ)
    (k : Fin 5) (hk : k.val < 3) :
    Fin.removeNth (α := fun _ => ℝ) (selJ j) (sixShearMatrix A B *ᵥ δ) k =
      (A *ᵥ (fun a => δ (selI a)) + B *ᵥ (fun a => δ (selJ a))) ⟨k, hk⟩ := by
  rw [Fin.removeNth_apply]
  have hs : (selJ j).succAbove k = selI ⟨k, hk⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change (k : ℕ) < 3 + (j : ℕ)
      omega
  rw [hs, sixShearMatrix_mulVec_selI]
  rfl

theorem removeNth_shear_ge (A B : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) (δ : Fin 6 → ℝ)
    (k : Fin 5) (hk : 3 ≤ k.val) :
    ∃ j' : Fin 3, Fin.removeNth (α := fun _ => ℝ) (selJ j) (sixShearMatrix A B *ᵥ δ) k =
      δ (selJ j') := by
  rw [Fin.removeNth_apply]
  obtain ⟨q, hq⟩ : ∃ q, (selJ j).succAbove k = q := ⟨_, rfl⟩
  have hval : 3 ≤ q.val := by
    rw [← hq]
    by_cases h : Fin.castSucc k < selJ j
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      exact hk
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
      simp only [Fin.val_succ]
      omega
  have hlt : q.val - 3 < 3 := by omega
  refine ⟨⟨q.val - 3, hlt⟩, ?_⟩
  have he : q = selJ ⟨q.val - 3, hlt⟩ := Fin.ext (by simp only [selJ, Fin.val_mk]; omega)
  rw [hq]
  exact (congrArg (fun r => (sixShearMatrix A B *ᵥ δ) r) he).trans
    (sixShearMatrix_mulVec_selJ A B δ _)

/-- High skew at the start makes the six-leg switch parameters, whose
endpoints fall in height windows over finitely many base boxes, small in
volume: a polynomial sublevel set is discarded and the regular part pays the
full base volume times the height width. -/
theorem six_switch_volume_of_large_skew (D : ℕ) : ∃ cNorm : ℕ,
    ∀ (T : Fin 3 → MvPolynomial (Fin 3) ℝ), (∀ a, (T a).totalDegree ≤ D) →
    ∀ (c : Fin 3 → ℝ) (A B Ai Bi : Matrix (Fin 3) (Fin 3) ℝ),
      A * Ai = 1 → B * Bi = 1 →
    ∀ (Ua Ub d η : ℝ), 0 ≤ Ua → 0 ≤ Ub → 0 < d → 0 < η →
      (∀ i j, |Ai i j| ≤ Ua) → (∀ i j, |Bi i j| ≤ Ub) → d ≤ |A.det| →
      (∃ i j, 2 * ((3 : ℕ) : ℝ) ^ 2 * Ua * Ub * η <
        |eval c (pderiv j (T i)) - eval c (pderiv i (T j))|) →
    ∀ (Λ ε : ℝ), 2 ≤ Λ → 0 ≤ ε →
    ∀ {ι : Type*} (S : Set (Fin 6 → ℝ)) (F : Finset ι) (lo hi : ι → Fin 3 → ℝ)
      (h0 : ι → ℝ),
      MeasurableSet S → (∀ δ ∈ S, ∀ k, |δ k| ≤ 1) →
      (∀ δ ∈ S, ∃ i ∈ F,
        (∀ a, lo i a ≤ (A *ᵥ (fun k => δ (selI k)) + B *ᵥ (fun k => δ (selJ k))) a ∧
          (A *ᵥ (fun k => δ (selI k)) + B *ᵥ (fun k => δ (selJ k))) a ≤ hi i a) ∧
        |eval δ (twoBasisEndpointHeight T c A B) - h0 i| ≤ ε) →
      volume S ≤ ENNReal.ofReal Λ⁻¹ +
        ((∑ i ∈ F, ∏ a, ENNReal.ofReal (hi i a - lo i a)) * 4) *
          ENNReal.ofReal (4 * (((D + 1 : ℕ) : ℝ) + 1) * ε / (d * η / Λ ^ cNorm)) := by
  obtain ⟨cNorm, hNorm⟩ :=
    Submission.Lib.K4PolynomialNorming.finite_dimensional_real_polynomial_norming (D + 1) 6
  refine ⟨cNorm, ?_⟩
  intro T hT c A B Ai Bi hA hB Ua Ub d η hUa hUb hd hη hAi hBi hdet hskew Λ ε hΛ hε
    ι S F lo hi h0 hS hbox hcover
  let H : MvPolynomial (Fin 6) ℝ := twoBasisEndpointHeight T c A B
  have hH : H.totalDegree ≤ D + 1 := twoBasisEndpointHeight_totalDegree_le T c A B D hT
  obtain ⟨j, e, hlarge⟩ := exists_large_twoBasisEndpointMinor_coeff T c A B Ai Bi hA hB
    Ua Ub d η hUa hUb hd hη.le hAi hBi hdet hskew
  let minor : MvPolynomial (Fin 6) ℝ := endpointMinorPolynomial H A Ai B selI selJ j
  have hlarge' : d * η < |minor.coeff e| := hlarge
  have hΛpos : 0 < Λ := by linarith
  let κ : ℝ := d * η / Λ ^ cNorm
  have hκ : 0 < κ := div_pos (mul_pos hd hη) (pow_pos hΛpos _)
  have hκeq : Λ ^ cNorm * κ = d * η := by
    simp only [κ]
    field_simp
  let Bad : Set (Fin 6 → ℝ) := {δ | (∀ k, |δ k| ≤ 1) ∧ |eval δ minor| ≤ κ}
  have hBadm : MeasurableSet Bad := by
    have hb : MeasurableSet {δ : Fin 6 → ℝ | ∀ k, |δ k| ≤ 1} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun k => measurableSet_le
        (continuous_abs.measurable.comp (measurable_pi_apply k)) measurable_const)
    exact hb.inter (measurableSet_le
      (continuous_abs.measurable.comp (MvPolynomial.continuous_eval minor).measurable)
      measurable_const)
  have hBad : volume Bad ≤ ENNReal.ofReal Λ⁻¹ := by
    by_contra hn
    have hvol : ENNReal.ofReal Λ⁻¹ ≤ volume Bad := (lt_of_not_ge hn).le
    have hc := hNorm minor ((endpointMinorPolynomial_totalDegree_le H A Ai B j).trans hH)
      Bad hBadm (fun u hu => hu.1) Λ κ hΛ hκ.le hvol (fun u hu => hu.2) e
    rw [hκeq] at hc
    exact (not_lt_of_ge hc) hlarge'
  let Good : Set (Fin 6 → ℝ) := S ∩ {δ | κ ≤ |eval δ minor|}
  have hGoodm : MeasurableSet Good := hS.inter (measurableSet_le measurable_const
    (continuous_abs.measurable.comp (MvPolynomial.continuous_eval minor).measurable))
  have hGood : volume Good ≤ (∑ i ∈ F, volume (baseBox5 (lo i) (hi i))) *
      ENNReal.ofReal (4 * (((D + 1 : ℕ) : ℝ) + 1) * ε / κ) := by
    apply six_endpoint_cells_volume_le H (D + 1) hH A Ai B hA j Good F
      (fun i => baseBox5 (lo i) (hi i)) h0 hε hκ hGoodm (fun i _ => measurableSet_Icc)
    · intro δ hδ
      obtain ⟨i, hi, hbase, hheight⟩ := hcover δ hδ.1
      refine ⟨i, hi, ?_, hheight⟩
      constructor
      · intro k
        by_cases hk : k.val < 3
        · simp only [hk, dite_true]
          rw [removeNth_shear_lt A B j δ k hk]
          exact (hbase ⟨k, hk⟩).1
        · simp only [hk, dite_false]
          obtain ⟨j', hj'⟩ := removeNth_shear_ge A B j δ k (by omega)
          rw [hj']
          exact (abs_le.mp (hbox δ hδ.1 _)).1
      · intro k
        by_cases hk : k.val < 3
        · simp only [hk, dite_true]
          rw [removeNth_shear_lt A B j δ k hk]
          exact (hbase ⟨k, hk⟩).2
        · simp only [hk, dite_false]
          obtain ⟨j', hj'⟩ := removeNth_shear_ge A B j δ k (by omega)
          rw [hj']
          exact (abs_le.mp (hbox δ hδ.1 _)).2
    · intro δ hδ
      exact hδ.2
  have hcov : S ⊆ Bad ∪ Good := by
    intro δ hδ
    by_cases h : κ ≤ |eval δ minor|
    · exact Or.inr ⟨hδ, h⟩
    · exact Or.inl ⟨hbox δ hδ, (lt_of_not_ge h).le⟩
  have hsum : (∑ i ∈ F, volume (baseBox5 (lo i) (hi i))) =
      (∑ i ∈ F, ∏ a, ENNReal.ofReal (hi i a - lo i a)) * 4 := by
    simp only [volume_baseBox5, Finset.sum_mul]
  calc volume S ≤ volume (Bad ∪ Good) := measure_mono hcov
    _ ≤ volume Bad + volume Good := measure_union_le _ _
    _ ≤ _ := by
      rw [← hsum]
      exact add_le_add hBad hGood

end Submission.Obl.k4_physical_row_packet_potential.Switch
