import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankDefs

/-!
# Bookkeeping for the per-plank comparison data
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial
open Submission.Lib.K4FinitePlankAtlases

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)
include ha

/-- Measurability of the full prior sets of every layer. -/
private theorem prior_meas' : MeasurableSet ((a.ls k ℓ).prior i) := by
  obtain ⟨-, -, hcd, -, -⟩ := ha.layer k ℓ
  obtain ⟨-, -, hmeas, -⟩ := hcd
  exact (hmeas i).1

private theorem rK_pos' : 0 < a.rK k :=
  lt_of_lt_of_le one_pos (ha.tangent_input.2.2.1.1 k)

private theorem fitSet_measurable' (m : Fin (a.ncand π k ℓ i)) :
    MeasurableSet (a.fitSet π k ℓ i m) :=
  (prior_meas' ha k ℓ i).inter (Fit_closed _ _ _ _).measurableSet

theorem cvd_subset_plank (m : Fin (a.ncand π k ℓ i)) : a.cvd π k ℓ i m ⊆ a.plank k ℓ i := by
  rintro p ⟨hl, ht⟩
  exact ⟨hl.1.1, ht⟩

theorem cvd_disjoint :
    Pairwise (fun m m' => Disjoint (a.cvd π k ℓ i m) (a.cvd π k ℓ i m')) := by
  intro m m' hmm'
  exact Set.disjoint_prod.mpr (Or.inl (firstAssignment_disjoint (a.fitSet π k ℓ i) hmm'))

theorem cvd_measurable (m : Fin (a.ncand π k ℓ i)) : MeasurableSet (a.cvd π k ℓ i m) :=
  (measurableSet_firstAssignment (a.fitSet π k ℓ i)
    (fitSet_measurable' ha π k ℓ i) m).prod measurableSet_Icc

theorem iUnion_cvd : (⋃ m, a.cvd π k ℓ i m) = a.cov π.θ π.σ k ℓ i := by
  have hU : (⋃ m, a.asg π k ℓ i m) = ⋃ m, a.fitSet π k ℓ i m :=
    iUnion_firstAssignment (a.fitSet π k ℓ i)
  ext p
  simp only [mem_iUnion, cov, cvd]
  constructor
  · rintro ⟨m, hl, ht⟩
    refine ⟨a.cand π k ℓ i m, ?_, ?_⟩
    · exact List.get_mem _ _
    · exact ⟨hl.1, ht⟩
  · rintro ⟨P, hP, hp⟩
    obtain ⟨m, rfl⟩ := List.mem_iff_get.1 hP
    have hmem : p.1 ∈ ⋃ m, a.asg π k ℓ i m := by
      rw [hU]
      exact mem_iUnion.2 ⟨m, hp.1⟩
    obtain ⟨m', hm'⟩ := mem_iUnion.1 hmem
    exact ⟨m', hm', hp.2⟩

theorem cand_admissible (m : Fin (a.ncand π k ℓ i)) :
    a.Admissible π.σ k (a.cand π k ℓ i m) :=
  (greedy_entry ha π.θ π.σ k ℓ i m).1

theorem thr_pos_of_ncand (m : Fin (a.ncand π k ℓ i)) : 0 < a.thr π.θ π.σ k ℓ i :=
  (greedy_entry ha π.θ π.σ k ℓ i m).2.1

/-- The covered incidences of a candidate are its candidate set minus all earlier ones. -/
private theorem cvd_eq_diff (m : Fin (a.ncand π k ℓ i)) :
    a.cvd π k ℓ i m =
      a.candSet π.θ π.σ k ℓ i ((a.greedy π.θ π.σ k ℓ i).get m) \
        ⋃ P ∈ (a.greedy π.θ π.σ k ℓ i).take m.val, a.candSet π.θ π.σ k ℓ i P := by
  have hfa := firstAssignment_get
    (fun P => (a.ls k ℓ).prior i ∩
      Fit P (a.tStart k ℓ i) (a.tEnd k ℓ i) (a.fitTol π.θ π.σ k))
    (a.greedy π.θ π.σ k ℓ i) m
  have hasg : a.asg π k ℓ i m =
      ((a.ls k ℓ).prior i ∩ Fit ((a.greedy π.θ π.σ k ℓ i).get m)
          (a.tStart k ℓ i) (a.tEnd k ℓ i) (a.fitTol π.θ π.σ k)) \
        ⋃ P ∈ (a.greedy π.θ π.σ k ℓ i).take m.val,
          ((a.ls k ℓ).prior i ∩ Fit P (a.tStart k ℓ i) (a.tEnd k ℓ i) (a.fitTol π.θ π.σ k)) :=
    hfa
  unfold cvd
  rw [hasg]
  ext p
  constructor
  · rintro ⟨⟨hA, hB⟩, hI⟩
    refine ⟨⟨hA, hI⟩, ?_⟩
    intro hU
    obtain ⟨P, hP, hPp⟩ := mem_iUnion₂.1 hU
    exact hB (mem_iUnion₂.2 ⟨P, hP, hPp.1⟩)
  · rintro ⟨⟨hA, hI⟩, hB⟩
    refine ⟨⟨hA, ?_⟩, hI⟩
    intro hU
    obtain ⟨P, hP, hPp⟩ := mem_iUnion₂.1 hU
    exact hB (mem_iUnion₂.2 ⟨P, hP, ⟨hPp, hI⟩⟩)

theorem cvd_mass (m : Fin (a.ncand π k ℓ i)) :
    ENNReal.ofReal (a.thr π.θ π.σ k ℓ i) ≤ a.ρ k ((a.ls k ℓ).world i) (a.cvd π k ℓ i m) := by
  rw [cvd_eq_diff ha π k ℓ i m]
  exact (greedy_entry ha π.θ π.σ k ℓ i m).2.2

theorem ncand_mul_thr_le :
    (a.ncand π k ℓ i : ENNReal) * ENNReal.ofReal (a.thr π.θ π.σ k ℓ i) ≤
      a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i) := by
  calc (a.ncand π k ℓ i : ENNReal) * ENNReal.ofReal (a.thr π.θ π.σ k ℓ i)
        = ∑ _m : Fin (a.ncand π k ℓ i), ENNReal.ofReal (a.thr π.θ π.σ k ℓ i) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ m : Fin (a.ncand π k ℓ i), a.ρ k ((a.ls k ℓ).world i) (a.cvd π k ℓ i m) :=
          Finset.sum_le_sum fun m _ => cvd_mass ha π k ℓ i m
    _ = a.ρ k ((a.ls k ℓ).world i) (⋃ m, a.cvd π k ℓ i m) := by
          rw [measure_iUnion (cvd_disjoint ha π k ℓ i) (cvd_measurable ha π k ℓ i),
            tsum_fintype]
    _ ≤ a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i) :=
          measure_mono (iUnion_subset fun m => cvd_subset_plank ha π k ℓ i m)

theorem asg_fit (m : Fin (a.ncand π k ℓ i)) :
    ∀ l ∈ a.asg π k ℓ i m, ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i),
      |x l t - eval ![t, y l t] (a.cand π k ℓ i m)| ≤ a.fitTol π.θ π.σ k := by
  intro l hl t ht
  exact hl.1.2 t ht

theorem asg_subset_prior (m : Fin (a.ncand π k ℓ i)) :
    a.asg π k ℓ i m ⊆ (a.ls k ℓ).prior i := by
  intro l hl
  exact hl.1.1

theorem asg_disjoint :
    Pairwise (fun m m' => Disjoint (a.asg π k ℓ i m) (a.asg π k ℓ i m')) :=
  firstAssignment_disjoint (a.fitSet π k ℓ i)

theorem asg_measurable (m : Fin (a.ncand π k ℓ i)) : MeasurableSet (a.asg π k ℓ i m) :=
  measurableSet_firstAssignment (a.fitSet π k ℓ i) (fitSet_measurable' ha π k ℓ i) m

omit ha in
private theorem y_measurable' : Measurable (fun p : Inc => y p.1 p.2) := by
  change Measurable (fun p : Inc => p.1.2 0 + p.2 * p.1.2 1)
  fun_prop

omit ha in
private theorem x_measurable' : Measurable (fun p : Inc => x p.1 p.2) := by
  change Measurable (fun p : Inc => p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4)
  fun_prop

theorem obs_measurable : Measurable (a.obs k) := by
  unfold obs
  refine Measurable.prodMk ?_ ?_
  · rw [measurable_pi_iff]
    intro e
    fin_cases e
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact measurable_snd
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact y_measurable'
  · exact Measurable.floor (x_measurable'.div_const _)

theorem recordOf_fiber_measurable (O : (Fin 2 → ℤ) × ℤ) :
    MeasurableSet (a.recordOf π k ⁻¹' {O}) := by
  have hobs := obs_measurable ha k
  have hrec : Measurable (a.recordOf π k) := by
    unfold recordOf recObs
    refine Measurable.prodMk ?_ ?_
    · rw [measurable_pi_iff]
      intro e
      exact Measurable.floor
        (((measurable_pi_apply e).comp (measurable_fst.comp hobs)).div_const _)
    · have h2 : Measurable (fun p : Inc => ((a.obs k p).2 : ℝ)) :=
        (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp (measurable_snd.comp hobs)
      exact Measurable.floor (h2.div_const _)
  exact hrec (measurableSet_singleton O)

theorem cand_totalDegree (m : Fin (a.ncand π k ℓ i)) :
    (a.cand π k ℓ i m).totalDegree ≤ 2 :=
  (cand_admissible ha π k ℓ i m).1

theorem cand_coeff (m : Fin (a.ncand π k ℓ i)) (b : Fin 2 →₀ ℕ) :
    |(a.cand π k ℓ i m).coeff b| ≤ a.tangent k ^ (π.σ.R : ℝ) :=
  (cand_admissible ha π k ℓ i m).2 b

theorem poly_totalDegree : ((a.ls k ℓ).poly i).totalDegree ≤ 2 := by
  obtain ⟨-, -, hcd, -, -⟩ := ha.layer k ℓ
  obtain ⟨-, -, -, -, -, h6, -⟩ := hcd
  exact (h6 i).2.2.2.2.2.1

theorem eval_Gzeta (m : Fin (a.ncand π k ℓ i)) (ζ : Fin 2 → ℝ) :
    eval ζ (a.Gzeta π k ℓ i m) = a.tangent k ^ π.σ.s₀ *
      (eval (a.psi k ℓ i ζ) (a.cand π k ℓ i m) - eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i)) := by
  unfold Gzeta
  rw [Normalize.eval_affSubst]
  change eval (a.psi k ℓ i ζ) _ = _
  simp only [map_mul, map_sub, eval_C]

theorem eval_Gz (m : Fin (a.ncand π k ℓ i)) (z : Fin 2 → ℝ) :
    eval z (a.Gz π k ℓ i m) = eval (fun e => 2 * z e + 1 / 2) (a.Gzeta π k ℓ i m) := by
  unfold Gz
  rw [Normalize.eval_affSubst]
  have hfun : (fun e : Fin 2 => (![![2, 0], ![0, 2]] : Fin 2 → Fin 2 → ℝ) e 0 * z 0 +
      (![![2, 0], ![0, 2]] : Fin 2 → Fin 2 → ℝ) e 1 * z 1 + (![1 / 2, 1 / 2] : Fin 2 → ℝ) e) =
      (fun e => 2 * z e + 1 / 2) := by
    funext e
    fin_cases e <;> simp
  rw [hfun]

theorem Gzeta_totalDegree (m : Fin (a.ncand π k ℓ i)) :
    (a.Gzeta π k ℓ i m).totalDegree ≤ 2 := by
  unfold Gzeta
  refine (Normalize.affSubst_totalDegree_le _ _ _).trans ?_
  rw [C_mul']
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_sub _ _).trans ?_
  exact max_le (cand_totalDegree ha π k ℓ i m) (poly_totalDegree ha k ℓ i)

theorem Gz_totalDegree (m : Fin (a.ncand π k ℓ i)) : (a.Gz π k ℓ i m).totalDegree ≤ 2 := by
  unfold Gz
  exact (Normalize.affSubst_totalDegree_le _ _ _).trans (Gzeta_totalDegree ha π k ℓ i m)

theorem eval_Fzeta (ζ : Fin 2 → ℝ) :
    eval ζ (a.Fzeta k ℓ i) = eval (a.psi k ℓ i ζ) ((a.ls k ℓ).poly i) := by
  unfold Fzeta
  rw [Normalize.eval_affSubst]
  rfl

theorem psi_zeta (u : Fin 2 → ℝ) : a.psi k ℓ i (a.zeta k ℓ i u) = u := by
  have hK : a.rK k ≠ 0 := (rK_pos' ha k).ne'
  have hT : (2 : ℝ) ^ (a.ls k ℓ).T ≠ 0 := by positivity
  funext e
  fin_cases e
  · simp only [psi, psiA, psib, zeta, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · simp only [psi, psiA, psib, zeta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring

theorem zeta_psi (ζ : Fin 2 → ℝ) : a.zeta k ℓ i (a.psi k ℓ i ζ) = ζ := by
  have hK : a.rK k ≠ 0 := (rK_pos' ha k).ne'
  have hT : (2 : ℝ) ^ (a.ls k ℓ).T ≠ 0 := by positivity
  funext e
  fin_cases e
  · simp only [psi, psiA, psib, zeta, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring
  · simp only [psi, psiA, psib, zeta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring

/-- The plank's lines (with the tangent-input slack `K/2^T`) lie in `[1/3,2/3] × [1/4,3/4]`. -/
theorem zeta_mem_of_fit (l : Line) (t : ℝ) (ht : t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i))
    (hy : |y l t - (a.ls k ℓ).u i - t * (a.ls k ℓ).v i| ≤ a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T) :
    a.zeta k ℓ i ![t, y l t] 0 ∈ Set.Icc (1 / 3 : ℝ) (2 / 3) ∧
      a.zeta k ℓ i ![t, y l t] 1 ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  have hK : 0 < a.rK k := rK_pos' ha k
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  obtain ⟨ht0, ht1⟩ := ht
  simp only [zeta, tStart, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  -- time coordinate
  have h0 : 0 ≤ (2 : ℝ) ^ (a.ls k ℓ).T * (t - (((a.ls k ℓ).time i : ℕ) : ℝ) /
      (2 : ℝ) ^ (a.ls k ℓ).T) := by
    apply mul_nonneg hT.le
    linarith
  have h1 : (2 : ℝ) ^ (a.ls k ℓ).T * (t - (((a.ls k ℓ).time i : ℕ) : ℝ) /
      (2 : ℝ) ^ (a.ls k ℓ).T) ≤ 1 := by
    have hle : t - (((a.ls k ℓ).time i : ℕ) : ℝ) / (2 : ℝ) ^ (a.ls k ℓ).T ≤
        1 / (2 : ℝ) ^ (a.ls k ℓ).T := by
      have : ((((a.ls k ℓ).time i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (a.ls k ℓ).T =
          (((a.ls k ℓ).time i : ℕ) : ℝ) / (2 : ℝ) ^ (a.ls k ℓ).T +
            1 / (2 : ℝ) ^ (a.ls k ℓ).T := by ring
      linarith
    calc (2 : ℝ) ^ (a.ls k ℓ).T * (t - (((a.ls k ℓ).time i : ℕ) : ℝ) /
          (2 : ℝ) ^ (a.ls k ℓ).T) ≤ (2 : ℝ) ^ (a.ls k ℓ).T * (1 / (2 : ℝ) ^ (a.ls k ℓ).T) :=
          mul_le_mul_of_nonneg_left hle hT.le
      _ = 1 := by field_simp
  -- spatial coordinate
  have habs := abs_le.1 hy
  have hw : |(2 : ℝ) ^ (a.ls k ℓ).T * (y l t - (a.ls k ℓ).u i - t * (a.ls k ℓ).v i) /
      a.rK k| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos hK, div_le_one hK]
    calc (2 : ℝ) ^ (a.ls k ℓ).T * |y l t - (a.ls k ℓ).u i - t * (a.ls k ℓ).v i|
        ≤ (2 : ℝ) ^ (a.ls k ℓ).T * (a.rK k / (2 : ℝ) ^ (a.ls k ℓ).T) :=
          mul_le_mul_of_nonneg_left hy hT.le
      _ = a.rK k := by field_simp
  have hw' := abs_le.1 hw
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith
  · linarith
  · linarith [hw'.1]
  · linarith [hw'.2]

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
