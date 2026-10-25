import Submission.Obl.k4_scalar_candidate_original_return.Core.ListedDefs

/-!
# The new labels at one stage: identities, fits, counts and lists
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
include ha

/-- The frozen priority assignment of the generic interface is the first-fit assignment. -/
theorem assignment_eq_asg (s : ℝ) (i : Fin (a.ls k ℓ).n) (h : Fin (a.ncand π k ℓ i)) :
    TangentData.assignment (a.ls k ℓ) s (a.fitTol π.θ π.σ k) (a.ncand π k ℓ)
      (a.cand π k ℓ) i h = a.asg π k ℓ i h := by
  ext l
  simp only [TangentData.assignment, asg, Submission.Lib.K4FinitePlankAtlases.firstAssignment,
    fitSet, tStart, tEnd, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hfit, hprev⟩
    exact ⟨⟨hp, hfit⟩, fun j hj hmem => hprev j hj hmem.2⟩
  · rintro ⟨⟨hp, hfit⟩, hprev⟩
    exact ⟨hp, hfit, fun j hj hmem => hprev j hj ⟨hp, hmem⟩⟩

theorem parentOf_binOf (i : Fin (a.ls k ℓ).n) (h : Fin (a.ncand π k ℓ i)) :
    a.parentOf π k ℓ (a.binOf π k ℓ i h) = i := by
  classical
  have hmem : a.jetBin π k ℓ i h ∈ a.binsOf π k ℓ i := by
    unfold binsOf
    exact Finset.mem_image_of_mem _ (Finset.mem_univ h)
  have hx : a.binOf π k ℓ i h = a.labelEquiv π k ℓ ⟨i, ⟨a.jetBin π k ℓ i h, hmem⟩⟩ := rfl
  unfold parentOf
  rw [hx, Equiv.symm_apply_apply]

theorem binLabel_binOf (i : Fin (a.ls k ℓ).n) (h : Fin (a.ncand π k ℓ i)) :
    a.binLabel π k ℓ (a.binOf π k ℓ i h) = a.jetBin π k ℓ i h := by
  classical
  have hmem : a.jetBin π k ℓ i h ∈ a.binsOf π k ℓ i := by
    unfold binsOf
    exact Finset.mem_image_of_mem _ (Finset.mem_univ h)
  have hx : a.binOf π k ℓ i h = a.labelEquiv π k ℓ ⟨i, ⟨a.jetBin π k ℓ i h, hmem⟩⟩ := rfl
  unfold binLabel
  rw [hx, Equiv.symm_apply_apply]

theorem jetBin_repOf (j : Fin (a.nNew π k ℓ)) :
    a.jetBin π k ℓ (a.parentOf π k ℓ j) (a.repOf π k ℓ j) = a.binLabel π k ℓ j := by
  classical
  unfold repOf
  exact (Classical.choose_spec (Finset.mem_image.mp ((a.labelEquiv π k ℓ).symm j).2.2)).2

omit ha in
/-- `C * N^a ≤ N^b` when the exponent gap is at least `κ₀` and `C ≤ N^κ₀`. -/
private theorem mul_rpow_le_rpow' {N C e₁ e₂ κ₀ : ℝ} (hN : 1 ≤ N) (hgap : κ₀ ≤ e₂ - e₁)
    (hC : C ≤ N ^ κ₀) (_hC0 : 0 ≤ C) : C * N ^ e₁ ≤ N ^ e₂ := by
  have hNpos : 0 < N := by linarith
  calc C * N ^ e₁ ≤ N ^ κ₀ * N ^ e₁ :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hNpos.le _)
    _ ≤ N ^ (e₂ - e₁) * N ^ e₁ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hgap)
          (Real.rpow_nonneg hNpos.le _)
    _ = N ^ e₂ := by rw [← Real.rpow_add hNpos]; ring_nf

/-- Every line of a new label fits its representative at depth `s + εm c₀ / 4`. -/
theorem label_fit (s : ℝ) (hP : ∀ i, a.PlankHyp π k ℓ i s) (j : Fin (a.nNew π k ℓ)) :
    ∀ l ∈ {l | ∃ i h, a.binOf π k ℓ i h = j ∧ l ∈ a.asg π k ℓ i h},
      ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time (a.parentOf π k ℓ j)),
        |x l t - eval ![t, y l t] (a.Qof π k ℓ j)| ≤
          a.tangent k ^ (-s - π.εm * π.σ.c₀ / 4) := by
  rintro l ⟨i, h, hbin, hl⟩ t ht
  have hpar : a.parentOf π k ℓ j = i := by
    rw [← hbin]
    exact parentOf_binOf ha π k ℓ i h
  subst hpar
  have hjb : a.jetBin π k ℓ (a.parentOf π k ℓ j) h =
      a.jetBin π k ℓ (a.parentOf π k ℓ j) (a.repOf π k ℓ j) := by
    rw [jetBin_repOf ha π k ℓ j, ← binLabel_binOf ha π k ℓ _ h, hbin]
  have hfit := rep_fit ha π k ℓ (a.parentOf π k ℓ j) s (hP _) h (a.repOf π k ℓ j) hjb l hl t ht
  refine hfit.trans ?_
  have hPj := hP (a.parentOf π k ℓ j)
  obtain ⟨hs₀, hc₀, hθ, hθε, hε, hε1⟩ := hPj.par_pos
  have hswin := hPj.s_win.1
  have hN2 := hPj.N_ge
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hNpos : 0 < a.tangent k := by linarith
  have hlarge := hPj.N_large
  have hk0 : 0 < kap0 π := by unfold kap0; positivity
  set N := a.tangent k with hNdef
  set E : ℝ := -π.σ.s₀ - π.θ * π.σ.c₀ / 4 - π.εm * π.σ.c₀ / 4 with hE
  have h30 : (2 : ℝ) ≤ N ^ (kap0 π) := le_trans (by norm_num) hlarge
  have h200 : (200 : ℝ) ≤ N ^ (kap0 π) := le_trans (by norm_num) hlarge
  -- first term
  have hA : 2 * a.fitTol π.θ π.σ k ≤ N ^ E := by
    unfold fitTol
    apply mul_rpow_le_rpow' hN1 _ h30 (by norm_num)
    unfold kap0
    have : π.θ * π.σ.c₀ ≤ π.σ.c₀ / 32 := by nlinarith
    nlinarith
  -- second term
  have hB : 2 * (100 * a.jetStep π k * N ^ (-π.σ.s₀)) ≤ N ^ E := by
    unfold jetStep
    have hmul : 2 * (100 * N ^ (-(π.εm * π.σ.c₀)) * N ^ (-π.σ.s₀)) =
        200 * N ^ (-(π.εm * π.σ.c₀) + -π.σ.s₀) := by
      rw [Real.rpow_add hNpos]; ring
    rw [hmul]
    apply mul_rpow_le_rpow' hN1 _ h200 (by norm_num)
    unfold kap0
    nlinarith
  -- monotonicity in the depth
  have hC : N ^ E ≤ N ^ (-s - π.εm * π.σ.c₀ / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have := (abs_le.mp hswin).2
    rw [hE]
    linarith
  linarith

theorem nNew_le (s : ℝ) (hP : ∀ i, a.PlankHyp π k ℓ i s) :
    (a.nNew π k ℓ : ℝ) ≤
      ((a.ls k ℓ).n : ℝ) * (a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) := by
  classical
  have hcard : a.nNew π k ℓ = ∑ i, (a.binsOf π k ℓ i).card := by
    unfold nNew
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
  have hle : ∀ i, ((a.binsOf π k ℓ i).card : ℝ) ≤
      a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) := by
    intro i
    have h1 : (a.binsOf π k ℓ i).card ≤ a.ncand π k ℓ i := by
      unfold binsOf
      exact Finset.card_image_le.trans (by simp)
    exact (Nat.cast_le.mpr h1).trans (ncand_le ha π k ℓ i s (hP i))
  rw [hcard, Nat.cast_sum]
  calc ∑ i, ((a.binsOf π k ℓ i).card : ℝ) ≤
        ∑ _i : Fin (a.ls k ℓ).n, (a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- New lists contain at most `3^6` bins for each old listed plank. -/
theorem listsOf_card (g : Fin (a.Wk k)) (z : Base × ℤ) :
    ((a.listsOf π k ℓ g z).card : ℝ) ≤ 729 * a.H k := by
  classical
  set r := a.recObs π k z with hr
  let t : (i : Fin (a.ls k ℓ).n) → Finset ↥(a.binsOf π k ℓ i) := fun i =>
    Finset.univ.filter (fun b => Nbr (a.bstarOf π k ℓ i r) b.1)
  let S : Finset (a.NewLabel π k ℓ) := ((a.ls k ℓ).lists g z).sigma t
  have hinj : (a.listsOf π k ℓ g z).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun j => (a.labelEquiv π k ℓ).symm j)
    · intro j hj
      have hj' : j ∈ a.listsOf π k ℓ g z := hj
      unfold listsOf at hj'
      rw [Finset.mem_filter] at hj'
      show (a.labelEquiv π k ℓ).symm j ∈ S
      rw [Finset.mem_sigma]
      refine ⟨hj'.2.2.1, ?_⟩
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj'.2.2.2
    · intro j₁ _ j₂ _ h
      exact (a.labelEquiv π k ℓ).symm.injective h
  have ht : ∀ i, (t i).card ≤ 729 := by
    intro i
    set b0 := a.bstarOf π k ℓ i r
    have hsub : (t i).card ≤
        (Fintype.piFinset (fun e : Fin 6 => Finset.Icc (b0 e - 1) (b0 e + 1))).card := by
      apply Finset.card_le_card_of_injOn (fun b => b.1)
      · intro b hb
        have hb' : b ∈ t i := hb
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hb'
        show b.1 ∈ Fintype.piFinset _
        rw [Fintype.mem_piFinset]
        intro e
        have h1 := abs_le.mp (hb' e)
        rw [Finset.mem_Icc]
        constructor <;> linarith [h1.1, h1.2]
      · intro b₁ _ b₂ _ h
        exact Subtype.ext h
    have hpi : (Fintype.piFinset (fun e : Fin 6 => Finset.Icc (b0 e - 1) (b0 e + 1))).card =
        729 := by
      rw [Fintype.card_piFinset]
      have h3 : ∀ e : Fin 6, (Finset.Icc (b0 e - 1) (b0 e + 1)).card = 3 := by
        intro e
        rw [Int.card_Icc]
        omega
      simp only [h3, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    omega
  have hS : (S.card : ℝ) ≤ 729 * (((a.ls k ℓ).lists g z).card : ℝ) := by
    have hcs : S.card = ∑ i ∈ (a.ls k ℓ).lists g z, (t i).card := Finset.card_sigma _ _
    rw [hcs, Nat.cast_sum]
    calc ∑ i ∈ (a.ls k ℓ).lists g z, ((t i).card : ℝ) ≤
          ∑ _i ∈ (a.ls k ℓ).lists g z, (729 : ℝ) :=
          Finset.sum_le_sum fun i _ => by exact_mod_cast ht i
      _ = 729 * (((a.ls k ℓ).lists g z).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hold : (((a.ls k ℓ).lists g z).card : ℝ) ≤ a.H k := by
    obtain ⟨-, -, hcd, -, -⟩ := ha.layer k ℓ
    have hlist := hcd.2.2.2.2.2.2.1 g z
    have hH : a.original k ^ (Real.log (a.H k) / Real.log (a.original k)) = a.H k :=
      ha.scales.original_rpow_log_factor k
    exact hlist.trans hH.le
  calc ((a.listsOf π k ℓ g z).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hinj
    _ ≤ 729 * (((a.ls k ℓ).lists g z).card : ℝ) := hS
    _ ≤ 729 * a.H k := by linarith

theorem listsOf_measurable (g : Fin (a.Wk k)) (j : Fin (a.nNew π k ℓ)) :
    MeasurableSet {z | j ∈ a.listsOf π k ℓ g z} := by
  classical
  obtain ⟨-, -, hcd, -, -⟩ := ha.layer k ℓ
  have hlm := hcd.2.2.2.2.2.2.2.1 g (a.parentOf π k ℓ j)
  have hrec : Measurable (a.recObs π k) := by
    unfold recObs
    refine Measurable.prodMk ?_ ?_
    · rw [measurable_pi_iff]
      intro e
      exact Measurable.floor (((measurable_pi_apply e).comp measurable_fst).div_const _)
    · exact Measurable.floor
        (((measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp measurable_snd).div_const _)
  have hset : {z | j ∈ a.listsOf π k ℓ g z} =
      {_z : Base × ℤ | (a.ls k ℓ).world (a.parentOf π k ℓ j) = g} ∩
        ({z | a.parentOf π k ℓ j ∈ (a.ls k ℓ).lists g z} ∩
          a.recObs π k ⁻¹' {O | Nbr (a.bstarOf π k ℓ (a.parentOf π k ℓ j) O)
            (a.binLabel π k ℓ j)}) := by
    ext z
    unfold listsOf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage]
  rw [hset]
  exact (MeasurableSet.const _).inter (hlm.inter (hrec (Set.to_countable _).measurableSet))

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
