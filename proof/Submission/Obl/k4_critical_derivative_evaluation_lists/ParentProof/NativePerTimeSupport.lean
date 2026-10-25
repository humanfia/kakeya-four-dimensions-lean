/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, NativePerTimeSupport.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeGroupSupport
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.PerTimeScalarSupport
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupSupportScales

/-! Adapted from this LOT tree, obligation o107, session x0734,
`Submission/Obl/k4_finite_narrowness_path_improvement/HorizontalGroupSupport.lean` (commit e9d85a5f34). -/

/-! Genuine scalar spacetime support of an original initial-position and
velocity group, obtained from the frozen whole fitted-label witnesses. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original witness floors bound all true labels meeting the group,
including labels whose current mass was later removed. -/
theorem AssignmentLevel.original_group_scalar_bins (h : cfg.Valid) {k : ℕ} {s r Bnd : ℝ}
    (a : cfg.AssignmentLevel k s) (floors : cfg.FullLabelMassFloors k s)
    (caps : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      cfg.μ k {y | baseGridCode (cfg.N k ^ (-r))
        ![y.2, (cfg.x k y.1 y.2) 1, (cfg.x k y.1 y.2) 2] = q ∧
        ⌊(cfg.x k y.1 y.2) 3⌋ = n} ≤ ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-r)) ^ 3))
    (hs : 0 ≤ s)
    (U : Set (α × ℝ)) (label : α × ℝ → Fin (cfg.n k s)) (p : Fin 3 → ℝ) (n : ℤ)
    (hp₀ : |p 0| ≤ cfg.K k) (hp₂ : |p 2| ≤ cfg.K k)
    (haH : cfg.N k ^ (-s) ≤ cfg.timeLength k s)
    (hδ1 : 3 * cfg.N k ^ (-r) ≤ 1)
    (hδH2 : cfg.N k ^ (-r) ≤ cfg.timeLength k s ^ 2)
    (hcover : ∀ y ∈ U, y.1 ∈ cfg.B k s (label y) ∧
      y.2 ∈ I (cfg.T k s) (cfg.j k s (label y)))
    (hhidden : ∀ y ∈ U, |(cfg.x k y.1 y.2) 3| ≤ Bnd)
    (htime : ∀ y ∈ U, ⌊y.2 / cfg.N k ^ (-s)⌋ = n)
    (hZ : ∀ y ∈ U, |(cfg.x k y.1 y.2) 1 - referenceZ p y.2| ≤ 2 * cfg.N k ^ (-s))
    (hY : ∀ y ∈ U, |(cfg.x k y.1 y.2) 2 - referenceY p y.2| ≤ 3 * cfg.N k ^ (-s)) :
    ∃ F : Finset ℤ,
      (F.card : ℝ) ≤ 347892350976 * cfg.K k * (16 * cfg.K k ^ 5) ^ 9 /
        (cfg.N k ^ (-s)) ^ cfg.d ∧
      ∀ y ∈ U, ⌊(cfg.x k y.1 y.2) 3 / cfg.N k ^ (-s)⌋ ∈ F := by
  letI := h.incidence_finite k
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hKpos : 0 < cfg.K k := by linarith
  have hH := cfg.timeLength_pos k s
  let G := 16 * cfg.K k ^ 5
  have hpow (n : ℕ) (hn : n ≤ 5) : cfg.K k ^ n ≤ cfg.K k ^ 5 := pow_le_pow_right₀ hK hn
  have hG : 3 ≤ G := by dsimp [G]; nlinarith only [one_le_pow₀ hK (n := 5)]
  have hKG : cfg.K k ≤ G := by
    have hp := hpow 1 (by norm_num)
    simp only [pow_one] at hp
    dsimp [G]
    nlinarith only [hp, pow_nonneg hK0 5]
  have hK2G : cfg.K k ^ 2 ≤ G := by
    dsimp [G]
    nlinarith only [hpow 2 (by norm_num), pow_nonneg hK0 5]
  have hK3G : cfg.K k ^ 3 ≤ G := by
    dsimp [G]
    nlinarith only [hpow 3 (by norm_num), pow_nonneg hK0 5]
  have hslopes : 8 * cfg.K k ^ 4 ≤ G := by
    dsimp [G]
    nlinarith only [hpow 4 (by norm_num), pow_nonneg hK0 5]
  have hcontact : 3 * cfg.N k ^ (-s) ≤ G * cfg.timeLength k s ^ 2 := by
    have hr := (critical_hidden_time_ratios hN1 hN hKpos h.rate_pos.le hs h.critical_rate
      a.time_lower a.time_upper).2
    change cfg.N k ^ (-s) / cfg.timeLength k s ^ 2 ≤ cfg.K k ^ 2 at hr
    have hh := (div_le_iff₀ (sq_pos_of_pos hH)).mp hr
    have h3 : 3 * cfg.K k ^ 2 ≤ G := by
      dsimp [G]
      nlinarith only [hpow 2 (by norm_num), pow_nonneg hK0 5]
    exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h3 (sq_nonneg _))
  obtain ⟨L, hL, hLfit⟩ := a.exists_affine_table h floors hs
  let point : α × ℝ → Fin 3 → ℝ := fun y => ![y.2, (cfg.x k y.1 y.2) 1, (cfg.x k y.1 y.2) 2]
  let value : α × ℝ → ℝ := fun y => (cfg.x k y.1 y.2) 3
  let block : Fin (cfg.n k s) → ℤ := fun i => ((cfg.j k s i : ℕ) : ℤ)
  have hb := (h.basic k).1
  have hpointm : Measurable point := by
    apply Measurable.of_eval
    intro e
    fin_cases e <;> dsimp [point, x] <;> fun_prop
  have hvaluem : Measurable value := by dsimp [value, x]; fun_prop
  have hmid (i : Fin (cfg.n k s)) :
      ((block i : ℝ) + 1 / 2) * cfg.timeLength k s = cfg.blockMidpoint k s i := by
    simp [block, blockMidpoint]
  have hwhole (i : Fin (cfg.n k s)) (l : α) (hl : l ∈ cfg.A k s i)
      (t : ℝ) (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
      point (l, t) ∈ horizontalTrueBox (cfg.c k s i)
        (((block i : ℝ) + 1 / 2) * cfg.timeLength k s) (cfg.timeLength k s) G := by
    have hh := a.whole_horizontal_box h i l hl t ht
    rw [hmid]
    exact ⟨hh.1, hh.2.1.trans (mul_le_mul_of_nonneg_right hK2G hH.le),
      hh.2.2.trans (mul_le_mul_of_nonneg_right hK2G (sq_nonneg _))⟩
  apply original_full_label_group_scalar_bins (cfg.μ k) U
    point value value label hpointm hvaluem (cfg.originalWitness k s) (cfg.c k s) L
    block p (cfg.timeLength k s) G (cfg.N k ^ (-s)) (cfg.N k ^ (-s)) cfg.d Bnd
    (cfg.N k ^ (-r)) (cfg.K k) n hH (cfg.timeLength_le_one k s) hG
    (Real.rpow_pos_of_pos hN _)
    haH (Real.rpow_nonneg hN.le _) le_rfl hcontact (hp₀.trans hKG) (hp₂.trans hKG)
    (Real.rpow_pos_of_pos hN _) hK0 hδH2 hδ1
  · intro i
    rw [hmid]
    exact cfg.blockMidpoint_bound k s i
  · intro i i' hne heq
    apply a.originalWitness_disjoint i i' hne
    apply Fin.ext
    dsimp [block] at heq
    exact_mod_cast heq
  · exact measurable_originalWitness h floors
  · intro i
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (a.originalWitness_floor h floors i)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < cfg.K k ^ 3) hK3G
  · intro i y hy
    exact hy.2.trans hKG
  · exact caps
  · intro i y hy
    exact hwhole i y.1 (a.fitted_subset i hy.1.1) y.2 hy.1.2
  · exact fun i => (a.coefficient_bound i 1).trans hKG
  · intro i
    have hh := a.plane_center i
    change |cfg.c k s i 3 + cfg.c k s i 0 + cfg.blockMidpoint k s i * cfg.c k s i 1| +
      |cfg.c k s i 4 - cfg.blockMidpoint k s i| ≤ cfg.K k * cfg.timeLength k s at hh
    rw [hmid]
    exact (by linarith only [hh, abs_nonneg (cfg.c k s i 4 - cfg.blockMidpoint k s i)] :
      _ ≤ cfg.K k * cfg.timeLength k s).trans (mul_le_mul_of_nonneg_right hKG hH.le)
  · intro i
    have hh := a.plane_center i
    change |cfg.c k s i 3 + cfg.c k s i 0 + cfg.blockMidpoint k s i * cfg.c k s i 1| +
      |cfg.c k s i 4 - cfg.blockMidpoint k s i| ≤ cfg.K k * cfg.timeLength k s at hh
    rw [hmid]
    exact (by linarith only [hh, abs_nonneg (cfg.c k s i 3 + cfg.c k s i 0 +
      cfg.blockMidpoint k s i * cfg.c k s i 1)] : _ ≤ cfg.K k * cfg.timeLength k s).trans
        (mul_le_mul_of_nonneg_right hKG hH.le)
  · exact fun i e => (hL i e).trans hslopes
  · exact hhidden
  · exact htime
  · exact hZ
  · exact hY
  · intro y hy
    exact hwhole (label y) y.1 (a.fitted_subset _ (hcover y hy).1) y.2 (hcover y hy).2
  · intro y hy
    exact (hLfit (label y) y.1 (hcover y hy).1 y.2 (hcover y hy).2).trans
      (mul_le_mul_of_nonneg_right hKG (Real.rpow_nonneg hN.le _))


/-- At each fixed positive true depth, every original group has at most a
subpower times a^(-d) genuine scalar bins in each a-time-bin. All caps and
whole-label floors are supplied by the exact frozen model. -/
theorem Valid.eventually_group_scalar_bins (h : cfg.Valid)
    (s η : ℝ) (hs : 0 < s) (hsU : s ≤ cfg.U) (hη : 0 < η) :
    ∀ᶠ k in Filter.atTop, ∀ (U : Set (α × ℝ))
      (label : α × ℝ → Fin (cfg.n k s)) (p : Fin 3 → ℝ) (n : ℤ) {Bnd : ℝ},
      |p 0| ≤ cfg.K k → |p 2| ≤ cfg.K k →
      (∀ y ∈ U, y.1 ∈ cfg.B k s (label y) ∧
        y.2 ∈ I (cfg.T k s) (cfg.j k s (label y))) →
      (∀ y ∈ U, |(cfg.x k y.1 y.2) 3| ≤ Bnd) →
      (∀ y ∈ U, ⌊y.2 / cfg.N k ^ (-s)⌋ = n) →
      (∀ y ∈ U, |(cfg.x k y.1 y.2) 1 - referenceZ p y.2| ≤ 2 * cfg.N k ^ (-s)) →
      (∀ y ∈ U, |(cfg.x k y.1 y.2) 2 - referenceY p y.2| ≤ 3 * cfg.N k ^ (-s)) →
      ∃ F : Finset ℤ, (F.card : ℝ) ≤ cfg.N k ^ η / (cfg.N k ^ (-s)) ^ cfg.d ∧
        ∀ y ∈ U, ⌊(cfg.x k y.1 y.2) 3 / cfg.N k ^ (-s)⌋ ∈ F := by
  obtain ⟨r, _, hinputs⟩ := h.eventually_group_support_inputs s hs hsU
  filter_upwards [hinputs, h.eventually_group_support_cost η hη] with k inputs hcost
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  intro U label p n Bnd hp₀ hp₂ hcover hhidden htime hZ hY
  obtain ⟨F, hF, htable⟩ := inputs.level.original_group_scalar_bins h inputs.floors inputs.caps hs.le
    U label p n hp₀ hp₂ inputs.scalar_time inputs.mesh_one inputs.mesh_square
    hcover hhidden htime hZ hY
  refine ⟨F, hF.trans (div_le_div_of_nonneg_right ?_ (by positivity)), htable⟩
  have hnum : 347892350976 * cfg.K k * (16 * cfg.K k ^ 5) ^ 9 ≤
      33397665693696 * cfg.K k * (16 * cfg.K k ^ 5) ^ 9 := by
    have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
    gcongr
    norm_num
  exact hnum.trans hcost

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
