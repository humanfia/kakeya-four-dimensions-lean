import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Dense

/-!
# Normalized coefficients of good lines

On a candidate label's block, a good incidence's line has normalized Scalar coefficients bounded
by `2K`, and the ancestor fit has bounded coefficients.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Lines with bounded normalized coefficients. -/
def CoreData.goodLines (D : CoreData α) (Q : Fin D.fc.n) : Set α :=
  {l | |D.ny0 Q l| ≤ 2 * D.K ∧ |D.ny1 Q l| ≤ 2 * D.K ∧ |D.nx0 Q l| ≤ 2 * D.K ∧
    |D.nx1 Q l| ≤ 2 * D.K}

theorem measurableSet_goodLines (D : CoreData α) (H : CoreHyp D) (Q : Fin D.fc.n) :
    MeasurableSet (D.goodLines Q) := by
  unfold CoreData.goodLines
  refine (measurableSet_le (D.measurable_ny0 H.bmeas).abs measurable_const).inter
    ((measurableSet_le (D.measurable_ny1 H.bmeas).abs measurable_const).inter
    ((measurableSet_le (D.measurable_nx0 H.bmeas).abs measurable_const).inter
    (measurableSet_le (D.measurable_nx1 H.bmeas).abs measurable_const)))

theorem tQ_mem_I (D : CoreData α) (Q : Fin D.fc.n) :
    D.tQ Q ∈ D.fc.I Q ∧ D.tQ Q + D.fc.q ∈ D.fc.I Q := by
  have hq : D.fc.q = ((2 : ℝ) ^ D.fc.T)⁻¹ := rfl
  have hpos : (0 : ℝ) < 2 ^ D.fc.T := by positivity
  unfold Fam.I blk CoreData.tQ
  have e : (((D.fc.j Q : ℕ) : ℝ) + 1) / 2 ^ D.fc.T = ((D.fc.j Q : ℕ) : ℝ) / 2 ^ D.fc.T + D.fc.q := by
    rw [hq, add_div, one_div]
  rw [e]
  have hq0 : 0 < D.fc.q := by rw [hq]; positivity
  exact ⟨⟨le_rfl, by linarith⟩, ⟨by linarith, le_rfl⟩⟩

theorem I_eq_Icc (D : CoreData α) (Q : Fin D.fc.n) :
    D.fc.I Q = Icc (D.tQ Q) (D.tQ Q + D.fc.q) := by
  have hq : D.fc.q = ((2 : ℝ) ^ D.fc.T)⁻¹ := rfl
  unfold Fam.I blk CoreData.tQ
  rw [hq, add_div, one_div]

/-- Good incidences have good lines. -/
theorem good_line (D : CoreData α) (H : CoreHyp D) {Q : Fin D.fc.n} {p : α × ℝ}
    (hp0 : p ∈ D.G0) (hpQ : p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q) : p.1 ∈ D.goodLines Q := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  obtain ⟨ht0, ht1⟩ := tQ_mem_I D Q
  obtain ⟨j, hBj, hIj⟩ := hp0.2.2.2.2.1
  have hL := Lanc_eq D H hp0 hpQ ⟨hBj, hIj⟩
  -- the coarse block contains the candidate block
  have hIsub : D.fc.I Q ⊆ D.f₀.I j := by
    obtain ⟨h, hA, hI⟩ := H.nest0 Q
    have : h = j := D.f₀.label_unique H.f₀good.disj hp0.2.1
      ⟨hA (H.fcgood.BA Q hpQ.1), hI hpQ.2⟩ ⟨H.f₀good.BA j hBj, hIj⟩
    rw [← this]; exact hI
  have hval : ∀ t ∈ D.fc.I Q, |blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) (p.1, t)| ≤ D.K := by
    intro t ht
    rw [D.blockVal_eq Q (p.1, t) hqc.ne', hL, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    exact H.f₀good.fit j p.1 hBj t (hIsub ht)
  have h0 := hval _ ht0
  have h1 := hval _ ht1
  have e0 : blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) (p.1, D.tQ Q) = D.nx0 Q p.1 := by
    unfold blockVal tau; simp
  have e1 : blockVal (D.tQ Q) D.fc.q (D.nx0 Q) (D.nx1 Q) (p.1, D.tQ Q + D.fc.q) =
      D.nx0 Q p.1 + D.nx1 Q p.1 := by
    unfold blockVal tau; field_simp; ring
  rw [e0] at h0
  rw [e1] at h1
  have g1 := (H.fcgood.geom Q p.1 (H.fcgood.BA Q hpQ.1) (D.tQ Q) ht0).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CoreData.ny0 CoreData.ZQ
    rw [abs_div, abs_of_pos hqc, div_le_iff₀ hqc]
    have e : D.b p.1 0 + D.tQ Q * D.b p.1 3 - (D.fc.c Q 0 + D.tQ Q * D.fc.c Q 1) =
        x1 D.b p.1 (D.tQ Q) - D.fc.c Q 0 - D.tQ Q * D.fc.c Q 1 := by unfold x1; ring
    rw [e]; nlinarith
  · unfold CoreData.ny1
    have := hp0.1.2.2
    have := abs_nonneg (D.b p.1 0); have := abs_nonneg (D.b p.1 1); have := abs_nonneg (D.b p.1 4)
    linarith
  · linarith
  · have : |D.nx1 Q p.1| ≤ |D.nx0 Q p.1 + D.nx1 Q p.1| + |D.nx0 Q p.1| := by
      have := abs_sub (D.nx0 Q p.1 + D.nx1 Q p.1) (D.nx0 Q p.1)
      simpa using this
    linarith

/-- The constant term of the ancestor fit. -/
theorem Lanc0_bound (D : CoreData α) (H : CoreHyp D) (hs₀ : 0 ≤ D.s₀) {Q : Fin D.fc.n}
    {p : α × ℝ} (hp0 : p ∈ D.G0) (hpQ : p.1 ∈ D.fc.B Q ∧ p.2 ∈ D.fc.I Q) :
    |D.Lanc Q 0| ≤ 6 * D.K + 3 * D.K * D.Λa := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  obtain ⟨j, hBj, hIj⟩ := hp0.2.2.2.2.1
  have hL := Lanc_eq D H hp0 hpQ ⟨hBj, hIj⟩
  obtain ⟨c1, c2, c3⟩ := Lanc_coeff D H hp0 hpQ
  have hfit : |x3 D.b p.1 p.2 - (D.Lanc Q 0 + D.Lanc Q 1 * p.2 + D.Lanc Q 2 * x1 D.b p.1 p.2 +
      D.Lanc Q 3 * x2 D.b p.1 p.2)| ≤ D.K * D.a₀ := by
    have := H.f₀good.fit j p.1 hBj p.2 hIj
    unfold Fam.fitVal at this
    rw [hL]; exact this
  have hx3 := abs_x3_le_of_native D hp0.1
  have hx1 := abs_x1_le_of_native D hp0.1
  have hx2 := abs_x2_le_of_native D hp0.1
  have ht : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hp0.1.1.1], hp0.1.1.2⟩
  have ha0 : D.a₀ ≤ 1 := by
    unfold CoreData.a₀
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [H.N2]) (by linarith)
  have hK1 := H.K1
  have hΛ0 : 0 ≤ D.Λa := (abs_nonneg _).trans c1
  unfold CoreData.Λa at hΛ0 ⊢
  set Λ := 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2)
  have m1 : |D.Lanc Q 1 * p.2| ≤ Λ := by
    rw [abs_mul]; calc |D.Lanc Q 1| * |p.2| ≤ Λ * 1 := mul_le_mul c1 ht (abs_nonneg _) hΛ0
      _ = Λ := mul_one _
  have m2 : |D.Lanc Q 2 * x1 D.b p.1 p.2| ≤ Λ * D.K := by
    rw [abs_mul]; exact mul_le_mul c2 hx1 (abs_nonneg _) hΛ0
  have m3 : |D.Lanc Q 3 * x2 D.b p.1 p.2| ≤ Λ * D.K := by
    rw [abs_mul]; exact mul_le_mul c3 hx2 (abs_nonneg _) hΛ0
  have e : D.Lanc Q 0 = x3 D.b p.1 p.2 - (x3 D.b p.1 p.2 - (D.Lanc Q 0 + D.Lanc Q 1 * p.2 +
      D.Lanc Q 2 * x1 D.b p.1 p.2 + D.Lanc Q 3 * x2 D.b p.1 p.2)) -
      D.Lanc Q 1 * p.2 - D.Lanc Q 2 * x1 D.b p.1 p.2 - D.Lanc Q 3 * x2 D.b p.1 p.2 := by ring
  rw [e]
  have hKa : D.K * D.a₀ ≤ D.K := by nlinarith
  calc _ ≤ |x3 D.b p.1 p.2| + |x3 D.b p.1 p.2 - (D.Lanc Q 0 + D.Lanc Q 1 * p.2 +
        D.Lanc Q 2 * x1 D.b p.1 p.2 + D.Lanc Q 3 * x2 D.b p.1 p.2)| +
        |D.Lanc Q 1 * p.2| + |D.Lanc Q 2 * x1 D.b p.1 p.2| + |D.Lanc Q 3 * x2 D.b p.1 p.2| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 4 * D.K + D.K + Λ + Λ * D.K + Λ * D.K := by
        gcongr
        exact hfit.trans hKa
    _ ≤ 6 * D.K + 3 * D.K * Λ := by nlinarith

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
