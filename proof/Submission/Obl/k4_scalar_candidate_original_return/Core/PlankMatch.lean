import Submission.Obl.k4_scalar_candidate_original_return.Core.PlankRemez

/-!
# The separated-pair mass of one plank, via the accepted local matching
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set MvPolynomial

theorem baseBox_eq_pi (N r : ℝ) (hN : 0 < N) (q : Fin 2 → ℤ) :
    baseBox N r q = Set.pi Set.univ
      (fun e => Set.Ico ((q e : ℝ) * N ^ (-r)) (((q e : ℝ) + 1) * N ^ (-r))) := by
  have hδ : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  ext u
  simp only [baseBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico]
  refine forall_congr' fun e => ?_
  rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]

theorem volume_baseBox (N r : ℝ) (hN : 0 < N) (q : Fin 2 → ℤ) :
    volume (baseBox N r q) = ENNReal.ofReal (N ^ (-r) * N ^ (-r)) := by
  have hδ : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  rw [baseBox_eq_pi N r hN q, volume_pi_pi, Fin.prod_univ_two, Real.volume_Ico, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

theorem baseBox_measurable (N r : ℝ) (hN : 0 < N) (q : Fin 2 → ℤ) :
    MeasurableSet (baseBox N r q) := by
  rw [baseBox_eq_pi N r hN q]
  exact MeasurableSet.univ_pi (fun e => measurableSet_Ico)

theorem baseBox_disjoint (N r : ℝ) {q q' : Fin 2 → ℤ} (h : q ≠ q') :
    Disjoint (baseBox N r q) (baseBox N r q') := by
  rw [Set.disjoint_left]
  intro u hu hu'
  apply h
  funext e
  rw [← hu e, ← hu' e]

theorem I_mem_unit {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ I T j) : 0 ≤ t ∧ t ≤ 1 := by
  obtain ⟨h0, h1⟩ := ht
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have hj : ((j : ℕ) : ℝ) + 1 ≤ 2 ^ T := by
    have : (j : ℕ) + 1 ≤ 2 ^ T := j.isLt
    exact_mod_cast this
  constructor
  · exact le_trans (div_nonneg (Nat.cast_nonneg _) hT.le) h0
  · exact h1.trans ((div_le_one hT).2 hj)

theorem x_close_of_grouped_bin {ρ₀ : ℝ} {m₀ : ℕ} (hρ₀ : 0 < ρ₀) (hm₀ : 0 < m₀) {x₁ x₂ : ℝ}
    (h : ⌊((⌊x₁ / ρ₀⌋ : ℤ) : ℝ) / (m₀ : ℝ)⌋ = ⌊((⌊x₂ / ρ₀⌋ : ℤ) : ℝ) / (m₀ : ℝ)⌋) :
    |x₁ - x₂| ≤ ((m₀ : ℝ) + 1) * ρ₀ := by
  have hm : (0 : ℝ) < m₀ := by exact_mod_cast hm₀
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hm, div_lt_one hm] at h1
  have f1 := Int.floor_le (x₁ / ρ₀)
  have f1' := Int.lt_floor_add_one (x₁ / ρ₀)
  have f2 := Int.floor_le (x₂ / ρ₀)
  have f2' := Int.lt_floor_add_one (x₂ / ρ₀)
  have hb := abs_lt.1 h1
  have hdiv : |x₁ / ρ₀ - x₂ / ρ₀| ≤ (m₀ : ℝ) + 1 := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]
  rw [← sub_div, abs_div, abs_of_pos hρ₀, div_le_iff₀ hρ₀] at hdiv
  exact hdiv

namespace PreparedData

section CellGeometry

variable {a : PreparedData} (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)

/-- The linear part of `z ↦ psi (2 z + 1/2)`. -/
noncomputable def cellMat : Matrix (Fin 2) (Fin 2) ℝ := fun e f => 2 * a.psiA k ℓ i e f

/-- The translation part of `z ↦ psi (2 z + 1/2)`. -/
noncomputable def cellShift : Fin 2 → ℝ :=
  fun e => a.psiA k ℓ i e 0 / 2 + a.psiA k ℓ i e 1 / 2 + a.psib k ℓ i e

theorem psi_affine (z : Fin 2 → ℝ) :
    a.psi k ℓ i (fun e => 2 * z e + 1 / 2) =
      Matrix.toLin' (a.cellMat k ℓ i) z + a.cellShift k ℓ i := by
  funext e
  simp only [psi, cellMat, cellShift, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.add_apply]
  ring

theorem cellMat_det : (a.cellMat k ℓ i).det = 48 * a.rK k / ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [cellMat, psiA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue]
  have hT : (2 : ℝ) ^ (a.ls k ℓ).T ≠ 0 := by positivity
  field_simp
  ring

theorem volume_cellZ (hK : 0 < a.rK k) (hN : 0 < a.tangent k) (q : Fin 2 → ℤ) :
    volume (a.cellZ π k ℓ i q) = ENNReal.ofReal (((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (48 * a.rK k)) *
      ENNReal.ofReal (a.tangent k ^ (-π.r) * a.tangent k ^ (-π.r)) := by
  have hset : a.cellZ π k ℓ i q = (Matrix.toLin' (a.cellMat k ℓ i)) ⁻¹'
      ((fun w => w + a.cellShift k ℓ i) ⁻¹' baseBox (a.tangent k) π.r q) := by
    ext z
    simp only [cellZ, Set.mem_ofPred_eq, Set.mem_preimage, psi_affine]
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hdet : LinearMap.det (Matrix.toLin' (a.cellMat k ℓ i)) ≠ 0 := by
    rw [LinearMap.det_toLin', cellMat_det]
    positivity
  rw [hset, Measure.addHaar_preimage_linearMap volume hdet, measure_preimage_add_right,
    volume_baseBox _ _ hN, LinearMap.det_toLin', cellMat_det]
  congr 2
  rw [abs_of_pos (by positivity), inv_div]

theorem cellZ_measurable (hN : 0 < a.tangent k) (q : Fin 2 → ℤ) :
    MeasurableSet (a.cellZ π k ℓ i q) := by
  have hset : a.cellZ π k ℓ i q = (fun z => Matrix.toLin' (a.cellMat k ℓ i) z +
      a.cellShift k ℓ i) ⁻¹' baseBox (a.tangent k) π.r q := by
    ext z
    simp only [cellZ, Set.mem_ofPred_eq, Set.mem_preimage, psi_affine]
  rw [hset]
  exact (baseBox_measurable _ _ hN q).preimage
    ((Matrix.toLin' (a.cellMat k ℓ i)).continuous_of_finiteDimensional.measurable.add_const _)

theorem cellZ_disjoint {q q' : Fin 2 → ℤ} (h : q ≠ q') :
    Disjoint (a.cellZ π k ℓ i q) (a.cellZ π k ℓ i q') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.1 (baseBox_disjoint (a.tangent k) π.r h) hz hz'

end CellGeometry

end PreparedData

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid) (π : CmpParams) (k : ℕ) (ℓ : Fin (a.ct k))
  (i : Fin (a.ls k ℓ).n)
include ha

/-- The matching conclusion at `R = N^{c₀}` and exponent `εm` (from `matching_far_mass`). -/
def MatchAt (R ε d₀ : ℝ) : Prop :=
  ∀ {Q : Type} [Countable Q] (n : ℕ) (G : Fin n → MvPolynomial (Fin 2) ℝ)
    (S : Q → Set (Fin 2 → ℝ)) (w : Fin n → Fin n → Q → ℤ → ENNReal) (Λ : ℝ),
    0 ≤ Λ →
    (n : ℝ) ≤ R ^ (d₀ + ε) →
    (∀ m, (G m).totalDegree ≤ 2) →
    (∀ m, ∀ z ∈ MatchApply.sq 1, |eval z (G m)| ≤ R ^ ε) →
    (∀ q, MeasurableSet (S q)) → (∀ q, S q ⊆ MatchApply.sq (1 / 4)) →
    Pairwise (fun q q' => Disjoint (S q) (S q')) →
    (∀ q, 0 < volume (S q)) → (∀ q, volume (S q) < ⊤) →
    (∀ m m' q c, w m m' q c ≠ 0 → ∀ z ∈ S q,
        |eval z (G m) - eval z (G m')| ≤ R ^ (-1 + ε)) →
    (∀ m q, ∑' c, ∑ m', w m m' q c ≤ ENNReal.ofReal Λ * volume (S q)) →
    (∀ m' q, ∑' c, ∑ m, w m m' q c ≤ ENNReal.ofReal Λ * volume (S q)) →
    MatchApply.farMass G w (R ^ (-ε)) ≤ ENNReal.ofReal (4 * Λ * n * R ^ (-ε))

theorem base_bound (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (m : Fin (a.ncand π k ℓ i))
    (p : Inc) (hp : p ∈ a.cvd π k ℓ i m) : ∀ e, |Cells.base p e| ≤ 2 * a.rK k := by
  obtain ⟨hl, ht⟩ := hp
  have hA : p.1 ∈ (a.ls k ℓ).prior i := asg_subset_prior ha π k ℓ i m hl
  obtain ⟨hy, -⟩ := hP.fit p.1 hA p.2 ht
  obtain ⟨ht0, ht1⟩ := I_mem_unit ht
  have hK := hP.K_ge
  have huv := hP.uv_le
  have hT : (1 : ℝ) ≤ 2 ^ (a.ls k ℓ).T := one_le_pow₀ (by norm_num)
  have h1 : a.rK k / 2 ^ (a.ls k ℓ).T ≤ a.rK k := div_le_self (by linarith) hT
  intro e
  fin_cases e
  · simp only [Cells.base, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [abs_of_nonneg ht0]
    linarith
  · simp only [Cells.base, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have h2 : |p.2 * (a.ls k ℓ).v i| ≤ |(a.ls k ℓ).v i| := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    have h3 : |y p.1 p.2| ≤ |y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i| +
        |(a.ls k ℓ).u i| + |p.2 * (a.ls k ℓ).v i| := by
      have := abs_add_three (y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i)
        ((a.ls k ℓ).u i) (p.2 * (a.ls k ℓ).v i)
      have heq : y p.1 p.2 - (a.ls k ℓ).u i - p.2 * (a.ls k ℓ).v i + (a.ls k ℓ).u i +
          p.2 * (a.ls k ℓ).v i = y p.1 p.2 := by ring
      rwa [heq] at this
    linarith

omit ha in
theorem fitTol_eq : a.fitTol π.θ π.σ k = a.tangent k ^ (-π.s') := by
  unfold fitTol CmpParams.s'
  congr 1
  ring

theorem obsRes_pos : 0 < a.obsRes k :=
  Real.rpow_pos_of_pos (ha.scales.original_pos k) _

theorem tangent_pos : 0 < a.tangent k :=
  Real.rpow_pos_of_pos (ha.scales.original_pos k) _

theorem mzero_bounds (s : ℝ) (hP : a.PlankHyp π k ℓ i s) :
    0 < a.mzero π k ∧ ((a.mzero π k : ℝ) + 1) * a.obsRes k ≤ 2 * a.fitTol π.θ π.σ k := by
  have hρ := obsRes_pos ha k
  have hft : 0 < a.fitTol π.θ π.σ k := Real.rpow_pos_of_pos (tangent_pos ha k) _
  have hobs : a.obsRes k ≤ a.fitTol π.θ π.σ k / 4 := by
    rw [fitTol_eq (a := a) π k]; exact hP.obs_small
  have h4 : (4 : ℝ) ≤ a.fitTol π.θ π.σ k / a.obsRes k := by
    rw [le_div_iff₀ hρ]; linarith
  have hfl : (a.mzero π k : ℝ) ≤ a.fitTol π.θ π.σ k / a.obsRes k :=
    Nat.floor_le (by positivity)
  refine ⟨?_, ?_⟩
  · have : (4 : ℕ) ≤ a.mzero π k := Nat.le_floor (by exact_mod_cast h4)
    omega
  · have h1 : (a.mzero π k : ℝ) * a.obsRes k ≤ a.fitTol π.θ π.σ k := by
      rwa [le_div_iff₀ hρ] at hfl
    linarith

omit ha in
theorem recordOf_fst (p : Inc) : (a.recordOf π k p).1 = baseBin (a.tangent k) π.r p := rfl

omit ha in
theorem recordOf_snd (p : Inc) : (a.recordOf π k p).2 =
    ⌊((⌊x p.1 p.2 / a.obsRes k⌋ : ℤ) : ℝ) / (a.mzero π k : ℝ)⌋ := rfl

theorem x_close_of_record (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (p p' : Inc)
    (h : a.recordOf π k p = a.recordOf π k p') :
    |x p.1 p.2 - x p'.1 p'.2| ≤ 2 * a.fitTol π.θ π.σ k := by
  obtain ⟨hm0, hm1⟩ := mzero_bounds ha π k ℓ i s hP
  have h2 : (a.recordOf π k p).2 = (a.recordOf π k p').2 := by rw [h]
  rw [recordOf_snd, recordOf_snd] at h2
  exact (x_close_of_grouped_bin (obsRes_pos ha k) hm0 h2).trans hm1

omit ha in
theorem record_nonempty (m : Fin (a.ncand π k ℓ i)) (O : (Fin 2 → ℤ) × ℤ)
    (h : a.recMass π k ℓ i m O ≠ 0) :
    ∃ p ∈ a.cvd π k ℓ i m, a.recordOf π k p = O := by
  obtain ⟨p, hp, hO⟩ := nonempty_of_measure_ne_zero h
  exact ⟨p, hp, hO⟩

/-- Two covered points with the same record give close candidate values on the whole
matching cell. -/
theorem close_on_cell (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (m m' : Fin (a.ncand π k ℓ i))
    (q : Fin 2 → ℤ) (c : ℤ) (hm : a.recMass π k ℓ i m (q, c) ≠ 0)
    (hm' : a.recMass π k ℓ i m' (q, c) ≠ 0) :
    ∀ z ∈ a.cellZ π k ℓ i q, |eval z (a.Gz π k ℓ i m) - eval z (a.Gz π k ℓ i m')| ≤
      5 * a.tangent k ^ π.σ.s₀ * a.fitTol π.θ π.σ k := by
  intro z hz
  obtain ⟨p, hp, hpO⟩ := record_nonempty π k ℓ i m (q, c) hm
  obtain ⟨p', hp', hpO'⟩ := record_nonempty π k ℓ i m' (q, c) hm'
  set u := a.psi k ℓ i (fun e => 2 * z e + 1 / 2) with hu
  have hN := tangent_pos ha k
  have hK := hP.K_ge
  have hδ1 : a.tangent k ^ (-π.r) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hP.N_ge])
    have := hP.par_pos
    unfold CmpParams.r
    have : (0 : ℝ) ≤ (π.σ.R : ℝ) := Nat.cast_nonneg _
    linarith
  have hδpos : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hN _
  -- cells of p and p'
  have hqp : baseBin (a.tangent k) π.r p = q := by
    rw [← recordOf_fst]; rw [hpO]
  have hqp' : baseBin (a.tangent k) π.r p' = q := by
    rw [← recordOf_fst]; rw [hpO']
  have huq : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ = q e := hz
  -- coordinates bounds
  have hb := base_bound ha π k ℓ i s hP m p hp
  have hb' := base_bound ha π k ℓ i s hP m' p' hp'
  have hub : ∀ e, |u e| ≤ 4 * a.rK k := by
    intro e
    have hfl : ⌊u e / a.tangent k ^ (-π.r)⌋ = ⌊Cells.base p e / a.tangent k ^ (-π.r)⌋ := by
      rw [huq e, ← congrFun hqp e]
      rfl
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    rw [← sub_div, abs_div, abs_of_pos hδpos, div_lt_iff₀ hδpos] at h1
    have h2 := abs_sub_abs_le_abs_sub (u e) (Cells.base p e)
    linarith [hb e]
  have hbp4 : ∀ e, |Cells.base p e| ≤ 4 * a.rK k := fun e => by linarith [hb e]
  have hbp4' : ∀ e, |Cells.base p' e| ≤ 4 * a.rK k := fun e => by linarith [hb' e]
  have hq1 : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ = ⌊Cells.base p e / a.tangent k ^ (-π.r)⌋ := by
    intro e; rw [huq e, ← congrFun hqp e]; rfl
  have hq2 : ∀ e, ⌊u e / a.tangent k ^ (-π.r)⌋ = ⌊Cells.base p' e / a.tangent k ^ (-π.r)⌋ := by
    intro e; rw [huq e, ← congrFun hqp' e]; rfl
  have hv1 := cand_cell_variation ha π k ℓ i s hP m u (Cells.base p) hub hbp4 hq1
  have hv2 := cand_cell_variation ha π k ℓ i s hP m' u (Cells.base p') hub hbp4' hq2
  have hf1 : |x p.1 p.2 - eval (Cells.base p) (a.cand π k ℓ i m)| ≤ a.fitTol π.θ π.σ k :=
    asg_fit ha π k ℓ i m p.1 hp.1 p.2 hp.2
  have hf2 : |x p'.1 p'.2 - eval (Cells.base p') (a.cand π k ℓ i m')| ≤ a.fitTol π.θ π.σ k :=
    asg_fit ha π k ℓ i m' p'.1 hp'.1 p'.2 hp'.2
  have hxx := x_close_of_record ha π k ℓ i s hP p p' (hpO.trans hpO'.symm)
  have hft := fitTol_eq (a := a) π k
  rw [← hft] at hv1 hv2
  have hdiff : |eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')| ≤
      5 * a.fitTol π.θ π.σ k := by
    have := abs_sub_le (eval u (a.cand π k ℓ i m)) (eval (Cells.base p) (a.cand π k ℓ i m))
      (eval u (a.cand π k ℓ i m'))
    have h3 := abs_sub_le (eval (Cells.base p) (a.cand π k ℓ i m)) (x p.1 p.2)
      (eval u (a.cand π k ℓ i m'))
    have h4 := abs_sub_le (x p.1 p.2) (x p'.1 p'.2) (eval u (a.cand π k ℓ i m'))
    have h5 := abs_sub_le (x p'.1 p'.2) (eval (Cells.base p') (a.cand π k ℓ i m'))
      (eval u (a.cand π k ℓ i m'))
    rw [abs_sub_comm] at hf1
    have hv2' : |eval (Cells.base p') (a.cand π k ℓ i m') - eval u (a.cand π k ℓ i m')| ≤
        a.fitTol π.θ π.σ k / 8 := by rw [abs_sub_comm]; exact hv2
    have hft0 : 0 ≤ a.fitTol π.θ π.σ k := (Real.rpow_pos_of_pos hN _).le
    linarith
  rw [eval_Gz ha, eval_Gz ha, eval_Gzeta ha, eval_Gzeta ha, ← hu]
  have hNs : 0 ≤ a.tangent k ^ π.σ.s₀ := (Real.rpow_pos_of_pos hN _).le
  rw [show a.tangent k ^ π.σ.s₀ * (eval u (a.cand π k ℓ i m) - eval u ((a.ls k ℓ).poly i)) -
      a.tangent k ^ π.σ.s₀ * (eval u (a.cand π k ℓ i m') - eval u ((a.ls k ℓ).poly i)) =
      a.tangent k ^ π.σ.s₀ * (eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')) by ring,
    abs_mul, abs_of_nonneg hNs]
  calc a.tangent k ^ π.σ.s₀ * |eval u (a.cand π k ℓ i m) - eval u (a.cand π k ℓ i m')|
      ≤ a.tangent k ^ π.σ.s₀ * (5 * a.fitTol π.θ π.σ k) :=
        mul_le_mul_of_nonneg_left hdiff hNs
    _ = 5 * a.tangent k ^ π.σ.s₀ * a.fitTol π.θ π.σ k := by ring


theorem sum_recMass_eq (O : (Fin 2 → ℤ) × ℤ) :
    ∑ m', a.recMass π k ℓ i m' O = a.recTotal π k ℓ i O := by
  unfold recMass recTotal
  rw [Set.iUnion_inter, measure_iUnion, tsum_fintype]
  · intro m m' hmm'
    exact (cvd_disjoint ha π k ℓ i hmm').mono Set.inter_subset_left Set.inter_subset_left
  · intro m
    exact (cvd_measurable ha π k ℓ i m).inter (recordOf_fiber_measurable ha π k O)

theorem sum_pair_le (m : Fin (a.ncand π k ℓ i)) (O : (Fin 2 → ℤ) × ℤ) :
    ∑ m', a.recMass π k ℓ i m O * a.recMass π k ℓ i m' O / a.recTotal π k ℓ i O ≤
      a.recMass π k ℓ i m O := by
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_recMass_eq ha π k ℓ i O]
  calc (a.recTotal π k ℓ i O)⁻¹ * (a.recMass π k ℓ i m O * a.recTotal π k ℓ i O)
      = a.recMass π k ℓ i m O * (a.recTotal π k ℓ i O * (a.recTotal π k ℓ i O)⁻¹) := by ring
    _ ≤ a.recMass π k ℓ i m O * 1 := by gcongr; exact ENNReal.mul_inv_le_one _
    _ = a.recMass π k ℓ i m O := mul_one _

theorem tsum_recMass_le (m : Fin (a.ncand π k ℓ i)) (q : Fin 2 → ℤ) :
    ∑' c, a.recMass π k ℓ i m (q, c) ≤
      a.ρ k ((a.ls k ℓ).world i)
        (a.cvd π k ℓ i m ∩ {p | baseBin (a.tangent k) π.r p = q}) := by
  unfold recMass
  rw [← measure_iUnion]
  · apply measure_mono
    intro p hp
    obtain ⟨c, hc, hrec⟩ := Set.mem_iUnion.1 hp
    refine ⟨hc, ?_⟩
    show baseBin (a.tangent k) π.r p = q
    rw [← recordOf_fst]
    rw [show a.recordOf π k p = (q, c) from hrec]
  · intro c c' hcc'
    apply Disjoint.mono Set.inter_subset_right Set.inter_subset_right
    apply Disjoint.preimage
    rw [Set.disjoint_singleton]
    intro h
    exact hcc' (Prod.ext_iff.1 h).2
  · intro c
    exact (cvd_measurable ha π k ℓ i m).inter (recordOf_fiber_measurable ha π k (q, c))

/-- The covered mass of a candidate in one base cell. -/
theorem cvd_cell_mass (s : ℝ) (hP : a.PlankHyp π k ℓ i s) (m : Fin (a.ncand π k ℓ i))
    (q : Fin 2 → ℤ) :
    a.ρ k ((a.ls k ℓ).world i) (a.cvd π k ℓ i m ∩ {p | baseBin (a.tangent k) π.r p = q}) ≤
      ENNReal.ofReal (5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s')) := by
  have hN1 : 1 < a.tangent k := by linarith [hP.N_ge]
  have hft := fitTol_eq (a := a) π k
  have hft0 : 0 ≤ a.fitTol π.θ π.σ k := (Real.rpow_pos_of_pos (tangent_pos ha k) _).le
  refine Cells.cell_mass_le (a.ρ k ((a.ls k ℓ).world i)) hN1 hft0 hft.le hP.noncon
    (a.cand π k ℓ i m) (a.cvd π k ℓ i m) ?_ ?_ q
  · intro p hp
    exact asg_fit ha π k ℓ i m p.1 hp.1 p.2 hp.2
  · intro p hp p' hp' hpp'
    have hb := base_bound ha π k ℓ i s hP m p hp
    have hb' := base_bound ha π k ℓ i s hP m p' hp'
    have hK := hP.K_ge
    have h4 : ∀ e, |Cells.base p e| ≤ 4 * a.rK k := fun e => by linarith [hb e]
    have h4' : ∀ e, |Cells.base p' e| ≤ 4 * a.rK k := fun e => by linarith [hb' e]
    have hq : ∀ e, ⌊Cells.base p e / a.tangent k ^ (-π.r)⌋ =
        ⌊Cells.base p' e / a.tangent k ^ (-π.r)⌋ := fun e => congrFun hpp' e
    have hv := cand_cell_variation ha π k ℓ i s hP m (Cells.base p) (Cells.base p') h4 h4' hq
    have hpos : 0 ≤ a.tangent k ^ (-π.s') := (Real.rpow_pos_of_pos (tangent_pos ha k) _).le
    linarith

/-- The number of candidates of a plank. -/
theorem ncand_le (s : ℝ) (hP : a.PlankHyp π k ℓ i s) :
    (a.ncand π k ℓ i : ℝ) ≤ a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) := by
  have hN := tangent_pos ha k
  have hK : 0 < a.rK k := by linarith [hP.K_ge]
  by_cases h0 : a.ncand π k ℓ i = 0
  · rw [h0, Nat.cast_zero]
    positivity
  have hthr := thr_pos_of_ncand ha π k ℓ i ⟨0, Nat.pos_of_ne_zero h0⟩
  have hle := ncand_mul_thr_le ha π k ℓ i
  have := hP.nu_prob
  have hT : (0 : ℝ) < 2 ^ (a.ls k ℓ).T := by positivity
  have hνfin : ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i) ≠ ⊤ :=
    measure_ne_top _ _
  have hvolI : volume (I (a.ls k ℓ).T ((a.ls k ℓ).time i)) =
      ENNReal.ofReal (1 / (2 : ℝ) ^ (a.ls k ℓ).T) := by
    show volume (Set.Icc _ _) = _
    rw [Real.volume_Icc]
    congr 1
    ring
  have hplank : a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i) ≤
      ENNReal.ofReal (a.rK k * (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i)
        ((a.ls k ℓ).prior i)).toReal * (1 / (2 : ℝ) ^ (a.ls k ℓ).T)) := by
    calc a.ρ k ((a.ls k ℓ).world i) (a.plank k ℓ i)
        ≤ (ENNReal.ofReal (a.rK k) • ((ν (a.p k) (a.sm k) ((a.ls k ℓ).world i)).prod volume))
            (a.plank k ℓ i) := hP.rho_le _
      _ = ENNReal.ofReal (a.rK k) * (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i)
            ((a.ls k ℓ).prior i) * volume (I (a.ls k ℓ).T ((a.ls k ℓ).time i))) := by
          rw [Measure.smul_apply, smul_eq_mul, plank, Measure.prod_prod]
      _ = _ := by
          rw [hvolI, ← ENNReal.ofReal_toReal hνfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_mul hK.le, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mul_assoc]
  have h1 : (a.ncand π k ℓ i : ℝ) * a.thr π.θ π.σ k ℓ i ≤
      a.rK k * (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i)
        ((a.ls k ℓ).prior i)).toReal * (1 / (2 : ℝ) ^ (a.ls k ℓ).T) := by
    have := hle.trans hplank
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    exact this
  unfold thr at h1 hthr
  set νA := (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i) ((a.ls k ℓ).prior i)).toReal with hνA
  have hνpos : 0 < νA := by
    by_contra hc
    have h0' : νA = 0 := le_antisymm (not_lt.1 hc) ENNReal.toReal_nonneg
    rw [h0', mul_zero] at hthr
    exact lt_irrefl _ hthr
  set E := a.rd * π.σ.c₀ + π.θ * π.σ.c₀ with hE
  have h2 : (a.ncand π k ℓ i : ℝ) * a.tangent k ^ (-E) ≤ a.rK k := by
    have hpos : 0 < νA / 2 ^ (a.ls k ℓ).T := div_pos hνpos hT
    have hexp : -a.rd * π.σ.c₀ - π.θ * π.σ.c₀ = -E := by rw [hE]; ring
    rw [hexp] at h1
    have h3 : (a.ncand π k ℓ i : ℝ) * a.tangent k ^ (-E) * (νA / 2 ^ (a.ls k ℓ).T) ≤
        a.rK k * (νA / 2 ^ (a.ls k ℓ).T) := by
      calc (a.ncand π k ℓ i : ℝ) * a.tangent k ^ (-E) * (νA / 2 ^ (a.ls k ℓ).T)
          = (a.ncand π k ℓ i : ℝ) * (a.tangent k ^ (-E) / 2 ^ (a.ls k ℓ).T * νA) := by ring
        _ ≤ a.rK k * νA * (1 / 2 ^ (a.ls k ℓ).T) := h1
        _ = a.rK k * (νA / 2 ^ (a.ls k ℓ).T) := by ring
    exact le_of_mul_le_mul_right h3 hpos
  have h4 : a.tangent k ^ (-E) * a.tangent k ^ E = 1 := by
    rw [← Real.rpow_add hN, neg_add_cancel, Real.rpow_zero]
  calc (a.ncand π k ℓ i : ℝ) = (a.ncand π k ℓ i : ℝ) * a.tangent k ^ (-E) * a.tangent k ^ E := by
        rw [mul_assoc, h4, mul_one]
    _ ≤ a.rK k * a.tangent k ^ E :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hN _).le

/-- The separated-pair mass of a plank. -/
theorem plank_farMass_le (s : ℝ) (hP : a.PlankHyp π k ℓ i s)
    (hM : MatchAt (a.tangent k ^ π.σ.c₀) π.εm a.rd) :
    MatchApply.farMass (a.Gz π k ℓ i) (a.pairW π k ℓ i) (a.jetStep π k) ≤
      ENNReal.ofReal (1000 * a.rK k ^ 3 *
        a.tangent k ^ (-a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀) /
          (2 : ℝ) ^ (2 * (a.ls k ℓ).T)) := by
  classical
  obtain ⟨hs₀, hc₀, hθ, hθε, hε, hε1⟩ := hP.par_pos
  obtain ⟨hd0, hd1⟩ := hP.d_range
  have hN := tangent_pos ha k
  have hN1 : 1 ≤ a.tangent k := by linarith [hP.N_ge]
  have hK1 := hP.K_ge
  have hK : 0 < a.rK k := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have : Countable (a.GoodCell π k ℓ i) := by unfold GoodCell; infer_instance
  -- the common cell volume
  set v : ℝ := ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 / (48 * a.rK k) *
    (a.tangent k ^ (-π.r) * a.tangent k ^ (-π.r)) with hv
  have hNr : 0 < a.tangent k ^ (-π.r) := Real.rpow_pos_of_pos hN _
  have hvpos : 0 < v := by positivity
  have hvol : ∀ q, volume (a.cellZ π k ℓ i q) = ENNReal.ofReal v := by
    intro q
    rw [volume_cellZ π k ℓ i hK hN q, hv, ← ENNReal.ofReal_mul (by positivity)]
  set Λ : ℝ := 5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s') / v with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛv : ENNReal.ofReal Λ * ENNReal.ofReal v =
      ENNReal.ofReal (5 * a.rK k * a.tangent k ^ (-2 * π.r - a.rd * π.s')) := by
    rw [← ENNReal.ofReal_mul hΛ0, hΛ, div_mul_cancel₀ _ hvpos.ne']
  -- small exponents
  have hkap : kap0 π + π.θ * π.σ.c₀ ≤ π.εm * π.σ.c₀ := by
    unfold kap0
    nlinarith
  have hkap0 : 0 ≤ kap0 π := by unfold kap0; positivity
  have h5 : (5 : ℝ) ≤ a.tangent k ^ (kap0 π) := le_trans (by norm_num) hP.N_large
  -- the matching scale and the jet step
  have hjet : a.jetStep π k = (a.tangent k ^ π.σ.c₀) ^ (-π.εm) := by
    unfold jetStep
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [hjet]
  have hcount := ncand_le ha π k ℓ i s hP
  have hn : (a.ncand π k ℓ i : ℝ) ≤ (a.tangent k ^ π.σ.c₀) ^ (a.rd + π.εm) := by
    rw [← Real.rpow_mul hN.le]
    calc (a.ncand π k ℓ i : ℝ) ≤ a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
          hcount
      _ ≤ a.tangent k ^ (kap0 π) * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) :=
          mul_le_mul_of_nonneg_right hP.K_small (Real.rpow_pos_of_pos hN _).le
      _ = a.tangent k ^ (kap0 π + (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) :=
          (Real.rpow_add hN _ _).symm
      _ ≤ a.tangent k ^ (π.σ.c₀ * (a.rd + π.εm)) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          nlinarith
  have hbound : ∀ m, ∀ z ∈ MatchApply.sq 1,
      |eval z (a.Gz π k ℓ i m)| ≤ (a.tangent k ^ π.σ.c₀) ^ π.εm := by
    intro m z hz
    rw [← Real.rpow_mul hN.le, mul_comm π.σ.c₀]
    exact Gz_bound ha π k ℓ i s hP m z hz
  have hclose : ∀ (m m' : Fin (a.ncand π k ℓ i)) (q : a.GoodCell π k ℓ i) (c : ℤ),
      a.pairW π k ℓ i m m' q c ≠ 0 → ∀ z ∈ a.cellZ π k ℓ i q.1,
        |eval z (a.Gz π k ℓ i m) - eval z (a.Gz π k ℓ i m')| ≤
          (a.tangent k ^ π.σ.c₀) ^ (-1 + π.εm) := by
    intro m m' q c hw z hz
    have h1 : a.recMass π k ℓ i m (q.1, c) ≠ 0 := by
      intro h0
      apply hw
      unfold pairW
      rw [h0, zero_mul, ENNReal.zero_div]
    have h2 : a.recMass π k ℓ i m' (q.1, c) ≠ 0 := by
      intro h0
      apply hw
      unfold pairW
      rw [h0, mul_zero, ENNReal.zero_div]
    refine (close_on_cell ha π k ℓ i s hP m m' q.1 c h1 h2 z hz).trans ?_
    rw [fitTol_eq (a := a) π k, ← Real.rpow_mul hN.le]
    have hA : 0 ≤ a.tangent k ^ π.σ.s₀ := (Real.rpow_pos_of_pos hN _).le
    have hB : 0 ≤ a.tangent k ^ (-π.s') := (Real.rpow_pos_of_pos hN _).le
    calc 5 * a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-π.s')
        ≤ a.tangent k ^ (kap0 π) * a.tangent k ^ π.σ.s₀ * a.tangent k ^ (-π.s') := by
          gcongr
      _ = a.tangent k ^ (kap0 π + π.σ.s₀ + -π.s') := by
          rw [Real.rpow_add hN, Real.rpow_add hN]
      _ ≤ a.tangent k ^ (π.σ.c₀ * (-1 + π.εm)) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          unfold CmpParams.s'
          nlinarith
  have hmarg1 : ∀ (m : Fin (a.ncand π k ℓ i)) (q : a.GoodCell π k ℓ i),
      ∑' c, ∑ m', a.pairW π k ℓ i m m' q c ≤
        ENNReal.ofReal Λ * volume (a.cellZ π k ℓ i q.1) := by
    intro m q
    rw [hvol, hΛv]
    calc ∑' c, ∑ m', a.pairW π k ℓ i m m' q c ≤ ∑' c, a.recMass π k ℓ i m (q.1, c) :=
          ENNReal.tsum_le_tsum (fun c => sum_pair_le ha π k ℓ i m (q.1, c))
      _ ≤ _ := tsum_recMass_le ha π k ℓ i m q.1
      _ ≤ _ := cvd_cell_mass ha π k ℓ i s hP m q.1
  have hmarg2 : ∀ (m' : Fin (a.ncand π k ℓ i)) (q : a.GoodCell π k ℓ i),
      ∑' c, ∑ m, a.pairW π k ℓ i m m' q c ≤
        ENNReal.ofReal Λ * volume (a.cellZ π k ℓ i q.1) := by
    intro m' q
    rw [hvol, hΛv]
    have hcomm : ∀ c, ∑ m, a.pairW π k ℓ i m m' q c =
        ∑ m, a.recMass π k ℓ i m' (q.1, c) * a.recMass π k ℓ i m (q.1, c) /
          a.recTotal π k ℓ i (q.1, c) := by
      intro c
      refine Finset.sum_congr rfl fun m _ => ?_
      unfold pairW
      rw [mul_comm (a.recMass π k ℓ i m (q.1, c))]
    calc ∑' c, ∑ m, a.pairW π k ℓ i m m' q c
        = ∑' c, ∑ m, a.recMass π k ℓ i m' (q.1, c) * a.recMass π k ℓ i m (q.1, c) /
            a.recTotal π k ℓ i (q.1, c) := tsum_congr hcomm
      _ ≤ ∑' c, a.recMass π k ℓ i m' (q.1, c) :=
          ENNReal.tsum_le_tsum (fun c => sum_pair_le ha π k ℓ i m' (q.1, c))
      _ ≤ _ := tsum_recMass_le ha π k ℓ i m' q.1
      _ ≤ _ := cvd_cell_mass ha π k ℓ i s hP m' q.1
  have key := hM (Q := a.GoodCell π k ℓ i) (a.ncand π k ℓ i) (a.Gz π k ℓ i)
    (fun q => a.cellZ π k ℓ i q.1) (a.pairW π k ℓ i) Λ hΛ0 hn
    (fun m => Gz_totalDegree ha π k ℓ i m) hbound
    (fun q => cellZ_measurable π k ℓ i hN q.1) (fun q => q.2)
    (fun q q' hqq' => cellZ_disjoint π k ℓ i (fun h => hqq' (Subtype.ext h)))
    (fun q => by rw [hvol]; exact ENNReal.ofReal_pos.2 hvpos)
    (fun q => by rw [hvol]; exact ENNReal.ofReal_lt_top)
    hclose hmarg1 hmarg2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerical simplification
  have hΛeq : Λ = 240 * a.rK k ^ 2 * a.tangent k ^ (-(a.rd * π.s')) /
      ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
    rw [hΛ, hv, show -2 * π.r - a.rd * π.s' = -π.r + -π.r + -(a.rd * π.s') by ring,
      Real.rpow_add hN, Real.rpow_add hN]
    field_simp
    ring
  have h2T : ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 = (2 : ℝ) ^ (2 * (a.ls k ℓ).T) := by
    rw [← pow_mul, mul_comm]
  have hds : 0 ≤ a.tangent k ^ (-(a.rd * π.s')) := (Real.rpow_pos_of_pos hN _).le
  have hεR : 0 ≤ a.tangent k ^ (π.σ.c₀ * -π.εm) := (Real.rpow_pos_of_pos hN _).le
  calc 4 * Λ * (a.ncand π k ℓ i : ℝ) * (a.tangent k ^ π.σ.c₀) ^ (-π.εm)
      = 960 * a.rK k ^ 2 * a.tangent k ^ (-(a.rd * π.s')) * (a.ncand π k ℓ i : ℝ) *
          a.tangent k ^ (π.σ.c₀ * -π.εm) / ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
        rw [hΛeq, ← Real.rpow_mul hN.le]
        ring
    _ ≤ 960 * a.rK k ^ 2 * a.tangent k ^ (-(a.rd * π.s')) *
          (a.rK k * a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀)) *
          a.tangent k ^ (π.σ.c₀ * -π.εm) / ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
        gcongr
    _ = 960 * a.rK k ^ 3 * a.tangent k ^ (-(a.rd * π.s') +
          (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) + π.σ.c₀ * -π.εm) /
          ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
        have hsplit : a.tangent k ^ (-(a.rd * π.s')) *
            a.tangent k ^ (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) * a.tangent k ^ (π.σ.c₀ * -π.εm) =
            a.tangent k ^ (-(a.rd * π.s') + (a.rd * π.σ.c₀ + π.θ * π.σ.c₀) +
              π.σ.c₀ * -π.εm) := by
          rw [← Real.rpow_add hN, ← Real.rpow_add hN]
        rw [← hsplit]
        ring
    _ ≤ 1000 * a.rK k ^ 3 *
          a.tangent k ^ (-a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀) /
          ((2 : ℝ) ^ (a.ls k ℓ).T) ^ 2 := by
        gcongr
        · norm_num
        · unfold CmpParams.s'
          nlinarith [mul_nonneg (sub_nonneg.2 hd1.le) (mul_pos hθ hc₀).le]
    _ = 1000 * a.rK k ^ 3 *
          a.tangent k ^ (-a.rd * π.σ.s₀ + 2 * π.θ * π.σ.c₀ - π.εm * π.σ.c₀) /
          (2 : ℝ) ^ (2 * (a.ls k ℓ).T) := by
        rw [h2T]

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
