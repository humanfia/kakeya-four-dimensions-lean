/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompWorldsFormat.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompWorlds

/-!
# The encoded world is tempered

The encoded prior is again piecewise Lebesgue on sign-format pieces, and the encoded
event has sign-format slices, with polynomially larger size bounds.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_dyadic_crop_worlds (BoolFormat PriorFormat EventFormat)

/-- `decCoeff b o` as polynomials of degree at most one. -/
noncomputable def decCoeffPoly (b o : ℝ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![X 0, X 1, C b⁻¹ * (X 2 - C o), X 3, X 4, C b⁻¹ * X 5]

theorem eval_decCoeffPoly (b o : ℝ) (x : Fin 6 → ℝ) :
    (fun i => eval x (decCoeffPoly b o i)) = decCoeff b o x := by
  funext i
  fin_cases i <;> simp [decCoeffPoly, decCoeff, div_eq_inv_mul]

theorem totalDegree_decCoeffPoly_le (b o : ℝ) (i : Fin 6) :
    (decCoeffPoly b o i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [decCoeffPoly]
  · simp [decCoeffPoly]
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
  · simp [decCoeffPoly]
  · simp [decCoeffPoly]
  · refine (totalDegree_mul _ _).trans ?_
    simp

theorem boolFormat_decCoeff_preimage {R : ℝ} {D : ℕ} {A : Set (Fin 6 → ℝ)}
    (hA : BoolFormat R D A) (b o : ℝ) : BoolFormat R D (decCoeff b o ⁻¹' A) := by
  have h := hA.affine_preimage (decCoeffPoly b o) (totalDegree_decCoeffPoly_le b o)
  have heq : (fun x i => eval x (decCoeffPoly b o i)) = decCoeff b o := by
    funext x; exact eval_decCoeffPoly b o x
  rwa [heq] at h

/-- The incidence decoding `(x₀..x₅, x₆) ↦ (decCoeff b o (x₀..x₅), x₆)` as polynomials. -/
noncomputable def decIncPoly (b o : ℝ) : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  fun i => if h : (i : ℕ) < 6 then
      rename Fin.castSucc (decCoeffPoly b o ⟨i, h⟩)
    else X 6

theorem eval_decIncPoly (b o : ℝ) (x : Fin 7 → ℝ) :
    (fun i => eval x (decIncPoly b o i)) =
      Fin.snoc (decCoeff b o (fun j : Fin 6 => x j.castSucc)) (x 6) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [decIncPoly, Fin.snoc]
  · have hj : ((Fin.castSucc j : Fin 7) : ℕ) < 6 := by simp
    simp only [decIncPoly, hj, dite_true, eval_rename, Fin.snoc_castSucc]
    have := congrFun (eval_decCoeffPoly b o (fun j : Fin 6 => x j.castSucc)) j
    simpa [Function.comp_def] using this

theorem totalDegree_decIncPoly_le (b o : ℝ) (i : Fin 7) : (decIncPoly b o i).totalDegree ≤ 1 := by
  unfold decIncPoly
  split_ifs with h
  · exact (totalDegree_rename_le _ _).trans (totalDegree_decCoeffPoly_le b o _)
  · simp

/-- Bound on encoded coefficients. -/
theorem abs_encCoeff_le {b o R : ℝ} (hR : 0 ≤ R) {l : Fin 6 → ℝ} (hl : ∀ e, |l e| ≤ R)
    (e : Fin 6) : |encCoeff b o l e| ≤ (|b| + 1) * R + |o| := by
  have hb : 0 ≤ |b| := abs_nonneg b
  have ho : 0 ≤ |o| := abs_nonneg o
  have hplain : ∀ e', |l e'| ≤ (|b| + 1) * R + |o| := fun e' => by nlinarith [hl e']
  have h2 : |b * l 2 + o| ≤ (|b| + 1) * R + |o| :=
    calc |b * l 2 + o| ≤ |b * l 2| + |o| := abs_add_le _ _
      _ = |b| * |l 2| + |o| := by rw [abs_mul]
      _ ≤ |b| * R + |o| := by gcongr; exact hl 2
      _ ≤ (|b| + 1) * R + |o| := by nlinarith
  have h5 : |b * l 5| ≤ (|b| + 1) * R + |o| :=
    calc |b * l 5| = |b| * |l 5| := abs_mul _ _
      _ ≤ |b| * R := by gcongr; exact hl 5
      _ ≤ (|b| + 1) * R + |o| := by nlinarith
  fin_cases e
  · exact hplain 0
  · exact hplain 1
  · exact h2
  · exact hplain 3
  · exact hplain 4
  · exact h5

/-- One encoded prior piece. -/
theorem map_encTraj_piece (W c i : ℕ) {b : ℝ} (hb : b ≠ 0) (o : ℝ) (A : Set (Fin 6 → ℝ)) :
    Measure.map (encTraj W c b o) (Measure.map (fun x => (i, x)) (volume.restrict A)) =
      ENNReal.ofReal |(b ^ 2)|⁻¹ • Measure.map (fun x => (W * i + c, x))
        (volume.restrict (decCoeff b o ⁻¹' A)) := by
  have hmk : ∀ n : ℕ, Measurable (fun x : Fin 6 → ℝ => ((n, x) : Traj)) :=
    fun n => measurable_const.prodMk measurable_id
  rw [Measure.map_map (measurable_encTraj W c b o) (hmk i)]
  have hcomp : encTraj W c b o ∘ (fun x => (i, x)) =
      (fun x => (W * i + c, x)) ∘ encCoeff b o := rfl
  rw [hcomp, ← Measure.map_map (hmk _) (measurable_encCoeff b o),
    map_encCoeff_restrict hb o, Measure.map_smul]
  exact (hmk _).aemeasurable

/-- The encoded prior is tempered. -/
theorem encPrior_format {W : ℕ} (hW : 0 < W) {R β : ℝ} {D : ℕ} (hR : 1 ≤ R) (hβ : 1 ≤ β)
    (a b o : Fin W → ℝ) (ν : Fin W → Measure Traj)
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hb : ∀ c, b c ≠ 0 ∧ |b c| ≤ β ∧ (b c ^ 2)⁻¹ ≤ β)
    (ho : ∀ c, |o c| ≤ β) (hν : ∀ c, PriorFormat R D (ν c)) :
    PriorFormat (4 * W * R * β ^ 2) D (encPrior W a b o ν) := by
  classical
  choose m hm cc ii AA hAA hνeq using hν
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hbig : ∀ x : ℝ, x ≤ R → x ≤ 4 * W * R * β ^ 2 := by
    intro x hx
    have : R ≤ 4 * W * R * β ^ 2 := by
      have h1 : (1 : ℝ) ≤ β ^ 2 := one_le_pow₀ hβ
      have h2 : R ≤ R * β ^ 2 := le_mul_of_one_le_right hR0 h1
      have h3 : R * β ^ 2 ≤ 4 * W * (R * β ^ 2) := by
        have : (1 : ℝ) ≤ 4 * W := by linarith
        nlinarith [mul_nonneg hR0 (sq_nonneg β)]
      nlinarith
    linarith
  -- the reindexed pieces
  let e := finSigmaFinEquiv (m := W) (n := m)
  let wd : Fin (∑ c, m c) → Fin W := fun k => (e.symm k).1
  let pc : (k : Fin (∑ c, m c)) → Fin (m (wd k)) := fun k => (e.symm k).2
  refine ⟨∑ c, m c, ?_, fun k => a (wd k) * cc (wd k) (pc k) * |(b (wd k) ^ 2)|⁻¹,
    fun k => W * ii (wd k) (pc k) + (wd k : ℕ),
    fun k => decCoeff (b (wd k)) (o (wd k)) ⁻¹' AA (wd k) (pc k), ?_, ?_⟩
  · have : ((∑ c, m c : ℕ) : ℝ) ≤ W * R := by
      push_cast
      calc ∑ c, (m c : ℝ) ≤ ∑ _c : Fin W, R := Finset.sum_le_sum fun c _ => hm c
        _ = W * R := by simp
    have h4 : (W : ℝ) * R ≤ 4 * W * R * β ^ 2 := by
      have h1 : (1 : ℝ) ≤ β ^ 2 := one_le_pow₀ hβ
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ W) hR0]
    linarith
  · intro k
    set c := wd k
    set j := pc k
    obtain ⟨hc0, hcR, hiR, hfmt, hbox⟩ := hAA c j
    obtain ⟨hbc, hbβ, hbinv⟩ := hb c
    have hab : |(b c ^ 2)|⁻¹ ≤ β := by rwa [abs_of_nonneg (sq_nonneg _)]
    refine ⟨by have := (ha c).1; positivity, ?_, ?_, ?_, ?_⟩
    · calc a c * cc c j * |(b c ^ 2)|⁻¹ ≤ 1 * R * β :=
            mul_le_mul (mul_le_mul (ha c).2 hcR hc0 zero_le_one) hab (by positivity)
              (by positivity)
        _ ≤ 4 * W * R * β ^ 2 := by
            have h1 : β ≤ β ^ 2 := by nlinarith
            have h4 : (1 : ℝ) ≤ 4 * W := by linarith
            have h2 : R * β ≤ R * β ^ 2 := mul_le_mul_of_nonneg_left h1 hR0
            have h3 : R * β ^ 2 ≤ 4 * W * (R * β ^ 2) :=
              le_mul_of_one_le_left (mul_nonneg hR0 (sq_nonneg β)) h4
            nlinarith
    · have hc : ((c : ℕ) : ℝ) ≤ W := by exact_mod_cast c.isLt.le
      push_cast
      have : (W : ℝ) * ii c j + c ≤ W * R + W := by
        have := mul_le_mul_of_nonneg_left hiR (by linarith : (0 : ℝ) ≤ W)
        linarith
      have h2 : (W : ℝ) * R + W ≤ 4 * W * R * β ^ 2 := by
        have h1 : (1 : ℝ) ≤ β ^ 2 := one_le_pow₀ hβ
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ W) hR0]
      linarith
    · exact (boolFormat_decCoeff_preimage hfmt _ _).mono (hbig R le_rfl) le_rfl
    · intro x hx e'
      have hx' : decCoeff (b c) (o c) x ∈ AA c j := hx
      have hrec := abs_encCoeff_le (b := b c) (o := o c) hR0 (hbox _ hx') e'
      rw [encCoeff_decCoeff hbc] at hrec
      refine hrec.trans ?_
      have : (|b c| + 1) * R + |o c| ≤ 2 * β * R + β := by nlinarith [ho c]
      have h2 : 2 * β * R + β ≤ 4 * W * R * β ^ 2 := by
        nlinarith [mul_nonneg hR0 hβ0, mul_nonneg (mul_nonneg hR0 hβ0) hβ0]
      linarith
  · -- the measure identity
    unfold encPrior
    have hterm : ∀ c, ENNReal.ofReal (a c) • Measure.map (encTraj W c (b c) (o c)) (ν c) =
        ∑ j, ENNReal.ofReal (a c * cc c j * |(b c ^ 2)|⁻¹) •
          Measure.map (fun x => (W * ii c j + (c : ℕ), x))
            (volume.restrict (decCoeff (b c) (o c) ⁻¹' AA c j)) := by
      intro c
      rw [hνeq c, Measure.map_finset_sum (measurable_encTraj _ _ _ _).aemeasurable,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Measure.map_smul, map_encTraj_piece W c (ii c j) (hb c).1, smul_smul, smul_smul]
      swap
      · exact (measurable_encTraj _ _ _ _).aemeasurable
      congr 1
      obtain ⟨hc0, -⟩ := hAA c j
      rw [ENNReal.ofReal_mul (mul_nonneg (ha c).1 hc0), ENNReal.ofReal_mul (ha c).1]
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    symm
    rw [← Equiv.sum_comp e, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
    show (fun x : (i : Fin W) × Fin (m i) => ENNReal.ofReal (a x.1 * cc x.1 x.2 * |(b x.1 ^ 2)|⁻¹) •
      Measure.map (fun y => (W * ii x.1 x.2 + (x.1 : ℕ), y))
        (volume.restrict (decCoeff (b x.1) (o x.1) ⁻¹' AA x.1 x.2))) (e.symm (e ⟨c, j⟩)) = _
    rw [e.symm_apply_apply]

/-- The encoded event is tempered. -/
theorem encEvent_format {W : ℕ} (hW : 0 < W) {R β : ℝ} {D : ℕ} (hR : 1 ≤ R) (hβ : 1 ≤ β)
    (b o : Fin W → ℝ) (E : Fin W → Set Inc) (hb : ∀ c, b c ≠ 0 ∧ |b c| ≤ β)
    (ho : ∀ c, |o c| ≤ β) (hE : ∀ c, EventFormat R D (E c)) :
    EventFormat (4 * W * R * β ^ 2) D (encEvent hW b o E) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  have hb2 : (1 : ℝ) ≤ β ^ 2 := one_le_pow₀ hβ
  have hRbig : R ≤ 4 * W * R * β ^ 2 := by
    have h3 : R * β ^ 2 ≤ 4 * W * (R * β ^ 2) :=
      le_mul_of_one_le_left (mul_nonneg hR0 (sq_nonneg β)) (by linarith)
    nlinarith
  refine ⟨measurableSet_encEvent hW b o (fun c => (hE c).1), ?_, ?_, ?_⟩
  · intro p hp
    have := (hE (worldOf hW p.1.1)).2.1 hp
    exact ⟨mem_univ _, (mem_prod.mp this).2⟩
  · intro p hp
    set c := worldOf hW p.1.1
    obtain ⟨hidx, hcoef⟩ := (hE c).2.2.1 _ hp
    constructor
    · have hdecomp : (p.1.1 : ℝ) = W * ((p.1.1 / W : ℕ) : ℝ) + ((p.1.1 % W : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod p.1.1 W).symm
      have hmod : ((p.1.1 % W : ℕ) : ℝ) ≤ W := by exact_mod_cast (Nat.mod_lt _ hW).le
      have hidx' : ((p.1.1 / W : ℕ) : ℝ) ≤ R := hidx
      have h1 := mul_le_mul_of_nonneg_left hidx' (by linarith : (0 : ℝ) ≤ W)
      have h2 : (W : ℝ) * R + W ≤ 4 * W * R * β ^ 2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ W) hR0]
      rw [hdecomp]; linarith
    · intro e
      have hrec := abs_encCoeff_le (b := b c) (o := o c) hR0 hcoef e
      rw [encCoeff_decCoeff (hb c).1] at hrec
      refine hrec.trans ?_
      have : (|b c| + 1) * R + |o c| ≤ 2 * β * R + β := by nlinarith [ho c, (hb c).2]
      have h2 : 2 * β * R + β ≤ 4 * W * R * β ^ 2 := by
        nlinarith [mul_nonneg hR0 hβ0, mul_nonneg (mul_nonneg hR0 hβ0) hβ0]
      linarith
  · intro i
    set c := worldOf hW i
    have hslice := ((hE c).2.2.2 (i / W)).affine_preimage (decIncPoly (b c) (o c))
      (totalDegree_decIncPoly_le (b c) (o c))
    have heq : (fun x i => eval x (decIncPoly (b c) (o c) i)) ⁻¹'
        {x : Fin 7 → ℝ | ((i / W, fun j => x j.castSucc), x 6) ∈ E c} =
        {x : Fin 7 → ℝ | ((i, fun j => x j.castSucc), x 6) ∈ encEvent hW b o E} := by
      have h6 : ∀ (v : Fin 6 → ℝ) (a : ℝ), Fin.snoc (α := fun _ : Fin 7 => ℝ) v a 6 = a := by
        intro v a; simp [Fin.snoc]
      ext x
      simp only [mem_preimage, mem_ofPred_eq, eval_decIncPoly, encEvent]
      simp [c, Fin.snoc_castSucc, h6]
    rw [← heq]
    exact hslice.mono hRbig le_rfl

/-- `encCoeff b o` as polynomials of degree at most one. -/
noncomputable def encCoeffPoly (b o : ℝ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![X 0, X 1, C b * X 2 + C o, X 3, X 4, C b * X 5]

theorem eval_encCoeffPoly (b o : ℝ) (x : Fin 6 → ℝ) :
    (fun i => eval x (encCoeffPoly b o i)) = encCoeff b o x := by
  funext i
  fin_cases i <;> simp [encCoeffPoly, encCoeff]

theorem totalDegree_encCoeffPoly_le (b o : ℝ) (i : Fin 6) :
    (encCoeffPoly b o i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [encCoeffPoly]
  · simp [encCoeffPoly]
  · refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
    exact (totalDegree_mul _ _).trans (by simp)
  · simp [encCoeffPoly]
  · simp [encCoeffPoly]
  · exact (totalDegree_mul _ _).trans (by simp)

/-- The incidence encoding `(x₀..x₅, x₆) ↦ (encCoeff b o (x₀..x₅), x₆)` as polynomials. -/
noncomputable def encIncPoly (b o : ℝ) : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  fun i => if h : (i : ℕ) < 6 then
      rename Fin.castSucc (encCoeffPoly b o ⟨i, h⟩)
    else X 6

theorem eval_encIncPoly (b o : ℝ) (x : Fin 7 → ℝ) :
    (fun i => eval x (encIncPoly b o i)) =
      Fin.snoc (encCoeff b o (fun j : Fin 6 => x j.castSucc)) (x 6) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [encIncPoly, Fin.snoc]
  · have hj : ((Fin.castSucc j : Fin 7) : ℕ) < 6 := by simp
    simp only [encIncPoly, hj, dite_true, eval_rename, Fin.snoc_castSucc]
    have := congrFun (eval_encCoeffPoly b o (fun j : Fin 6 => x j.castSucc)) j
    simpa [Function.comp_def] using this

theorem totalDegree_encIncPoly_le (b o : ℝ) (i : Fin 7) : (encIncPoly b o i).totalDegree ≤ 1 := by
  unfold encIncPoly
  split_ifs with h
  · exact (totalDegree_rename_le _ _).trans (totalDegree_encCoeffPoly_le b o _)
  · simp

/-- The decoded selection of one world, from a selection of the encoded world. -/
theorem eventFormat_decoded {W : ℕ} (c : ℕ) {b o R R' : ℝ} {D D' : ℕ} {E : Set Inc}
    {S : Set Inc} (hE : EventFormat R D E) (hS : MeasurableSet S)
    (hSl : ∀ i, BoolFormat R' D' {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ S})
    (hsub : encInc W c b o ⁻¹' S ⊆ E) :
    EventFormat (max R R') (max D D') (encInc W c b o ⁻¹' S) := by
  obtain ⟨hEm, hEt, hEb, -⟩ := hE
  refine ⟨(measurable_encInc W c b o) hS, (hsub.trans hEt), ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := hEb p (hsub hp)
    exact ⟨h1.trans (le_max_left _ _), fun e => (h2 e).trans (le_max_left _ _)⟩
  · intro i
    have hsl := ((hSl (W * i + c)).affine_preimage (encIncPoly b o)
      (totalDegree_encIncPoly_le b o)).mono (le_max_right R R') (le_max_right D D')
    have h6 : ∀ (v : Fin 6 → ℝ) (a : ℝ), Fin.snoc (α := fun _ : Fin 7 => ℝ) v a 6 = a := by
      intro v a; simp [Fin.snoc]
    have heq : (fun x i => eval x (encIncPoly b o i)) ⁻¹'
        {x : Fin 7 → ℝ | ((W * i + c, fun j : Fin 6 => x j.castSucc), x 6) ∈ S} =
        {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ encInc W c b o ⁻¹' S} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq, eval_encIncPoly, encInc, encTraj]
      simp [Fin.snoc_castSucc, h6]
    rw [← heq]
    exact hsl

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
