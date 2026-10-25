-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatFormat.lean
import Submission.Obl.k4_terminal_label_saturation.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat
import Submission.Lib.K4RepresentativeAssembly.FiniteFormat
import Submission.Obl.k4_terminal_label_saturation.SatVolume

/-!
# Polynomial format of the crossing-count restriction

Saturation keeps only the incidences whose terminal observation is compatible
with at most `H` charts of their world.  In the seven event coordinates
(six line coefficients and the time) this is a Boolean combination of
polynomially many atoms of degree at most four:

* for each hidden bin in the coordinate range, a bin-boundary atom;
* for each bin and chart, six atoms describing `chartCompat` at that bin.

The general lemma `fmt_of_atoms` turns such a description into the frozen
format `fmt`.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MvPolynomial Set

/-- A Boolean combination of atoms indexed by any finite type is in the
frozen polynomial format, with one atom per index. -/
theorem fmt_of_atoms {n D : ℕ} {ι : Type*} [Fintype ι] (p : ι → MvPolynomial (Fin n) ℝ)
    (hp : ∀ k, (p k).totalDegree ≤ D) (Φ : (ι → Bool) → Bool) (S : Set (Fin n → ℝ))
    (hS : ∀ z, z ∈ S ↔ Φ (fun k => decide (0 ≤ eval z (p k))) = true) :
    fmt n (Fintype.card ι) D S := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, le_rfl, fun i => p (e.symm i), fun i => hp _,
    fun v => Φ (fun k => v (e k)), ?_⟩
  intro z
  rw [hS z]
  simp only [Equiv.symm_apply_apply]

/-! ## Event-coordinate polynomials -/

/-- The four space-time coordinates of an incidence, as polynomials in the six
line coefficients and the time. -/
noncomputable def eventCoord : Fin 4 → MvPolynomial (Fin 7) ℝ :=
  ![X 6, X 0 + X 6 * X 3, X 1 + X 6 * X 4, X 2 + X 6 * X 5]

theorem eval_eventCoord (z : Fin 7 → ℝ) :
    (fun i => eval z (eventCoord i)) = x (0, fun i : Fin 6 => z i.castSucc) (z 6) := by
  funext i
  fin_cases i <;> simp [eventCoord, x]

theorem eventCoord_degree (i : Fin 4) : (eventCoord i).totalDegree ≤ 2 := by
  fin_cases i
  · simp [eventCoord]
  all_goals
    dsimp [eventCoord]
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    exact (totalDegree_mul _ _).trans (by simp)

/-- Evaluation of `R` at the incidence's base point and a prescribed hidden value. -/
noncomputable def baseEval (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) : MvPolynomial (Fin 7) ℝ :=
  aeval ![eventCoord 0, eventCoord 1, eventCoord 2, C w] R

theorem baseEval_eval (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) (z : Fin 7 → ℝ) :
    eval z (baseEval R w) =
      eval ![z 6, z 0 + z 6 * z 3, z 1 + z 6 * z 4, w] R := by
  rw [baseEval, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real]
  have hv : (fun i => eval z (![eventCoord 0, eventCoord 1, eventCoord 2, C w] i)) =
      ![z 6, z 0 + z 6 * z 3, z 1 + z 6 * z 4, w] := by
    funext i
    fin_cases i <;> simp [eventCoord]
  rw [hv]

theorem baseEval_degree (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    (baseEval R w).totalDegree ≤ 2 * R.totalDegree := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.degree_aeval_le_mul
  intro i
  fin_cases i
  · exact eventCoord_degree 0
  · exact eventCoord_degree 1
  · exact eventCoord_degree 2
  · simp

/-- The squared norm in the spatial test of a chart. -/
noncomputable def boxPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) :
    MvPolynomial (Fin 7) ℝ :=
  ∑ i : Fin 2, (∑ k : Fin 2, C (Q⁻¹ i k) *
    (![eventCoord 1, eventCoord 2] k - C (c k) - eventCoord 0 * C (u k))) ^ 2

theorem boxPoly_eval (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (z : Fin 7 → ℝ) :
    eval z (boxPoly Q c u) =
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 0 + z 6 * z 3, z 1 + z 6 * z 4] - c -
        (z 6) • u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [boxPoly, eventCoord, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  ring

theorem boxPoly_degree (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) :
    (boxPoly Q c u).totalDegree ≤ 4 := by
  unfold boxPoly
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_pow _ _).trans
  have hin : (∑ k : Fin 2, C (Q⁻¹ i k) *
      (![eventCoord 1, eventCoord 2] k - C (c k) - eventCoord 0 * C (u k))).totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro k _
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_sub _ _).trans
      apply max_le
      · fin_cases k
        · exact eventCoord_degree 1
        · exact eventCoord_degree 2
      · simp
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, add_zero]
      exact (eventCoord_degree 0).trans (by norm_num)
  omega

/-! ## The crossing-count restriction -/

/-- The terminal observation of an event point in the seven coordinates. -/
noncomputable def obsZ (B δ : ℝ) (z : Fin 7 → ℝ) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  (WithLp.toLp 2 ![z 6, z 0 + z 6 * z 3, z 1 + z 6 * z 4], ⌊B * (z 2 + z 6 * z 5) / δ⌋)

theorem obs_eq_obsZ (B δ : ℝ) (i : ℕ) (z : Fin 7 → ℝ) :
    obs B δ ((i, fun j : Fin 6 => z j.castSucc), z 6) = obsZ B δ z := by
  simp [obs, obsZ, x]

/-- Lower end of the bin range for hidden coordinates in `[-Λ, Λ]`. -/
noncomputable def binLow (Λ B δ : ℝ) : ℤ := ⌊-(Λ * B / δ)⌋

/-- Number of bins covering hidden coordinates in `[-Λ, Λ]`. -/
noncomputable def binCount (Λ B δ : ℝ) : ℕ := ⌈2 * (Λ * B / δ)⌉₊ + 2

theorem floor_mem_binRange {Λ B δ w : ℝ} (hΛ : 0 ≤ Λ) (hB : 0 < B) (hδ : 0 < δ)
    (hw : |w| ≤ Λ) :
    ∃ k : Fin (binCount Λ B δ), ⌊B * w / δ⌋ = binLow Λ B δ + (k : ℤ) := by
  set a := Λ * B / δ with ha
  have ha0 : 0 ≤ a := by positivity
  have hlo : -a ≤ B * w / δ := by
    rw [ha, neg_div' ]
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith [(abs_le.mp hw).1]
  have hhi : B * w / δ ≤ a := by
    rw [ha]
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith [(abs_le.mp hw).2]
  have h1 : binLow Λ B δ ≤ ⌊B * w / δ⌋ := Int.floor_mono hlo
  have h2 : ⌊B * w / δ⌋ - binLow Λ B δ < (binCount Λ B δ : ℤ) := by
    have e1 : (⌊B * w / δ⌋ : ℝ) ≤ a := (Int.floor_le _).trans hhi
    have e2 : -a - 1 < (binLow Λ B δ : ℝ) := Int.sub_one_lt_floor _
    have e3 : 2 * a ≤ (⌈2 * a⌉₊ : ℝ) := Nat.le_ceil _
    have : ((⌊B * w / δ⌋ - binLow Λ B δ : ℤ) : ℝ) < ((binCount Λ B δ : ℕ) : ℝ) := by
      push_cast [binCount]
      linarith
    exact_mod_cast this
  refine ⟨⟨(⌊B * w / δ⌋ - binLow Λ B δ).toNat, ?_⟩, ?_⟩
  · omega
  · simp only [Fin.val_mk]
    omega

/-- The six atoms of chart compatibility at a fixed hidden value `w`. -/
noncomputable def compatAtom (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    Fin 6 → MvPolynomial (Fin 7) ℝ :=
  ![eventCoord 0 - C (j / (2 : ℝ) ^ T), C ((j + 1) / (2 : ℝ) ^ T) - eventCoord 0,
    C (κ ^ 2) - boxPoly Q c u, C (3 * κ * δ) - baseEval R w, C (3 * κ * δ) + baseEval R w,
    if |curvature R 3| * (δ / B) ≤ B / (2 * κ) then
      baseEval (pderiv 3 R) w ^ 2 - C ((B / (2 * κ)) ^ 2) else C 1]

theorem compatAtom_degree (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (w : ℝ) (a : Fin 6) : (compatAtom T j κ δ B c u Q R w a).totalDegree ≤ 4 := by
  have h0 := eventCoord_degree 0
  have hb := baseEval_degree R w
  have hd : (pderiv (3 : Fin 4) R).totalDegree ≤ 1 :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le R 3).trans (by omega)
  have hb' := baseEval_degree (pderiv 3 R) w
  have hC (r : ℝ) : (C r : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 4 := by
    rw [totalDegree_C]; omega
  fin_cases a
  · exact (totalDegree_sub _ _).trans (max_le (h0.trans (by norm_num)) (hC _))
  · exact (totalDegree_sub _ _).trans (max_le (hC _) (h0.trans (by norm_num)))
  · exact (totalDegree_sub _ _).trans (max_le (hC _) (boxPoly_degree Q c u))
  · exact (totalDegree_sub _ _).trans (max_le (hC _) (by omega))
  · exact (totalDegree_add _ _).trans (max_le (hC _) (by omega))
  · change (if |curvature R 3| * (δ / B) ≤ B / (2 * κ) then
      baseEval (pderiv 3 R) w ^ 2 - C ((B / (2 * κ)) ^ 2) else C 1).totalDegree ≤ 4
    split_ifs
    · apply (totalDegree_sub _ _).trans (max_le ?_ (hC _))
      exact (totalDegree_pow _ _).trans (by omega)
    · exact hC 1

/-- The chart membership of an observation, in coordinates. -/
theorem mem_chartCompat_obsZ_iff (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (z : Fin 7 → ℝ) (n : ℤ)
    (hn : (obsZ B δ z).2 = n) :
    obsZ B δ z ∈ chartCompat T j κ δ B c u Q R ↔
      (j / (2 : ℝ) ^ T ≤ z 6 ∧ z 6 ≤ (j + 1) / (2 : ℝ) ^ T) ∧
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 0 + z 6 * z 3, z 1 + z 6 * z 4] - c -
        (z 6) • u)‖ ≤ κ ∧
      hiddenBinTest R (z 6) (z 0 + z 6 * z 3) (z 1 + z 6 * z 4) (3 * κ * δ) (B / (2 * κ))
        (δ / B) n := by
  rw [← hn]
  rfl

theorem compatAtom_iff (T : ℕ) (j : ℝ) {κ δ B : ℝ} (hκ : 0 ≤ κ) (hB : 0 < B)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (z : Fin 7 → ℝ) (n : ℤ) (hn : (obsZ B δ z).2 = n) :
    obsZ B δ z ∈ chartCompat T j κ δ B c u Q R ↔
      ∀ a, 0 ≤ eval z (compatAtom T j κ δ B c u Q R ((n : ℝ) * (δ / B)) a) := by
  have hβ : 0 ≤ B / (2 * κ) := by positivity
  set w : ℝ := (n : ℝ) * (δ / B) with hw
  set V : ℝ := eval ![z 6, z 0 + z 6 * z 3, z 1 + z 6 * z 4, w] R with hV
  set V' : ℝ := eval ![z 6, z 0 + z 6 * z 3, z 1 + z 6 * z 4, w] (pderiv 3 R) with hV'
  set nb : ℝ := ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 0 + z 6 * z 3, z 1 + z 6 * z 4] -
    c - (z 6) • u)‖ with hnb
  have hz6 : eval z (eventCoord 0) = z 6 := by simp [eventCoord]
  have e0 : eval z (compatAtom T j κ δ B c u Q R w 0) = z 6 - j / (2 : ℝ) ^ T := by
    change eval z (eventCoord 0 - C (j / (2 : ℝ) ^ T)) = _
    rw [map_sub, eval_C, hz6]
  have e1 : eval z (compatAtom T j κ δ B c u Q R w 1) = (j + 1) / (2 : ℝ) ^ T - z 6 := by
    change eval z (C ((j + 1) / (2 : ℝ) ^ T) - eventCoord 0) = _
    rw [map_sub, eval_C, hz6]
  have e2 : eval z (compatAtom T j κ δ B c u Q R w 2) = κ ^ 2 - nb ^ 2 := by
    change eval z (C (κ ^ 2) - boxPoly Q c u) = _
    rw [map_sub, eval_C, boxPoly_eval]
  have e3 : eval z (compatAtom T j κ δ B c u Q R w 3) = 3 * κ * δ - V := by
    change eval z (C (3 * κ * δ) - baseEval R w) = _
    rw [map_sub, eval_C, baseEval_eval]
  have e4 : eval z (compatAtom T j κ δ B c u Q R w 4) = 3 * κ * δ + V := by
    change eval z (C (3 * κ * δ) + baseEval R w) = _
    rw [map_add, eval_C, baseEval_eval]
  have e5 : 0 ≤ eval z (compatAtom T j κ δ B c u Q R w 5) ↔
      (|curvature R 3| * (δ / B) ≤ B / (2 * κ) → B / (2 * κ) ≤ |V'|) := by
    change 0 ≤ eval z (if |curvature R 3| * (δ / B) ≤ B / (2 * κ) then
      baseEval (pderiv 3 R) w ^ 2 - C ((B / (2 * κ)) ^ 2) else C 1) ↔ _
    split_ifs with hlow
    · rw [map_sub, map_pow, eval_C, baseEval_eval, sub_nonneg, ← hV', ← sq_abs V',
        sq_le_sq₀ hβ (abs_nonneg _)]
      simp only [hlow, forall_const]
    · simp only [map_one, zero_le_one, hlow, IsEmpty.forall_iff]
  rw [mem_chartCompat_obsZ_iff T j κ δ B c u Q R z n hn]
  have hall : (∀ a : Fin 6, 0 ≤ eval z (compatAtom T j κ δ B c u Q R w a)) ↔
      (0 ≤ eval z (compatAtom T j κ δ B c u Q R w 0) ∧
        0 ≤ eval z (compatAtom T j κ δ B c u Q R w 1) ∧
        0 ≤ eval z (compatAtom T j κ δ B c u Q R w 2) ∧
        0 ≤ eval z (compatAtom T j κ δ B c u Q R w 3) ∧
        0 ≤ eval z (compatAtom T j κ δ B c u Q R w 4) ∧
        0 ≤ eval z (compatAtom T j κ δ B c u Q R w 5)) := by
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
    · rintro ⟨h0, h1, h2, h3, h4, h5⟩ a
      fin_cases a
      exacts [h0, h1, h2, h3, h4, h5]
  rw [hall, e0, e1, e2, e3, e4, e5]
  have hnb : nb ≤ κ ↔ 0 ≤ κ ^ 2 - nb ^ 2 := by
    rw [sub_nonneg, sq_le_sq₀ (norm_nonneg _) hκ]
  have hV3 : |V| ≤ 3 * κ * δ ↔ (0 ≤ 3 * κ * δ - V ∧ 0 ≤ 3 * κ * δ + V) := by
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  simp only [hiddenBinTest]
  rw [← hnb]
  change (_ ∧ _) ∧ nb ≤ κ ∧ (|V| ≤ 3 * κ * δ ∧ _) ↔ _
  rw [hV3]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, ⟨h3, h4⟩, h5⟩
    exact ⟨by linarith, by linarith, h2, h3, h4, h5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact ⟨⟨by linarith, by linarith⟩, h2, ⟨h3, h4⟩, h5⟩

theorem eval_eventCoord_three (z : Fin 7 → ℝ) : eval z (eventCoord 3) = z 2 + z 6 * z 5 := by
  simp [eventCoord]

/-- The atoms describing the crossing-count restriction. -/
noncomputable def crossingAtom (T : ℕ) (κ δ B Λ : ℝ) {C' : ℕ} (j : Fin C' → ℝ)
    (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C' → MvPolynomial (Fin 4) ℝ) :
    Fin 2 ⊕ (Fin (binCount Λ B δ + 1) ⊕ (Fin (binCount Λ B δ) × Fin C' × Fin 6)) →
      MvPolynomial (Fin 7) ℝ
  | Sum.inl 0 => C Λ - eventCoord 3
  | Sum.inl 1 => C Λ + eventCoord 3
  | Sum.inr (Sum.inl k) => C B * eventCoord 3 - C (((binLow Λ B δ + (k : ℤ) : ℤ) : ℝ) * δ)
  | Sum.inr (Sum.inr (k, b, a)) => compatAtom T (j b) κ δ B (c b) (u b) (Q b) (R b)
      (((binLow Λ B δ + (k : ℤ) : ℤ) : ℝ) * (δ / B)) a

/-- Saturation's restriction is in polynomial format: the event points whose
hidden coordinate lies in `[-Λ, Λ]` and whose observation is compatible with at
most `H` of the charts selected by `sel`. -/
theorem fmt_crossing (T : ℕ) {κ δ B Λ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ) (hB : 0 < B)
    (hΛ : 0 ≤ Λ) (H : ℝ) {C' : ℕ} (sel : Fin C' → Prop)
    (j : Fin C' → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (hR : ∀ b, (R b).totalDegree ≤ 2) :
    fmt 7 (2 + ((binCount Λ B δ + 1) + binCount Λ B δ * (C' * 6))) 4
      {z : Fin 7 → ℝ | |z 2 + z 6 * z 5| ≤ Λ ∧
        (({b | sel b ∧
          obsZ B δ z ∈ chartCompat T (j b) κ δ B (c b) (u b) (Q b) (R b)}.ncard : ℕ) : ℝ) ≤ H} := by
  classical
  set K := binCount Λ B δ with hK
  set n₀ := binLow Λ B δ with hn₀
  let ι := Fin 2 ⊕ (Fin (K + 1) ⊕ (Fin K × Fin C' × Fin 6))
  have hcard : (Fintype.card ι : ℝ) = 2 + ((K + 1) + K * (C' * 6)) := by
    simp [ι, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [← hcard]
  let p : ι → MvPolynomial (Fin 7) ℝ := crossingAtom T κ δ B Λ j c u Q R
  have hdeg : ∀ k, (p k).totalDegree ≤ 4 := by
    have h3 := eventCoord_degree 3
    have hC (r : ℝ) : (C r : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 4 := by
      rw [totalDegree_C]; omega
    rintro (k | k | ⟨k, b, a⟩)
    · fin_cases k
      · exact (totalDegree_sub _ _).trans (max_le (hC _) (h3.trans (by norm_num)))
      · exact (totalDegree_add _ _).trans (max_le (hC _) (h3.trans (by norm_num)))
    · apply (totalDegree_sub _ _).trans (max_le ?_ (hC _))
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_C]
      omega
    · exact compatAtom_degree T (j b) κ δ B (c b) (u b) (Q b) (R b) (hR b) _ a
  -- the Boolean combination
  let Ψ : (ι → Bool) → Prop := fun v =>
    v (Sum.inl 0) = true ∧ v (Sum.inl 1) = true ∧ ∃ k : Fin K,
      v (Sum.inr (Sum.inl k.castSucc)) = true ∧ v (Sum.inr (Sum.inl k.succ)) = false ∧
      (({b | sel b ∧ ∀ a, v (Sum.inr (Sum.inr (k, b, a))) = true}.ncard : ℕ) : ℝ) ≤ H
  refine fmt_of_atoms p hdeg (fun v => decide (Ψ v)) _ ?_
  intro z
  set w := z 2 + z 6 * z 5 with hw
  have hx3 : eval z (eventCoord 3) = w := eval_eventCoord_three z
  have hlo : (0 ≤ eval z (p (Sum.inl 0))) ↔ w ≤ Λ := by
    change 0 ≤ eval z (C Λ - eventCoord 3) ↔ _
    rw [map_sub, eval_C, hx3, sub_nonneg]
  have hhi : (0 ≤ eval z (p (Sum.inl 1))) ↔ -Λ ≤ w := by
    change 0 ≤ eval z (C Λ + eventCoord 3) ↔ _
    rw [map_add, eval_C, hx3]
    constructor <;> intro h <;> linarith
  have hbin (k : Fin (K + 1)) : (0 ≤ eval z (p (Sum.inr (Sum.inl k)))) ↔
      (((n₀ + (k : ℤ) : ℤ) : ℝ)) ≤ B * w / δ := by
    change 0 ≤ eval z (C B * eventCoord 3 - C ((((n₀ + (k : ℤ) : ℤ) : ℝ)) * δ)) ↔ _
    rw [map_sub, map_mul, eval_C, eval_C, hx3, sub_nonneg, le_div_iff₀ hδ]
  have hcomp (k : Fin K) (b : Fin C') (hk : (obsZ B δ z).2 = n₀ + (k : ℤ)) :
      (∀ a, 0 ≤ eval z (p (Sum.inr (Sum.inr (k, b, a))))) ↔
        obsZ B δ z ∈ chartCompat T (j b) κ δ B (c b) (u b) (Q b) (R b) := by
    rw [compatAtom_iff T (j b) hκ hB (c b) (u b) (Q b) (R b) z _ hk]
    rfl
  have hfloor : (obsZ B δ z).2 = ⌊B * w / δ⌋ := rfl
  have hset (k : Fin K) (hk : ⌊B * w / δ⌋ = n₀ + (k : ℤ)) :
      {b | sel b ∧ ∀ a, 0 ≤ eval z (p (Sum.inr (Sum.inr (k, b, a))))} =
        {b | sel b ∧ obsZ B δ z ∈ chartCompat T (j b) κ δ B (c b) (u b) (Q b) (R b)} := by
    ext b
    simp only [mem_ofPred_eq]
    rw [hcomp k b (by rw [hfloor, hk])]
  rw [decide_eq_true_iff]
  simp only [Ψ, mem_ofPred_eq, decide_eq_true_eq, decide_eq_false_iff_not, hlo, hhi, hbin]
  constructor
  · rintro ⟨hw, hcount⟩
    obtain ⟨k, hk⟩ := floor_mem_binRange hΛ hB hδ hw
    refine ⟨(abs_le.mp hw).2, (abs_le.mp hw).1, k, ?_, ?_, ?_⟩
    · have := Int.floor_le (B * w / δ)
      rw [hk] at this
      simpa only [Fin.coe_castSucc] using this
    · have := Int.lt_floor_add_one (B * w / δ)
      rw [hk] at this
      simp only [Fin.val_succ, not_le]
      push_cast at this ⊢
      linarith
    · rw [hset k hk]
      exact hcount
  · rintro ⟨hwhi, hwlo, k, hk1, hk2, hcount⟩
    have hk : ⌊B * w / δ⌋ = n₀ + (k : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa only [Fin.coe_castSucc] using hk1
      · simp only [Fin.val_succ, not_le] at hk2
        push_cast at hk2 ⊢
        linarith
    refine ⟨abs_le.mpr ⟨hwlo, hwhi⟩, ?_⟩
    rw [← hset k hk]
    exact hcount

/-- Any condition on the family of chart compatibilities of the observation, at
hidden bins inside the range of `binLow`/`binCount`, is in polynomial format:
bin-boundary atoms locate the bin and six atoms per bin and chart decide each
compatibility. -/
theorem fmt_binwise (T : ℕ) {κ δ B Λ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 < δ) (hB : 0 < B)
    {C' : ℕ} (j : Fin C' → ℝ) (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (hR : ∀ b, (R b).totalDegree ≤ 2) (Ψ : (Fin C' → Prop) → Prop) :
    fmt 7 ((binCount Λ B δ + 1) + binCount Λ B δ * (C' * 6)) 4
      {z : Fin 7 → ℝ | ∃ k : Fin (binCount Λ B δ),
        ⌊B * (z 2 + z 6 * z 5) / δ⌋ = binLow Λ B δ + (k : ℤ) ∧
        Ψ (fun b => obsZ B δ z ∈ chartCompat T (j b) κ δ B (c b) (u b) (Q b) (R b))} := by
  classical
  set K := binCount Λ B δ with hK
  set n₀ := binLow Λ B δ with hn₀
  let ι := Fin (K + 1) ⊕ (Fin K × Fin C' × Fin 6)
  have hcard : (Fintype.card ι : ℝ) = (K + 1) + K * (C' * 6) := by
    simp [ι, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [← hcard]
  let p : ι → MvPolynomial (Fin 7) ℝ := fun k => crossingAtom T κ δ B Λ j c u Q R (Sum.inr k)
  have hdeg : ∀ k, (p k).totalDegree ≤ 4 := by
    have h3 := eventCoord_degree 3
    have hC (r : ℝ) : (C r : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 4 := by
      rw [totalDegree_C]; omega
    rintro (k | ⟨k, b, a⟩)
    · apply (totalDegree_sub _ _).trans (max_le ?_ (hC _))
      apply (totalDegree_mul _ _).trans
      rw [totalDegree_C]
      omega
    · exact compatAtom_degree T (j b) κ δ B (c b) (u b) (Q b) (R b) (hR b) _ a
  let Ψ' : (ι → Bool) → Prop := fun v => ∃ k : Fin K,
      v (Sum.inl k.castSucc) = true ∧ v (Sum.inl k.succ) = false ∧
      Ψ (fun b => ∀ a, v (Sum.inr (k, b, a)) = true)
  refine fmt_of_atoms p hdeg (fun v => decide (Ψ' v)) _ ?_
  intro z
  set w := z 2 + z 6 * z 5 with hw
  have hx3 : eval z (eventCoord 3) = w := eval_eventCoord_three z
  have hbin (k : Fin (K + 1)) : (0 ≤ eval z (p (Sum.inl k))) ↔
      (((n₀ + (k : ℤ) : ℤ) : ℝ)) ≤ B * w / δ := by
    change 0 ≤ eval z (C B * eventCoord 3 - C ((((n₀ + (k : ℤ) : ℤ) : ℝ)) * δ)) ↔ _
    rw [map_sub, map_mul, eval_C, eval_C, hx3, sub_nonneg, le_div_iff₀ hδ]
  have hfloor : (obsZ B δ z).2 = ⌊B * w / δ⌋ := rfl
  have hpred (k : Fin K) (hk : ⌊B * w / δ⌋ = n₀ + (k : ℤ)) :
      (fun b => ∀ a, decide (0 ≤ eval z (p (Sum.inr (k, b, a)))) = true) =
        (fun b => obsZ B δ z ∈ chartCompat T (j b) κ δ B (c b) (u b) (Q b) (R b)) := by
    funext b
    apply propext
    simp only [decide_eq_true_eq]
    rw [compatAtom_iff T (j b) hκ hB (c b) (u b) (Q b) (R b) z _ (by rw [hfloor, hk])]
    rfl
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hΨ⟩
    refine ⟨k, ?_, ?_, ?_⟩
    · rw [decide_eq_true_eq, hbin]
      have := Int.floor_le (B * w / δ)
      rw [hk] at this
      simpa only [Fin.val_castSucc] using this
    · rw [decide_eq_false_iff_not, hbin, not_le]
      have := Int.lt_floor_add_one (B * w / δ)
      rw [hk] at this
      simp only [Fin.val_succ]
      push_cast at this ⊢
      linarith
    · rw [hpred k hk]
      exact hΨ
  · rintro ⟨k, hk1, hk2, hΨ⟩
    rw [decide_eq_true_eq, hbin] at hk1
    rw [decide_eq_false_iff_not, hbin, not_le] at hk2
    have hk : ⌊B * w / δ⌋ = n₀ + (k : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · simpa only [Fin.val_castSucc] using hk1
      · simp only [Fin.val_succ] at hk2
        push_cast at hk2 ⊢
        linarith
    refine ⟨k, hk, ?_⟩
    rw [← hpred k hk]
    exact hΨ

end Submission.Obl.k4_terminal_label_saturation
