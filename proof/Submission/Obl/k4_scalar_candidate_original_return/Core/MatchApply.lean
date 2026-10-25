import Submission.Obl.k4_local_algebraic_graph_matching
import Submission.Obl.k4_two_color_matching

/-!
# The accepted local algebraic graph matching for two-variable quadratic graphs

Two-dimensional base cells `S q` (pairwise disjoint, inside the square of half-width
`1/4`), records `(q, c)` and pair weights `w m m' q c` between quadratic graphs `G m`.
Embedding the base in `ℝ³` with a dummy uniform coordinate, `o112` (applied to the accepted
two-colour matching `o015`) bounds the weight of pairs that are close on their cell but
separated somewhere on the disc of radius `1/2`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.MatchApply

open MeasureTheory Set MvPolynomial

/-- The closed square of half-width `a`. -/
def sq (a : ℝ) : Set (Fin 2 → ℝ) := {z | ∀ i, |z i| ≤ a}

/-- Two graphs are separated by `h` somewhere on the disc of radius `1/2`. -/
def Far (G G' : MvPolynomial (Fin 2) ℝ) (h : ℝ) : Prop :=
  ∃ z : Fin 2 → ℝ, z 0 ^ 2 + z 1 ^ 2 ≤ 1 / 4 ∧ h ≤ |eval z G - eval z G'|

/-- Total weight of separated pairs. -/
noncomputable def farMass {Q : Type} {n : ℕ} (G : Fin n → MvPolynomial (Fin 2) ℝ)
    (w : Fin n → Fin n → Q → ℤ → ENNReal) (h : ℝ) : ENNReal :=
  by
    classical
    exact ∑' q, ∑' c, ∑ m, ∑ m', if Far (G m) (G m') h then w m m' q c else 0

/-! ### Complexified graphs -/

/-- The complexified two-variable graph, as a function of the first two coordinates. -/
noncomputable def cF (g : MvPolynomial (Fin 2) ℝ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  eval (fun i : Fin 2 => z (Fin.castSucc i)) (MvPolynomial.map Complex.ofRealHom g)

/-- Its relation polynomial `w - g(z₀, z₁)`. -/
noncomputable def cP (g : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 4) ℂ :=
  X 3 - rename (fun i : Fin 2 => (Fin.castSucc (Fin.castSucc i) : Fin 4))
    (MvPolynomial.map Complex.ofRealHom g)

lemma totalDegree_map_le' {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial σ R) : (MvPolynomial.map f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset f p)

lemma cP_eval (g : MvPolynomial (Fin 2) ℝ) (v : Fin 3 → ℂ) (a : ℂ) :
    eval (Fin.snoc v a) (cP g) = a - eval (fun i : Fin 2 => v (Fin.castSucc i))
      (MvPolynomial.map Complex.ofRealHom g) := by
  unfold cP
  rw [map_sub, eval_X, eval_rename]
  have h3 : (3 : Fin 4) = Fin.last 3 := rfl
  rw [h3, Fin.snoc_last]
  have hcomp : (Fin.snoc v a ∘ fun i : Fin 2 => (Fin.castSucc (Fin.castSucc i) : Fin 4)) =
      fun i : Fin 2 => v (Fin.castSucc i) := by
    funext i
    simp only [Function.comp_apply, Fin.snoc_castSucc]
  rw [hcomp]

lemma cP_ne_zero (g : MvPolynomial (Fin 2) ℝ) : cP g ≠ 0 := by
  intro h
  have h1 := cP_eval g 0 (eval (fun i : Fin 2 => (0 : Fin 3 → ℂ) (Fin.castSucc i))
      (MvPolynomial.map Complex.ofRealHom g) + 1)
  rw [h, map_zero] at h1
  have : (0 : ℂ) = 1 := by rw [h1]; ring
  exact zero_ne_one this

lemma cP_totalDegree (g : MvPolynomial (Fin 2) ℝ) (hg : g.totalDegree ≤ 2) :
    (cP g).totalDegree ≤ 2 := by
  unfold cP
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]; norm_num
  · exact (totalDegree_rename_le _ _).trans ((totalDegree_map_le' _ _).trans hg)

lemma cF_relation (g : MvPolynomial (Fin 2) ℝ) (z : EuclideanSpace ℂ (Fin 3)) :
    eval (Fin.snoc (fun j : Fin 3 => z j) (cF g z)) (cP g) = 0 := by
  rw [cP_eval]
  unfold cF
  ring

/-- The coordinate projection to the first two coordinates, as a continuous linear map. -/
noncomputable def proj2 : EuclideanSpace ℂ (Fin 3) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin 2 => EuclideanSpace.proj (Fin.castSucc i)

lemma cF_differentiable (g : MvPolynomial (Fin 2) ℝ) :
    DifferentiableOn ℂ (cF g) (Metric.ball 0 4) := by
  have h := AnalyticOnNhd.eval_continuousLinearMap proj2 (MvPolynomial.map Complex.ofRealHom g)
  have heq : (fun x => eval (proj2 x) (MvPolynomial.map Complex.ofRealHom g)) = cF g := by
    funext z
    rfl
  rw [heq] at h
  exact (h.differentiableOn).mono (subset_univ _)

lemma cF_emb (g : MvPolynomial (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    cF g (WithLp.toLp 2 (fun i => (x i : ℂ))) =
      ((eval (fun i : Fin 2 => x (Fin.castSucc i)) g : ℝ) : ℂ) := by
  unfold cF
  rw [show (((eval (fun i : Fin 2 => x (Fin.castSucc i)) g : ℝ) : ℂ)) =
      Complex.ofRealHom (eval (fun i : Fin 2 => x (Fin.castSucc i)) g) from rfl, map_eval]
  congr 1


/-! ### The three-dimensional base -/

/-- Volume-preserving coordinates: the last coordinate, then the first two. -/
noncomputable def e3 : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2))

lemma e3_mp : MeasurePreserving e3 volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))

lemma e3_apply (x : EuclideanSpace ℝ (Fin 3)) :
    e3 x = (x (Fin.last 2), fun j : Fin 2 => x (Fin.castSucc j)) := by
  simp only [e3, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_symm_mk]
  refine Prod.ext rfl ?_
  funext j
  show x.ofLp ((Fin.last 2).succAbove j) = x.ofLp j.castSucc
  rw [Fin.succAbove_last]

/-- The 3-D cell over a 2-D cell, with a dummy last coordinate. -/
def box (S : Set (Fin 2 → ℝ)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  e3 ⁻¹' (Icc (-(1 / 8 : ℝ)) (1 / 8) ×ˢ S)

lemma box_measurable {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) : MeasurableSet (box S) :=
  e3.measurable (measurableSet_Icc.prod hS)

lemma volume_box {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) :
    volume (box S) = ENNReal.ofReal (1 / 4) * volume S := by
  rw [box, e3_mp.measure_preimage (measurableSet_Icc.prod hS).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  norm_num

lemma mem_box {S : Set (Fin 2 → ℝ)} {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ box S ↔ x (Fin.last 2) ∈ Icc (-(1 / 8 : ℝ)) (1 / 8) ∧
      (fun j : Fin 2 => x (Fin.castSucc j)) ∈ S := by
  rw [box, mem_preimage, e3_apply, mem_prod]

lemma box_disjoint {S S' : Set (Fin 2 → ℝ)} (h : Disjoint S S') : Disjoint (box S) (box S') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact Set.disjoint_left.mp h (mem_box.mp hx).2 (mem_box.mp hx').2

lemma norm_le_of_mem_box {S : Set (Fin 2 → ℝ)} (hS : S ⊆ sq (1 / 4))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ box S) : ‖x‖ ≤ 1 / 2 := by
  obtain ⟨h2, hS'⟩ := mem_box.mp hx
  have h01 := hS hS'
  have hx0 : |x 0| ≤ 1 / 4 := h01 0
  have hx1 : |x 1| ≤ 1 / 4 := h01 1
  have hx2 : |x 2| ≤ 1 / 8 := abs_le.mpr ⟨h2.1, h2.2⟩
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have hsq : ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 + ‖x.ofLp 2‖ ^ 2 ≤ (1 / 2) ^ 2 := by
    simp only [Real.norm_eq_abs]
    have a0 : |x.ofLp 0| ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx0 2
    have a1 : |x.ofLp 1| ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx1 2
    have a2 : |x.ofLp 2| ^ 2 ≤ (1 / 8) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx2 2
    nlinarith
  calc √(‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 + ‖x.ofLp 2‖ ^ 2) ≤ √((1 / 2) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

lemma abs_coord_le_norm (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ‖x.ofLp i‖ ^ 2 ≤ ∑ j, ‖x.ofLp j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x.ofLp j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc |x i| = √(‖x.ofLp i‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]
    _ ≤ √(∑ j, ‖x.ofLp j‖ ^ 2) := Real.sqrt_le_sqrt h

/-- Uniform probability on the box over `S`. -/
noncomputable def U (S : Set (Fin 2 → ℝ)) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  (volume (box S))⁻¹ • volume.restrict (box S)

lemma U_apply {S : Set (Fin 2 → ℝ)} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) : U S A = (volume (box S))⁻¹ * volume (A ∩ box S) := by
  rw [U, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]

lemma U_univ {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) (h0 : 0 < volume S)
    (hfin : volume S < ⊤) : U S univ = 1 := by
  rw [U_apply MeasurableSet.univ, univ_inter]
  apply ENNReal.inv_mul_cancel
  · rw [volume_box hS]
    exact mul_ne_zero (by norm_num) h0.ne'
  · rw [volume_box hS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne

lemma inv_mul_self_le_one (a : ENNReal) : a⁻¹ * a ≤ 1 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  rcases eq_or_ne a ⊤ with h' | h'
  · simp [h']
  · rw [ENNReal.inv_mul_cancel h h']

local instance U_finite (S : Set (Fin 2 → ℝ)) : IsFiniteMeasure (U S) := by
  constructor
  rw [U_apply MeasurableSet.univ, univ_inter]
  exact (inv_mul_self_le_one _).trans_lt ENNReal.one_lt_top

lemma U_compl_box {S : Set (Fin 2 → ℝ)} (hS : MeasurableSet S) : U S (box S)ᶜ = 0 := by
  rw [U_apply (box_measurable hS).compl, compl_inter_self, measure_empty, mul_zero]


lemma norm_cF_sub (g g' : MvPolynomial (Fin 2) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖cF g (WithLp.toLp 2 (fun i => (x i : ℂ))) - cF g' (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ =
      |eval (fun j : Fin 2 => x (Fin.castSucc j)) g -
        eval (fun j : Fin 2 => x (Fin.castSucc j)) g'| := by
  rw [cF_emb, cF_emb, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma exists_lift (z : Fin 2 → ℝ) (hz : z 0 ^ 2 + z 1 ^ 2 ≤ 1 / 4) :
    ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 ∧ (fun j : Fin 2 => x (Fin.castSucc j)) = z := by
  refine ⟨WithLp.toLp 2 (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ), ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    have h0 : (WithLp.toLp 2 (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ)).ofLp 0 = z 0 := rfl
    have h1 : (WithLp.toLp 2 (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ)).ofLp 1 = z 1 := rfl
    have h2 : (WithLp.toLp 2 (Fin.snoc z (0 : ℝ) : Fin 3 → ℝ)).ofLp 2 = 0 := rfl
    rw [h0, h1, h2]
    simp only [Real.norm_eq_abs, sq_abs, norm_zero]
    calc √(z 0 ^ 2 + z 1 ^ 2 + 0 ^ 2) ≤ √((1 / 2) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  · funext j
    fin_cases j <;> rfl

/-! ### The pair measure -/

section Pair

variable {Q : Type} [Countable Q] {n : ℕ} (G : Fin n → MvPolynomial (Fin 2) ℝ)
  (w : Fin n → Fin n → Q → ℤ → ENNReal) (h : ℝ) (S : Q → Set (Fin 2 → ℝ))

/-- The weight of a separated pair on a record. -/
noncomputable def coef (q : Q) (c : ℤ) (m m' : Fin n) : ENNReal :=
  by
    classical
    exact if Far (G m) (G m') h then w m m' q c else 0

omit [Countable Q] in
lemma farMass_eq : farMass G w h = ∑' q, ∑' c, ∑ m, ∑ m', coef G w h q c m m' := rfl

omit [Countable Q] in
lemma coef_le (q : Q) (c : ℤ) (m m' : Fin n) : coef G w h q c m m' ≤ w m m' q c := by
  unfold coef
  split_ifs <;> simp

/-- Separated pairs, each spread uniformly over the box above its cell. -/
noncomputable def pairMeasure : Measure ((Fin n × Fin n) × EuclideanSpace ℝ (Fin 3)) :=
  Measure.sum fun q : Q => Measure.sum fun c : ℤ =>
    ∑ m, ∑ m', coef G w h q c m m' • (Measure.dirac (m, m')).prod (U (S q))

omit [Countable Q] in
lemma pairMeasure_apply {A : Set ((Fin n × Fin n) × EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) :
    pairMeasure G w h S A = ∑' q, ∑' c, ∑ m, ∑ m',
      coef G w h q c m m' * ((Measure.dirac (m, m')).prod (U (S q))) A := by
  rw [pairMeasure, Measure.sum_apply _ hA]
  congr 1
  funext q
  rw [Measure.sum_apply _ hA]
  congr 1
  funext c
  rw [Measure.finsetSum_apply]
  congr 1
  funext m
  rw [Measure.finsetSum_apply]
  congr 1

lemma dirac_prod_apply (x : Fin n × Fin n) (ν : Measure (EuclideanSpace ℝ (Fin 3)))
    [IsFiniteMeasure ν] {A : Set ((Fin n × Fin n) × EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) :
    ((Measure.dirac x).prod ν) A = ν (Prod.mk x ⁻¹' A) := by
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hA]

omit [Countable Q] in
lemma pairMeasure_univ (hSm : ∀ q, MeasurableSet (S q)) (hSpos : ∀ q, 0 < volume (S q))
    (hSfin : ∀ q, volume (S q) < ⊤) : pairMeasure G w h S univ = farMass G w h := by
  rw [pairMeasure_apply G w h S MeasurableSet.univ, farMass_eq]
  congr 1; funext q; congr 1; funext c; congr 1; funext m; congr 1; funext m'
  rw [dirac_prod_apply _ _ MeasurableSet.univ, preimage_univ, U_univ (hSm q) (hSpos q) (hSfin q),
    mul_one]

lemma four_mul (b : ENNReal) (h0 : b ≠ 0) (htop : b ≠ ⊤) :
    b * (ENNReal.ofReal (1 / 4) * b)⁻¹ = 4 := by
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm (ENNReal.ofReal _)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  norm_num

/-- Marginal bound in the first colour. -/
lemma pairMeasure_marg₁ (Λ : ℝ) (hSm : ∀ q, MeasurableSet (S q))
    (hSpos : ∀ q, 0 < volume (S q)) (hSfin : ∀ q, volume (S q) < ⊤)
    (hSdisj : Pairwise (fun q q' => Disjoint (S q) (S q')))
    (hmarg : ∀ m q, ∑' c, ∑ m', w m m' q c ≤ ENNReal.ofReal Λ * volume (S q))
    (i : Fin n) {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : MeasurableSet V) :
    pairMeasure G w h S {p | p.1.1 = i ∧ p.2 ∈ V} ≤ 4 * ENNReal.ofReal Λ * volume V := by
  have hA : MeasurableSet {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) | p.1.1 = i ∧ p.2 ∈ V} :=
    (measurableSet_eq_fun measurable_fst.fst measurable_const).inter (measurable_snd hV)
  rw [pairMeasure_apply G w h S hA]
  have hterm : ∀ q c, (∑ m, ∑ m', coef G w h q c m m' *
      ((Measure.dirac (m, m')).prod (U (S q))) {p | p.1.1 = i ∧ p.2 ∈ V}) =
      ∑ m', coef G w h q c i m' * U (S q) V := by
    intro q c
    rw [Fintype.sum_eq_single i]
    · congr 1
      funext m'
      rw [dirac_prod_apply _ _ hA]
      congr 2
      ext x
      simp
    · intro m hm
      apply Finset.sum_eq_zero
      intro m' _
      rw [dirac_prod_apply _ _ hA]
      have : Prod.mk (m, m') ⁻¹' {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) |
          p.1.1 = i ∧ p.2 ∈ V} = ∅ := by
        ext x
        simp [hm]
      rw [this, measure_empty, mul_zero]
  simp_rw [hterm]
  calc ∑' q, ∑' c, ∑ m', coef G w h q c i m' * U (S q) V
      ≤ ∑' q, ∑' c, ∑ m', w i m' q c * U (S q) V := by
        gcongr with q c m'
        exact coef_le G w h q c i m'
    _ = ∑' q, (∑' c, ∑ m', w i m' q c) * U (S q) V := by
        congr 1; funext q
        rw [← ENNReal.tsum_mul_right]
        congr 1; funext c
        rw [Finset.sum_mul]
    _ ≤ ∑' q, (ENNReal.ofReal Λ * volume (S q)) * U (S q) V := by
        gcongr with q
        exact hmarg i q
    _ = ∑' q, 4 * ENNReal.ofReal Λ * volume (V ∩ box (S q)) := by
        congr 1; funext q
        rw [U_apply hV, volume_box (hSm q)]
        have := four_mul (volume (S q)) (hSpos q).ne' (hSfin q).ne
        calc ENNReal.ofReal Λ * volume (S q) *
              ((ENNReal.ofReal (1 / 4) * volume (S q))⁻¹ * volume (V ∩ box (S q)))
            = ENNReal.ofReal Λ * (volume (S q) * (ENNReal.ofReal (1 / 4) * volume (S q))⁻¹) *
              volume (V ∩ box (S q)) := by ring
          _ = _ := by rw [this]; ring
    _ = 4 * ENNReal.ofReal Λ * volume (⋃ q, V ∩ box (S q)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · intro q q' hqq'
          exact ((box_disjoint (hSdisj hqq')).mono inter_subset_right inter_subset_right)
        · intro q
          exact hV.inter (box_measurable (hSm q))
    _ ≤ 4 * ENNReal.ofReal Λ * volume V := by
        gcongr
        exact iUnion_subset fun q => inter_subset_left

/-- Marginal bound in the second colour. -/
lemma pairMeasure_marg₂ (Λ : ℝ) (hSm : ∀ q, MeasurableSet (S q))
    (hSpos : ∀ q, 0 < volume (S q)) (hSfin : ∀ q, volume (S q) < ⊤)
    (hSdisj : Pairwise (fun q q' => Disjoint (S q) (S q')))
    (hmarg : ∀ m' q, ∑' c, ∑ m, w m m' q c ≤ ENNReal.ofReal Λ * volume (S q))
    (i : Fin n) {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : MeasurableSet V) :
    pairMeasure G w h S {p | p.1.2 = i ∧ p.2 ∈ V} ≤ 4 * ENNReal.ofReal Λ * volume V := by
  have hA : MeasurableSet {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) | p.1.2 = i ∧ p.2 ∈ V} :=
    (measurableSet_eq_fun measurable_fst.snd measurable_const).inter (measurable_snd hV)
  rw [pairMeasure_apply G w h S hA]
  have hterm : ∀ q c, (∑ m, ∑ m', coef G w h q c m m' *
      ((Measure.dirac (m, m')).prod (U (S q))) {p | p.1.2 = i ∧ p.2 ∈ V}) =
      ∑ m, coef G w h q c m i * U (S q) V := by
    intro q c
    apply Finset.sum_congr rfl
    intro m _
    rw [Fintype.sum_eq_single i]
    · rw [dirac_prod_apply _ _ hA]
      congr 2
      ext x
      simp
    · intro m' hm'
      rw [dirac_prod_apply _ _ hA]
      have : Prod.mk (m, m') ⁻¹' {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) |
          p.1.2 = i ∧ p.2 ∈ V} = ∅ := by
        ext x
        simp [hm']
      rw [this, measure_empty, mul_zero]
  simp_rw [hterm]
  calc ∑' q, ∑' c, ∑ m, coef G w h q c m i * U (S q) V
      ≤ ∑' q, ∑' c, ∑ m, w m i q c * U (S q) V := by
        gcongr with q c m
        exact coef_le G w h q c m i
    _ = ∑' q, (∑' c, ∑ m, w m i q c) * U (S q) V := by
        congr 1; funext q
        rw [← ENNReal.tsum_mul_right]
        congr 1; funext c
        rw [Finset.sum_mul]
    _ ≤ ∑' q, (ENNReal.ofReal Λ * volume (S q)) * U (S q) V := by
        gcongr with q
        exact hmarg i q
    _ = ∑' q, 4 * ENNReal.ofReal Λ * volume (V ∩ box (S q)) := by
        congr 1; funext q
        rw [U_apply hV, volume_box (hSm q)]
        have := four_mul (volume (S q)) (hSpos q).ne' (hSfin q).ne
        calc ENNReal.ofReal Λ * volume (S q) *
              ((ENNReal.ofReal (1 / 4) * volume (S q))⁻¹ * volume (V ∩ box (S q)))
            = ENNReal.ofReal Λ * (volume (S q) * (ENNReal.ofReal (1 / 4) * volume (S q))⁻¹) *
              volume (V ∩ box (S q)) := by ring
          _ = _ := by rw [this]; ring
    _ = 4 * ENNReal.ofReal Λ * volume (⋃ q, V ∩ box (S q)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion]
        · intro q q' hqq'
          exact ((box_disjoint (hSdisj hqq')).mono inter_subset_right inter_subset_right)
        · intro q
          exact hV.inter (box_measurable (hSm q))
    _ ≤ 4 * ENNReal.ofReal Λ * volume V := by
        gcongr
        exact iUnion_subset fun q => inter_subset_left

lemma volume_sq_lt_top : volume (sq (1 / 4)) < ⊤ := by
  have hsub : sq (1 / 4) ⊆ Icc (fun _ : Fin 2 => -(1 / 4 : ℝ)) (fun _ => 1 / 4) := by
    intro z hz
    exact ⟨fun i => (abs_le.mp (hz i)).1, fun i => (abs_le.mp (hz i)).2⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [Real.volume_Icc_pi]
  exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top

/-- The separated mass is finite. -/
lemma farMass_lt_top (Λ : ℝ) (hSm : ∀ q, MeasurableSet (S q))
    (hSsub : ∀ q, S q ⊆ sq (1 / 4))
    (hSdisj : Pairwise (fun q q' => Disjoint (S q) (S q')))
    (hmarg : ∀ m q, ∑' c, ∑ m', w m m' q c ≤ ENNReal.ofReal Λ * volume (S q)) :
    farMass G w h < ⊤ := by
  rw [farMass_eq]
  calc ∑' q, ∑' c, ∑ m, ∑ m', coef G w h q c m m'
      ≤ ∑' q, ∑' c, ∑ m, ∑ m', w m m' q c := by
        gcongr with q c m m'
        exact coef_le G w h q c m m'
    _ = ∑' q, ∑ m, ∑' c, ∑ m', w m m' q c := by
        congr 1; funext q
        exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑' q, ∑ _m : Fin n, ENNReal.ofReal Λ * volume (S q) := by
        gcongr with q m
        exact hmarg m q
    _ = (n : ENNReal) * ENNReal.ofReal Λ * ∑' q, volume (S q) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.tsum_mul_left]
        congr 1; funext q
        ring
    _ = (n : ENNReal) * ENNReal.ofReal Λ * volume (⋃ q, S q) := by
        rw [measure_iUnion hSdisj hSm]
    _ ≤ (n : ENNReal) * ENNReal.ofReal Λ * volume (sq (1 / 4)) := by
        gcongr
        exact iUnion_subset hSsub
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top n)
        ENNReal.ofReal_lt_top) volume_sq_lt_top

/-- The incidences carried by separated pairs: the pair label times the box of its cell. -/
def carrier : Set ((Fin n × Fin n) × EuclideanSpace ℝ (Fin 3)) :=
  ⋃ q, ⋃ c : ℤ, ⋃ m, ⋃ m', {p | coef G w h q c m m' ≠ 0 ∧ p.1 = (m, m') ∧ p.2 ∈ box (S q)}

lemma carrier_measurable (hSm : ∀ q, MeasurableSet (S q)) :
    MeasurableSet (carrier G w h S) := by
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun c => MeasurableSet.iUnion
    fun m => MeasurableSet.iUnion fun m' => ?_
  by_cases hc : coef G w h q c m m' ≠ 0
  · have : {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) | coef G w h q c m m' ≠ 0 ∧
        p.1 = (m, m') ∧ p.2 ∈ box (S q)} = {(m, m')} ×ˢ box (S q) := by
      ext p
      simp [hc]
    rw [this]
    exact (measurableSet_singleton _).prod (box_measurable (hSm q))
  · have : {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) | coef G w h q c m m' ≠ 0 ∧
        p.1 = (m, m') ∧ p.2 ∈ box (S q)} = ∅ := by
      ext p
      simp only [ne_eq, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h'
      exact absurd h' hc
    rw [this]
    exact MeasurableSet.empty

lemma pairMeasure_compl_carrier (hSm : ∀ q, MeasurableSet (S q)) :
    pairMeasure G w h S (carrier G w h S)ᶜ = 0 := by
  rw [pairMeasure_apply G w h S (carrier_measurable G w h S hSm).compl]
  refine ENNReal.tsum_eq_zero.mpr fun q => ENNReal.tsum_eq_zero.mpr fun c =>
    Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun m' _ => ?_
  by_cases hc : coef G w h q c m m' = 0
  · rw [hc, zero_mul]
  · rw [dirac_prod_apply _ _ (carrier_measurable G w h S hSm).compl]
    have hsub : Prod.mk (m, m') ⁻¹' (carrier G w h S)ᶜ ⊆ (box (S q))ᶜ := by
      intro x hx hxb
      apply hx
      exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨m, mem_iUnion.mpr
        ⟨m', hc, rfl, hxb⟩⟩⟩⟩
    rw [measure_mono_null hsub (U_compl_box (hSm q)), mul_zero]

end Pair


theorem matching_far_mass (d₀ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R ε : ℝ, R₀ ≤ R → 0 < ε → ε ≤ ε₀ →
      ∀ {Q : Type} [Countable Q] (n : ℕ) (G : Fin n → MvPolynomial (Fin 2) ℝ)
        (S : Q → Set (Fin 2 → ℝ)) (w : Fin n → Fin n → Q → ℤ → ENNReal) (Λ : ℝ),
        0 ≤ Λ →
        (n : ℝ) ≤ R ^ (d₀ + ε) →
        (∀ m, (G m).totalDegree ≤ 2) →
        (∀ m, ∀ z ∈ sq 1, |eval z (G m)| ≤ R ^ ε) →
        (∀ q, MeasurableSet (S q)) → (∀ q, S q ⊆ sq (1 / 4)) →
        Pairwise (fun q q' => Disjoint (S q) (S q')) →
        (∀ q, 0 < volume (S q)) → (∀ q, volume (S q) < ⊤) →
        (∀ m m' q c, w m m' q c ≠ 0 → ∀ z ∈ S q,
            |eval z (G m) - eval z (G m')| ≤ R ^ (-1 + ε)) →
        (∀ m q, ∑' c, ∑ m', w m m' q c ≤ ENNReal.ofReal Λ * volume (S q)) →
        (∀ m' q, ∑' c, ∑ m, w m m' q c ≤ ENNReal.ofReal Λ * volume (S q)) →
        farMass G w (R ^ (-ε)) ≤ ENNReal.ofReal (4 * Λ * n * R ^ (-ε)) := by
  classical
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmain⟩ :=
    Submission.k4_local_algebraic_graph_matching Submission.k4_two_color_matching 2 d₀ hd₀ hd₁
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R ε hR hε hεle Q _ n G S w Λ hΛ hn hG hGb hSm hSsub hSdisj hSpos hSfin hclose
    hmarg₁ hmarg₂
  by_contra hcon
  have hlt : ENNReal.ofReal (4 * Λ * n * R ^ (-ε)) < farMass G w (R ^ (-ε)) := not_le.mp hcon
  have hRpos : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hB0 : farMass G w (R ^ (-ε)) ≠ 0 := ne_of_gt (lt_of_le_of_lt (by positivity) hlt)
  have hBtop : farMass G w (R ^ (-ε)) ≠ ⊤ :=
    (farMass_lt_top G w _ S Λ hSm hSsub hSdisj hmarg₁).ne
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      apply hB0
      subst h0
      rw [farMass_eq]
      simp
    · exact h0
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  set B := farMass G w (R ^ (-ε)) with hB
  set μ := B⁻¹ • pairMeasure G w (R ^ (-ε)) S with hμ
  have hμuniv : μ univ = 1 := by
    rw [hμ, Measure.smul_apply, pairMeasure_univ G w _ S hSm hSpos hSfin, smul_eq_mul,
      ENNReal.inv_mul_cancel hB0 hBtop]
  have hconst : B⁻¹ * (4 * ENNReal.ofReal Λ) ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) := by
    have h4 : 4 * ENNReal.ofReal Λ = ENNReal.ofReal (4 * Λ * n * R ^ (-ε)) *
        ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have hRe : R ^ ε ≠ 0 := (Real.rpow_pos_of_pos hRpos ε).ne'
      have : 4 * Λ * n * R ^ (-ε) * (R ^ ε * (1 / (n : ℝ))) = 4 * Λ := by
        rw [Real.rpow_neg hRpos.le]
        field_simp
      rw [this, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc B⁻¹ * (4 * ENNReal.ofReal Λ)
        = B⁻¹ * (ENNReal.ofReal (4 * Λ * n * R ^ (-ε)) *
            ENNReal.ofReal (R ^ ε * (1 / (n : ℝ)))) := by rw [h4]
      _ ≤ B⁻¹ * (B * ENNReal.ofReal (R ^ ε * (1 / (n : ℝ)))) := by gcongr
      _ = ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hB0 hBtop, one_mul]
  have hmargμ₁ : ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet V →
      μ {p | p.1.1 = i ∧ p.2 ∈ V} ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume V := by
    intro i V hV
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    calc B⁻¹ * pairMeasure G w (R ^ (-ε)) S {p | p.1.1 = i ∧ p.2 ∈ V}
        ≤ B⁻¹ * (4 * ENNReal.ofReal Λ * volume V) := by
          gcongr
          exact pairMeasure_marg₁ G w _ S Λ hSm hSpos hSfin hSdisj hmarg₁ i hV
      _ = B⁻¹ * (4 * ENNReal.ofReal Λ) * volume V := by ring
      _ ≤ _ := by gcongr
  have hmargμ₂ : ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet V →
      μ {p | p.1.2 = i ∧ p.2 ∈ V} ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume V := by
    intro i V hV
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    calc B⁻¹ * pairMeasure G w (R ^ (-ε)) S {p | p.1.2 = i ∧ p.2 ∈ V}
        ≤ B⁻¹ * (4 * ENNReal.ofReal Λ * volume V) := by
          gcongr
          exact pairMeasure_marg₂ G w _ S Λ hSm hSpos hSfin hSdisj hmarg₂ i hV
      _ = B⁻¹ * (4 * ENNReal.ofReal Λ) * volume V := by ring
      _ ≤ _ := by gcongr
  have hf : ∀ i : Fin n, cP (G i) ≠ 0 ∧ (cP (G i)).totalDegree ≤ 2 ∧
      DifferentiableOn ℂ (cF (G i)) (Metric.ball 0 4) ∧
      (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (Fin.snoc (fun j : Fin 3 => z j) (cF (G i) z)) (cP (G i)) = 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
        (cF (G i) (WithLp.toLp 2 (fun j => (x j : ℂ)))).im = 0 ∧
        ‖cF (G i) (WithLp.toLp 2 (fun j => (x j : ℂ))) - (fun _ => (0 : ℂ)) x‖ ≤ 1 * R ^ ε := by
    intro i
    refine ⟨cP_ne_zero _, cP_totalDegree _ (hG i), cF_differentiable _,
      fun z _ => cF_relation _ z, fun x hx => ⟨?_, ?_⟩⟩
    · rw [cF_emb]
      exact Complex.ofReal_im _
    · rw [cF_emb, sub_zero, Complex.norm_real, Real.norm_eq_abs, one_mul]
      apply hGb i
      intro j
      exact (abs_coord_le_norm x _).trans hx
  have hπ : ∀ i : Fin n, (0 : ℝ) ≤ (fun _ => 1 / (n : ℝ)) i := fun _ => by positivity
  have hsum : (∑ i : Fin n, (fun _ => 1 / (n : ℝ)) i) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hmass : ENNReal.ofReal (R ^ (-ε)) ≤ μ univ := by
    rw [hμuniv]
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith))
  have hcarrier : carrier G w (R ^ (-ε)) S ⊆ {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) |
      ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖cF (G p.1.1) (WithLp.toLp 2 (fun j => (p.2 j : ℂ))) -
        cF (G p.1.2) (WithLp.toLp 2 (fun j => (p.2 j : ℂ)))‖ ≤ 1 * R ^ (-1 + ε) ∧
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧
        1 * R ^ (-ε) ≤ ‖cF (G p.1.1) (WithLp.toLp 2 (fun j => (x j : ℂ))) -
          cF (G p.1.2) (WithLp.toLp 2 (fun j => (x j : ℂ)))‖} := by
    intro p hp
    obtain ⟨q, c, m, m', hc, hp1, hp2⟩ := by
      simpa only [carrier, mem_iUnion, mem_ofPred_eq] using hp
    have hFw : Far (G m) (G m') (R ^ (-ε)) ∧ w m m' q c ≠ 0 := by
      unfold coef at hc
      split_ifs at hc with hFar
      · exact ⟨hFar, hc⟩
      · exact absurd rfl hc
    obtain ⟨⟨z, hz, hfar⟩, hw⟩ := hFw
    rw [Set.mem_ofPred_eq, hp1]
    refine ⟨norm_le_of_mem_box (hSsub q) hp2, ?_, ?_⟩
    · rw [norm_cF_sub, one_mul]
      exact hclose m m' q c hw _ (mem_box.mp hp2).2
    · obtain ⟨x, hx, hxz⟩ := exists_lift z hz
      refine ⟨x, hx, ?_⟩
      rw [norm_cF_sub, one_mul, hxz]
      exact hfar
  have hconc : μ {p : (Fin n × Fin n) × EuclideanSpace ℝ (Fin 3) |
      ‖p.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖cF (G p.1.1) (WithLp.toLp 2 (fun j => (p.2 j : ℂ))) -
        cF (G p.1.2) (WithLp.toLp 2 (fun j => (p.2 j : ℂ)))‖ ≤ 1 * R ^ (-1 + ε) ∧
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧
        1 * R ^ (-ε) ≤ ‖cF (G p.1.1) (WithLp.toLp 2 (fun j => (x j : ℂ))) -
          cF (G p.1.2) (WithLp.toLp 2 (fun j => (x j : ℂ)))‖}ᶜ = 0 := by
    rw [hμ, Measure.smul_apply, smul_eq_mul,
      measure_mono_null (compl_subset_compl.mpr hcarrier)
        (pairMeasure_compl_carrier G w _ S hSm), mul_zero]
  exact hmain R 1 ε hR one_pos hε hεle n n (fun i => cF (G i)) (fun i => cF (G i))
    (fun i => cP (G i)) (fun i => cP (G i)) (fun _ => 0) (fun _ => 1 / (n : ℝ))
    (fun _ => 1 / (n : ℝ)) μ hn hn hf hf hπ hπ hsum hsum hmass hμuniv.le hmargμ₁ hmargμ₂ hconc

end Submission.Obl.k4_scalar_candidate_original_return.MatchApply
