/- Adapted within this LOT tree from o190/x0633, b469254f8a8d614d595658e7ceb1bb13f4234bd2,
Submission/Obl/k4_pair_bin_atlas_assembly/FormatOps.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Rescale
import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatRule
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

/-!
# Closure properties of the frozen polynomial format `fmt`

All statements are for the `fmt` of `k4_quadratic_atlas_normalization.Interface`; they are
obtained from the accepted general rule `k4_coarsened_outer_horizon_composition.fmt_rule`
(an arbitrary Boolean rule on finitely many formatted sets) and its polynomial preimage lemma.
-/

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Submission.Obl.k4_quadratic_atlas_normalization MvPolynomial

variable {n : ℕ}

theorem fmt_rule' {D : ℕ} {ι : Type*} [Fintype ι] (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ)
    (hS : ∀ i, fmt n (H i) D (S i)) (rule : (ι → Prop) → Prop) :
    fmt n (∑ i, H i) D {x | rule (fun i => x ∈ S i)} :=
  Submission.Obl.k4_coarsened_outer_horizon_composition.fmt_rule S H hS rule

theorem fmt_mono' {H H' : ℝ} {D D' : ℕ} {S : Set (Fin n → ℝ)} (h : fmt n H D S)
    (hH : H ≤ H') (hD : D ≤ D') : fmt n H' D' S := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  exact ⟨m, hm.trans hH, p, fun i => (hp i).trans hD, b, hb⟩

theorem fmt_congr' {H : ℝ} {D : ℕ} {S S' : Set (Fin n → ℝ)} (h : fmt n H D S) (hS : S = S') :
    fmt n H D S' := hS ▸ h

theorem measurableSet_of_fmt {H : ℝ} {D : ℕ} {S : Set (Fin n → ℝ)} (h : fmt n H D S) :
    MeasurableSet S :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.measurableSet h

theorem fmt_nonneg (P : MvPolynomial (Fin n) ℝ) {D : ℕ} (hP : P.totalDegree ≤ D) :
    fmt n 1 D {x | 0 ≤ eval x P} := by
  refine ⟨1, by norm_num, fun _ => P, fun _ => hP, fun v => v 0, ?_⟩
  intro x
  simp

theorem fmt_inter {H H' : ℝ} {D : ℕ} {S T : Set (Fin n → ℝ)} (hS : fmt n H D S)
    (hT : fmt n H' D T) : fmt n (H + H') D (S ∩ T) := by
  have h := fmt_rule' (fun b : Bool => if b then S else T) (fun b => if b then H else H')
    (by intro b; cases b <;> simpa) (fun P => P true ∧ P false)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  exact fmt_congr' h (by ext x; simp)

theorem fmt_union {H H' : ℝ} {D : ℕ} {S T : Set (Fin n → ℝ)} (hS : fmt n H D S)
    (hT : fmt n H' D T) : fmt n (H + H') D (S ∪ T) := by
  have h := fmt_rule' (fun b : Bool => if b then S else T) (fun b => if b then H else H')
    (by intro b; cases b <;> simpa) (fun P => P true ∨ P false)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  exact fmt_congr' h (by ext x; simp)

/-- A filtered finite union of uniformly formatted sets. -/
theorem fmt_iUnion_filter {ι : Type*} [Fintype ι] {H : ℝ} {D : ℕ} (S : ι → Set (Fin n → ℝ))
    (hS : ∀ i, fmt n H D (S i)) (cond : ι → Prop) :
    fmt n (Fintype.card ι * H) D {x | ∃ i, cond i ∧ x ∈ S i} := by
  have h := fmt_rule' S (fun _ => H) hS (fun P => ∃ i, cond i ∧ P i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- A finite intersection of uniformly formatted sets. -/
theorem fmt_iInter {ι : Type*} [Fintype ι] {H : ℝ} {D : ℕ} (S : ι → Set (Fin n → ℝ))
    (hS : ∀ i, fmt n H D (S i)) :
    fmt n (Fintype.card ι * H) D {x | ∀ i, x ∈ S i} := by
  have h := fmt_rule' S (fun _ => H) hS (fun P => ∀ i, P i)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem fmt_abs_le (P : MvPolynomial (Fin n) ℝ) {D : ℕ} (hP : P.totalDegree ≤ D) (V : ℝ) :
    fmt n 2 D {x | |eval x P| ≤ V} := by
  have h1 := fmt_nonneg (C V - P) (D := D)
    ((totalDegree_sub _ _).trans (max_le (by simp) hP))
  have h2 := fmt_nonneg (C V + P) (D := D)
    ((totalDegree_add _ _).trans (max_le (by simp) hP))
  have h := fmt_inter h1 h2
  norm_num at h
  exact fmt_congr' h (by ext x; simp [abs_le]; constructor <;> intro h <;> constructor <;>
    linarith [h.1, h.2])

theorem fmt_le_abs (P : MvPolynomial (Fin n) ℝ) {D : ℕ} (hP : P.totalDegree ≤ D) (V : ℝ) :
    fmt n 2 D {x | V ≤ |eval x P|} := by
  have h1 := fmt_nonneg (P - C V) (D := D)
    ((totalDegree_sub _ _).trans (max_le hP (by simp)))
  have h2 := fmt_nonneg (-P - C V) (D := D)
    ((totalDegree_sub _ _).trans (max_le ((totalDegree_neg P).le.trans hP) (by simp)))
  have h := fmt_union h1 h2
  rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
  refine fmt_congr' h ?_
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, map_sub, eval_C, map_neg, le_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Preimage under an affine polynomial map. -/
theorem fmt_affine_preimage {m : ℕ} {H : ℝ} {D : ℕ} {S : Set (Fin n → ℝ)}
    (hS : fmt n H D S) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) :
    fmt m H D ((fun x i => eval x (f i)) ⁻¹' S) := by
  have h := Submission.Obl.k4_coarsened_outer_horizon_composition.fmt_polynomial_preimage
    hS f hf
  simp only [one_mul] at h
  exact h

/-- The affine coefficient map of a trajectory at a fixed time. -/
noncomputable def xSub (t : ℝ) : Fin 4 → MvPolynomial (Fin 6) ℝ :=
  ![C t, X 0 + C t * X 3, X 1 + C t * X 4, X 2 + C t * X 5]

theorem eval_xSub (i : ℕ) (v : Fin 6 → ℝ) (t : ℝ) :
    (fun k => eval v (xSub t k)) = x (i, v) t := by
  funext k
  fin_cases k <;> simp [xSub, x]

theorem totalDegree_xSub_le (t : ℝ) (k : Fin 4) : (xSub t k).totalDegree ≤ 1 := by
  have hX : ∀ e : Fin 6, (X e : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    fun e => (totalDegree_X e).le
  have hCX : ∀ (a : ℝ) (e : Fin 6), (C a * X e : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    fun a e => (totalDegree_mul _ _).trans (by simp)
  fin_cases k <;> simp only [xSub, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · simp
  all_goals exact (totalDegree_add _ _).trans (max_le (hX _) (hCX _ _))

/-- A condition on the trajectory point at a fixed time, as a condition on the six affine
parameters. -/
theorem fmt_trace {H : ℝ} {D : ℕ} {S : Set (Fin 4 → ℝ)} (hS : fmt 4 H D S) (i : ℕ) (t : ℝ) :
    fmt 6 H D {v : Fin 6 → ℝ | x (i, v) t ∈ S} := by
  have h := fmt_affine_preimage hS (xSub t) (totalDegree_xSub_le t)
  exact fmt_congr' h (by ext v; simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_xSub i v t])

/-- Fixing the last (time) coordinate of a seven-coordinate incidence set. -/
theorem fmt_fixed_time {H : ℝ} {D : ℕ} (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (i : ℕ) (t : ℝ)
    (hF : fmt 7 H D {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ F}) :
    fmt 6 H D {v : Fin 6 → ℝ | ((i, v), t) ∈ F} := by
  let q : Fin 7 → MvPolynomial (Fin 6) ℝ := Fin.snoc (fun z : Fin 6 => X z) (C t)
  have hq : ∀ k, (q k).totalDegree ≤ 1 := by
    intro k
    refine Fin.lastCases ?_ (fun z => ?_) k
    · show (q (Fin.last 6)).totalDegree ≤ 1
      simp only [q, Fin.snoc_last, totalDegree_C, zero_le]
    · simp [q]
  have h := fmt_affine_preimage hF q hq
  refine fmt_congr' h ?_
  ext v
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have h6 : eval v (q 6) = t := by
    show eval v (q (Fin.last 6)) = t
    simp only [q, Fin.snoc_last, eval_C]
  have hz : (fun z : Fin 6 => eval v (q z.castSucc)) = v := by
    funext z; simp [q]
  rw [h6, hz]

/-- A six-coordinate set as a cylinder in seven coordinates. -/
theorem fmt_cylinder {H : ℝ} {D : ℕ} {A : Set (Fin 6 → ℝ)} (h : fmt 6 H D A) :
    fmt 7 H D {r : Fin 7 → ℝ | (fun z : Fin 6 => r z.castSucc) ∈ A} := by
  have h' := fmt_affine_preimage h (fun z : Fin 6 => (X z.castSucc : MvPolynomial (Fin 7) ℝ))
    (fun z => (totalDegree_X _).le)
  exact fmt_congr' h' (by ext r; simp)

/-- The time coordinate in a closed interval. -/
theorem fmt_time_mem_Icc (lo hi : ℝ) :
    fmt 7 2 1 {r : Fin 7 → ℝ | r 6 ∈ Set.Icc lo hi} := by
  have h1 := fmt_nonneg (X 6 - C lo : MvPolynomial (Fin 7) ℝ) (D := 1)
    ((totalDegree_sub _ _).trans (max_le (totalDegree_X _).le (by simp)))
  have h2 := fmt_nonneg (C hi - X 6 : MvPolynomial (Fin 7) ℝ) (D := 1)
    ((totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_X _).le))
  have h := fmt_inter h1 h2
  norm_num at h
  exact fmt_congr' h (by ext r; simp [Set.mem_Icc])

end Submission.Obl.k4_matched_pair_representative_realization.Selection
