import Submission.Obl.k4_scalar_conditional_crop_worlds.Formats

/-!
# Closure properties of the polynomial sign format

`Format n B D A` says that `A` is cut out by at most `B` polynomials of degree at most `D` with
coefficients bounded by `B`, through an arbitrary set of sign vectors. The format is stable
under finite intersections and unions (the bounds add up), and every affine half-space in one
coordinate is in the format.
-/

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

open MvPolynomial Set

noncomputable section

lemma Format.nonneg {n : ℕ} {B : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : Format n B D A) :
    0 ≤ B := by
  obtain ⟨k, hk, -⟩ := h
  exact (Nat.cast_nonneg k).trans hk

lemma Format.congr {n : ℕ} {B : ℝ} {D : ℕ} {A A' : Set (Fin n → ℝ)} (h : Format n B D A)
    (hA : A = A') : Format n B D A' := hA ▸ h

lemma Format.univ (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (D : ℕ) : Format n B D Set.univ := by
  refine ⟨0, by simpa using hB, Fin.elim0, fun j => j.elim0, Set.univ, ?_⟩
  ext x
  simp

lemma Format.empty (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (D : ℕ) : Format n B D ∅ := by
  refine ⟨0, by simpa using hB, Fin.elim0, fun j => j.elim0, ∅, ?_⟩
  ext x
  simp

lemma Format.inter {n : ℕ} {B₁ B₂ : ℝ} {D : ℕ} {A₁ A₂ : Set (Fin n → ℝ)}
    (h₁ : Format n B₁ D A₁) (h₂ : Format n B₂ D A₂) : Format n (B₁ + B₂) D (A₁ ∩ A₂) := by
  have hB₁ := h₁.nonneg
  have hB₂ := h₂.nonneg
  obtain ⟨k₁, hk₁, p₁, hp₁, S₁, rfl⟩ := h₁
  obtain ⟨k₂, hk₂, p₂, hp₂, S₂, rfl⟩ := h₂
  refine ⟨k₁ + k₂, by push_cast; linarith, Fin.append p₁ p₂, ?_,
    {s | (fun i => s (Fin.castAdd k₂ i)) ∈ S₁ ∧ (fun i => s (Fin.natAdd k₁ i)) ∈ S₂}, ?_⟩
  · intro j
    induction j using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      exact ⟨(hp₁ i).1, fun b => ((hp₁ i).2 b).trans (by linarith)⟩
    | right i =>
      rw [Fin.append_right]
      exact ⟨(hp₂ i).1, fun b => ((hp₂ i).2 b).trans (by linarith)⟩
  · ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Fin.append_left, Fin.append_right]

lemma Format.union {n : ℕ} {B₁ B₂ : ℝ} {D : ℕ} {A₁ A₂ : Set (Fin n → ℝ)}
    (h₁ : Format n B₁ D A₁) (h₂ : Format n B₂ D A₂) : Format n (B₁ + B₂) D (A₁ ∪ A₂) := by
  have hB₁ := h₁.nonneg
  have hB₂ := h₂.nonneg
  obtain ⟨k₁, hk₁, p₁, hp₁, S₁, rfl⟩ := h₁
  obtain ⟨k₂, hk₂, p₂, hp₂, S₂, rfl⟩ := h₂
  refine ⟨k₁ + k₂, by push_cast; linarith, Fin.append p₁ p₂, ?_,
    {s | (fun i => s (Fin.castAdd k₂ i)) ∈ S₁ ∨ (fun i => s (Fin.natAdd k₁ i)) ∈ S₂}, ?_⟩
  · intro j
    induction j using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      exact ⟨(hp₁ i).1, fun b => ((hp₁ i).2 b).trans (by linarith)⟩
    | right i =>
      rw [Fin.append_right]
      exact ⟨(hp₂ i).1, fun b => ((hp₂ i).2 b).trans (by linarith)⟩
  · ext x
    simp only [mem_union, mem_ofPred_eq, Fin.append_left, Fin.append_right]

lemma Format.iInter_fin {n D : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    ∀ (m : ℕ) (A : Fin m → Set (Fin n → ℝ)), (∀ i, Format n B D (A i)) →
      Format n (m * B) D (⋂ i, A i)
  | 0, A, _ => by
    simpa using Format.univ n le_rfl D
  | m + 1, A, h => by
    have := (h 0).inter (Format.iInter_fin hB m (fun i => A i.succ) (fun i => h i.succ))
    rw [show ((m + 1 : ℕ) : ℝ) * B = B + m * B by push_cast; ring]
    refine this.congr ?_
    ext x
    simp only [mem_inter_iff, mem_iInter]
    exact (Fin.forall_fin_succ (P := fun i => x ∈ A i)).symm

lemma Format.iUnion_fin {n D : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    ∀ (m : ℕ) (A : Fin m → Set (Fin n → ℝ)), (∀ i, Format n B D (A i)) →
      Format n (m * B) D (⋃ i, A i)
  | 0, A, _ => by
    simpa using Format.empty n le_rfl D
  | m + 1, A, h => by
    have := (h 0).union (Format.iUnion_fin hB m (fun i => A i.succ) (fun i => h i.succ))
    rw [show ((m + 1 : ℕ) : ℝ) * B = B + m * B by push_cast; ring]
    refine this.congr ?_
    ext x
    simp only [mem_union, mem_iUnion]
    exact (Fin.exists_fin_succ (P := fun i => x ∈ A i)).symm

/-- A single sign condition on one polynomial. -/
lemma Format.sign_mem {n D : ℕ} {B : ℝ} (q : MvPolynomial (Fin n) ℝ) (T : Set SignType)
    (hB : 1 ≤ B) (hq : q.totalDegree ≤ D) (hc : ∀ b, |q.coeff b| ≤ B) :
    Format n B D {x | SignType.sign (eval x q) ∈ T} := by
  refine ⟨1, by simpa using hB, fun _ => q, fun _ => ⟨hq, hc⟩, {s | s 0 ∈ T}, ?_⟩
  ext x
  simp

/-- The affine polynomial `a * X e + d`. -/
def affinePoly {n : ℕ} (e : Fin n) (a d : ℝ) : MvPolynomial (Fin n) ℝ := C a * X e + C d

lemma eval_affinePoly {n : ℕ} (e : Fin n) (a d : ℝ) (x : Fin n → ℝ) :
    eval x (affinePoly e a d) = a * x e + d := by
  simp [affinePoly]

lemma totalDegree_affinePoly {n : ℕ} (e : Fin n) (a d : ℝ) :
    (affinePoly e a d).totalDegree ≤ 1 := by
  unfold affinePoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  · rw [totalDegree_C]
    exact zero_le_one

lemma abs_coeff_affinePoly_le {n : ℕ} (e : Fin n) (a d : ℝ) (b : Fin n →₀ ℕ) :
    |(affinePoly e a d).coeff b| ≤ |a| + |d| := by
  classical
  unfold affinePoly
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_X, coeff_C]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- An affine sign condition in one coordinate. -/
lemma Format.affine {n D : ℕ} {B : ℝ} (e : Fin n) (a d : ℝ) (T : Set SignType)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (had : |a| + |d| ≤ B) :
    Format n B D {x | SignType.sign (a * x e + d) ∈ T} := by
  have := Format.sign_mem (affinePoly e a d) T hB ((totalDegree_affinePoly e a d).trans hD)
    (fun b => (abs_coeff_affinePoly_le e a d b).trans had)
  simpa only [eval_affinePoly] using this

lemma Format.affine_nonneg {n D : ℕ} {B : ℝ} (e : Fin n) (a d : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (had : |a| + |d| ≤ B) :
    Format n B D {x | 0 ≤ a * x e + d} := by
  refine (Format.affine e a d {s | s ≠ -1} hB hD had).congr ?_
  ext x
  simp only [mem_ofPred_eq, ne_eq, sign_eq_neg_one_iff, not_lt]

lemma Format.affine_nonpos {n D : ℕ} {B : ℝ} (e : Fin n) (a d : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (had : |a| + |d| ≤ B) :
    Format n B D {x | a * x e + d ≤ 0} := by
  refine (Format.affine e a d {s | s ≠ 1} hB hD had).congr ?_
  ext x
  simp only [mem_ofPred_eq, ne_eq, sign_eq_one_iff, not_lt]

lemma Format.affine_neg {n D : ℕ} {B : ℝ} (e : Fin n) (a d : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (had : |a| + |d| ≤ B) :
    Format n B D {x | a * x e + d < 0} := by
  refine (Format.affine e a d {s | s = -1} hB hD had).congr ?_
  ext x
  simp only [mem_ofPred_eq, sign_eq_neg_one_iff]

/-- A coordinate in a closed interval `[l, l + σ]` after an affine change `a * x e + d`. -/
lemma Format.affine_Icc {n D : ℕ} {B : ℝ} (e : Fin n) (a d σ : ℝ)
    (hB : 1 ≤ B) (hD : 1 ≤ D) (had : |a| + |d| + |σ| ≤ B) :
    Format n (B + B) D {x | 0 ≤ a * x e + d ∧ a * x e + d ≤ σ} := by
  have h₁ := Format.affine_nonneg (D := D) e a d hB hD
    (by linarith [abs_nonneg σ])
  have h₂ := Format.affine_nonpos (D := D) e a (d - σ) hB hD
    (by linarith [abs_sub d σ])
  refine (h₁.inter h₂).congr ?_
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by linarith⟩

/-- A coordinate in the half-open unit interval. -/
lemma Format.coord_Ico {n D : ℕ} (e : Fin n) (hD : 1 ≤ D) :
    Format n 4 D {x | x e ∈ Ico (0 : ℝ) 1} := by
  have h₁ := Format.affine_nonneg (D := D) e 1 0 (by norm_num : (1 : ℝ) ≤ 2) hD (by norm_num)
  have h₂ := Format.affine_neg (D := D) e 1 (-1) (by norm_num : (1 : ℝ) ≤ 2) hD (by norm_num)
  refine ((h₁.inter h₂).mono (by norm_num) le_rfl).congr ?_
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ico, one_mul, add_zero]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by linarith⟩

/-- A coordinate in a half-open interval `[c / J, (c + 1) / J)` with `c < J`. -/
lemma Format.coord_timeCell {n D : ℕ} (e : Fin n) (hD : 1 ≤ D) {J : ℕ} (hJ : 0 < J)
    (c : Fin J) :
    Format n 4 D {x | x e ∈ Ico ((c : ℝ) / (J : ℝ)) (((c : ℝ) + 1) / (J : ℝ))} := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc : (c : ℝ) + 1 ≤ J := by exact_mod_cast c.isLt
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hlo : |-((c : ℝ) / J)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_one hJ']
    linarith
  have hhi : |-(((c : ℝ) + 1) / J)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_one hJ']
    exact hc
  have h₁ := Format.affine_nonneg (D := D) e 1 (-((c : ℝ) / J)) (by norm_num : (1 : ℝ) ≤ 2) hD
    (by rw [abs_one]; linarith)
  have h₂ := Format.affine_neg (D := D) e 1 (-(((c : ℝ) + 1) / J)) (by norm_num : (1 : ℝ) ≤ 2)
    hD (by rw [abs_one]; linarith)
  refine ((h₁.inter h₂).mono (by norm_num) le_rfl).congr ?_
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ico, one_mul]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨by linarith, by linarith⟩

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
