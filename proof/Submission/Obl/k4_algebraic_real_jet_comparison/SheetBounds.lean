import Mathlib
import Submission.Obl.k4_algebraic_sheet_bound
import Submission.Obl.k4_algebraic_real_jet_comparison.AlgebraicClosure
import Submission.Obl.k4_algebraic_real_jet_comparison.AffineRelations

/- Adapted from session x0381, o112, commit e55b3ba,
   Submission/Obl/k4_local_algebraic_graph_matching/SheetBounds.lean. -/
namespace Submission.Obl.k4_algebraic_real_jet_comparison

open MvPolynomial Set Metric

/-- A bounded-degree equation on the fixed holomorphic domain. -/
def HasSheetRelation (n D : ℕ) (f : EuclideanSpace ℂ (Fin n) → ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
    ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 4,
      eval (Fin.snoc (fun i => z i) (f z)) P = 0

lemma HasSheetRelation.const_mul {n D : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HasSheetRelation n D f) {c : ℂ} (hc : c ≠ 0) :
    HasSheetRelation n D (fun z => c * f z) := by
  obtain ⟨P, hP, hPD, hroot⟩ := hf
  refine ⟨affineRelation (fun _ => 0) 1 c⁻¹ P, ?_,
    (totalDegree_affineRelation_le _ _ _ _).trans hPD, ?_⟩
  · intro hzero
    apply hP
    exact affineRelation_injective (fun _ => 0) one_ne_zero (inv_ne_zero hc)
      (by simpa using hzero)
  · intro z hz
    rw [eval_affineRelation]
    simpa only [zero_add, one_mul, inv_mul_cancel_left₀ hc] using hroot z hz

lemma HasSheetRelation.comp_affine {n D : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HasSheetRelation n D f) (a : EuclideanSpace ℂ (Fin n)) {r : ℂ} (hr : r ≠ 0)
    (hmap : MapsTo (fun z => a + r • z) (ball 0 4) (ball 0 4)) :
    HasSheetRelation n D (fun z => f (a + r • z)) := by
  obtain ⟨P, hP, hPD, hroot⟩ := hf
  refine ⟨affineRelation (fun i => a i) r 1 P, ?_,
    (totalDegree_affineRelation_le _ _ _ _).trans hPD, ?_⟩
  · intro hzero
    apply hP
    exact affineRelation_injective _ hr one_ne_zero (by simpa using hzero)
  · intro z hz
    rw [eval_affineRelation]
    simpa only [one_mul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      hroot (a + r • z) (hmap hz)

/-- A single degree bound works for every pair of sheets in both lists. -/
theorem exists_sheet_difference_degree (n D : ℕ) :
    ∃ E : ℕ, ∀ (f g : EuclideanSpace ℂ (Fin n) → ℂ),
      HasSheetRelation n D f → HasSheetRelation n D g →
      HasSheetRelation n E (fun z => f z - g z) := by
  obtain ⟨E, hE⟩ := exists_difference_degree_bound n D
  refine ⟨E, ?_⟩
  intro f g ⟨P, hP, hPD, hProot⟩ ⟨Q, hQ, hQD, hQroot⟩
  obtain ⟨S, hS, hSE, hroot⟩ := hE P Q hP hQ hPD hQD
  exact ⟨S, hS, hSE, fun z hz => hroot (fun i => z i) (f z) (g z)
    (hProot z hz) (hQroot z hz)⟩

/-- Homogeneous form of the accepted coefficient-independent sheet norm bound. -/
theorem exists_sheet_norm_constant (n D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (f : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D f →
      DifferentiableOn ℂ f (ball 0 4) → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖f (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B) →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 1 → ‖f z‖ ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := Submission.k4_algebraic_sheet_bound n D
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro f hrel hf B hB hbase z hz
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  let g := fun z => (B : ℂ)⁻¹ * f z
  obtain ⟨P, hP, hPD, hroot⟩ := hrel.const_mul (inv_ne_zero hBc)
  have hnorm (w : EuclideanSpace ℂ (Fin n)) : ‖g w‖ = ‖f w‖ / B := by
    simp only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hB, div_eq_inv_mul]
  have hg : DifferentiableOn ℂ g (ball 0 4) := hf.const_mul _
  have hgb : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖g (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ 1 := by
    intro x hx
    rw [hnorm]
    exact (div_le_one hB).mpr (hbase x hx)
  have hh := hbound P g hP hPD hg hroot hgb z hz
  rw [hnorm] at hh
  exact ((div_le_iff₀ hB).mp hh).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hB.le)


/-- Enlarge a complex normalization ball by a fixed amount, using only the accepted bound. -/
lemma extend_sheet_norm_bound {n D : ℕ} {C : ℝ}
    (hbound : ∀ (f : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D f →
      DifferentiableOn ℂ f (ball 0 4) → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖f (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B) →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 1 → ‖f z‖ ≤ C * B)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hrel : HasSheetRelation n D f)
    (hf : DifferentiableOn ℂ f (ball 0 4)) {L B : ℝ} (hL : 1 ≤ L) (hL' : L ≤ 7 / 4)
    (hB : 0 < B) (hbase : ∀ z, ‖z‖ ≤ L → ‖f z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ L + 1 / 4 → ‖f z‖ ≤ C * B := by
  intro z hz
  let c := (L - 1 / 4) / (L + 1 / 4)
  have hden : 0 < L + 1 / 4 := by linarith
  have hc : 0 ≤ c := div_nonneg (by linarith) hden.le
  have hc' : c ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hca : c * (L + 1 / 4) = L - 1 / 4 := div_mul_cancel₀ _ hden.ne'
  have hcv : (2 * (1 - c)) * (L + 1 / 4) = 1 := by nlinarith [hca]
  let a := (c : ℂ) • z
  let v := (2 : ℂ) • (z - a)
  have ha : ‖a‖ ≤ L - 1 / 4 := by
    calc
      ‖a‖ = c * ‖z‖ := by simp [a, norm_smul, abs_of_nonneg hc]
      _ ≤ c * (L + 1 / 4) := mul_le_mul_of_nonneg_left hz hc
      _ = L - 1 / 4 := hca
  have hv : ‖v‖ ≤ 1 := by
    have he : v = ((2 * (1 - c) : ℝ) : ℂ) • z := by
      dsimp [v, a]
      push_cast
      module
    calc
      ‖v‖ = (2 * (1 - c)) * ‖z‖ := by
        rw [he, norm_smul]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ 2 * (1 - c) by positivity)]
      _ ≤ (2 * (1 - c)) * (L + 1 / 4) := by gcongr
      _ = 1 := hcv
  have hn (w : EuclideanSpace ℂ (Fin n)) : ‖(1 / 2 : ℂ) • w‖ = (1 / 2) * ‖w‖ := by
    rw [norm_smul]
    norm_num
  have hmap : MapsTo (fun w : EuclideanSpace ℂ (Fin n) => a + (1 / 2 : ℂ) • w)
      (ball 0 4) (ball 0 4) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw ⊢
    calc
      ‖a + (1 / 2 : ℂ) • w‖ ≤ ‖a‖ + ‖(1 / 2 : ℂ) • w‖ := norm_add_le _ _
      _ = ‖a‖ + (1 / 2) * ‖w‖ := by rw [hn]
      _ < 4 := by linarith
  have hgrel := hrel.comp_affine a (by norm_num : (1 / 2 : ℂ) ≠ 0) hmap
  have hglinear : Differentiable ℂ
      (fun w : EuclideanSpace ℂ (Fin n) => a + (1 / 2 : ℂ) • w) := by fun_prop
  have hgdiff : DifferentiableOn ℂ (fun w => f (a + (1 / 2 : ℂ) • w)) (ball 0 4) :=
    hf.comp hglinear.differentiableOn hmap
  have hgb : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖f (a + (1 / 2 : ℂ) • WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B := by
    intro x hx
    apply hbase
    have he := Submission.Obl.k4_algebraic_sheet_bound.norm_complexify x
    calc
      _ ≤ ‖a‖ + ‖(1 / 2 : ℂ) • WithLp.toLp 2 (fun i => (x i : ℂ))‖ := norm_add_le _ _
      _ = ‖a‖ + (1 / 2) * ‖x‖ := by rw [hn, he]
      _ ≤ L := by linarith
  have hh := hbound _ hgrel hgdiff B hB hgb v hv
  have hav : a + (1 / 2 : ℂ) • v = z := by
    dsimp [v]
    rw [smul_smul]
    norm_num
  simpa only [hav] using hh

/-- Uniform comparison on a larger interior complex ball, obtained by four overlapping steps. -/
theorem exists_sheet_norm_constant_two (n D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℂ (Fin n) → ℂ), HasSheetRelation n D f →
      DifferentiableOn ℂ f (ball 0 4) → ∀ B : ℝ, 0 < B →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖f (WithLp.toLp 2 (fun i => (x i : ℂ)))‖ ≤ B) →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 2 → ‖f z‖ ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := exists_sheet_norm_constant n D
  have hCpos : 0 < C := by linarith
  refine ⟨C ^ 5, by positivity, ?_⟩
  intro f hrel hf B hB hbase
  have h₀ := hbound f hrel hf B hB hbase
  have h₁ : ∀ z, ‖z‖ ≤ 5 / 4 → ‖f z‖ ≤ C * (C * B) := by
    convert extend_sheet_norm_bound hbound f hrel hf (L := 1) (B := C * B)
      (by norm_num) (by norm_num) (mul_pos hCpos hB) h₀ using 1 <;> norm_num
  have h₂ : ∀ z, ‖z‖ ≤ 3 / 2 → ‖f z‖ ≤ C * (C * (C * B)) := by
    convert extend_sheet_norm_bound hbound f hrel hf (L := 5 / 4) (B := C * (C * B))
      (by norm_num) (by norm_num) (by positivity) h₁ using 1 <;> norm_num
  have h₃ : ∀ z, ‖z‖ ≤ 7 / 4 → ‖f z‖ ≤ C * (C * (C * (C * B))) := by
    convert extend_sheet_norm_bound hbound f hrel hf (L := 3 / 2) (B := C * (C * (C * B)))
      (by norm_num) (by norm_num) (by positivity) h₂ using 1 <;> norm_num
  have h₄ : ∀ z, ‖z‖ ≤ 2 → ‖f z‖ ≤ C * (C * (C * (C * (C * B)))) := by
    convert extend_sheet_norm_bound hbound f hrel hf (L := 7 / 4) (B := C * (C * (C * (C * B))))
      (by norm_num) (by norm_num) (by positivity) h₃ using 1 <;> norm_num
  intro z hz
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h₄ z hz

end Submission.Obl.k4_algebraic_real_jet_comparison
