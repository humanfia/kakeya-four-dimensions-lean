import Submission.Obl.k4_physical_parent_potential_candidates.FubiniProductJets
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniInput

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set FubiniJets FubiniProductJets

noncomputable section

namespace FubiniJets

/-- Pointwise bounds for a scalar function and its first two coordinate jets. -/
structure C2Bound (f : FubiniBase → ℝ) (K : ℝ) (x : FubiniBase) : Prop where
  value : |f x| ≤ K
  first : ∀ i, |jet f 1 ![i] x| ≤ K
  second : ∀ i j, |jet f 2 ![i,j] x| ≤ K

namespace C2Bound

variable {f g : FubiniBase → ℝ} {A B : ℝ} {x : FubiniBase} {U : Set FubiniBase}

theorem nonneg (hf : C2Bound f A x) : 0 ≤ A := (abs_nonneg _).trans hf.value

theorem mono (hf : C2Bound f A x) (hAB : A ≤ B) : C2Bound f B x :=
  ⟨hf.value.trans hAB, fun i => (hf.first i).trans hAB, fun i j => (hf.second i j).trans hAB⟩

theorem add (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (hfb : C2Bound f A x) (hgb : C2Bound g B x) :
    C2Bound (fun y => f y+g y) (A+B) x := by
  refine ⟨(abs_add_le _ _).trans (add_le_add hfb.value hgb.value), ?_, ?_⟩
  · intro i
    rw [jet_add hU hf hg hx 1 (by norm_num)]
    exact (abs_add_le _ _).trans (add_le_add (hfb.first i) (hgb.first i))
  · intro i j
    rw [jet_add hU hf hg hx 2 (by norm_num)]
    exact (abs_add_le _ _).trans (add_le_add (hfb.second i j) (hgb.second i j))

theorem const_mul (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hx : x ∈ U)
    (hfb : C2Bound f A x) (r : ℝ) : C2Bound (fun y => r*f y) (|r| * A) x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hfb.value (abs_nonneg _)
  · intro i
    rw [jet_const_mul hU hf hx r 1 (by norm_num), abs_mul]
    exact mul_le_mul_of_nonneg_left (hfb.first i) (abs_nonneg _)
  · intro i j
    rw [jet_const_mul hU hf hx r 2 (by norm_num), abs_mul]
    exact mul_le_mul_of_nonneg_left (hfb.second i j) (abs_nonneg _)

theorem neg (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hx : x ∈ U)
    (hfb : C2Bound f A x) : C2Bound (fun y => -f y) A x := by
  simpa using hfb.const_mul hU hf hx (-1)

theorem sub (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (hfb : C2Bound f A x) (hgb : C2Bound g B x) :
    C2Bound (fun y => f y-g y) (A+B) x := by
  simpa only [sub_eq_add_neg] using hfb.add hU hf hg.neg hx (hgb.neg hU hg hx)

theorem mul (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U)
    (hx : x ∈ U) (hfb : C2Bound f A x) (hgb : C2Bound g B x) :
    C2Bound (fun y => f y*g y) (4*A*B) x := by
  have hA := hfb.nonneg
  have hB := hgb.nonneg
  have ht {a b : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a*b| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  refine ⟨(ht hfb.value hgb.value).trans (by nlinarith [mul_nonneg hA hB]), ?_, ?_⟩
  · intro i
    rw [first_mul hU hf hg hx]
    exact (abs_add_le _ _).trans (by
      nlinarith [ht (hfb.first i) hgb.value, ht hfb.value (hgb.first i), mul_nonneg hA hB])
  · intro i j
    rw [second_mul hU hf hg hx]
    linarith [abs_add_le (jet f 2 ![i,j] x*g x) (jet f 1 ![j] x*jet g 1 ![i] x),
      abs_add_le (jet f 2 ![i,j] x*g x+jet f 1 ![j] x*jet g 1 ![i] x)
        (jet f 1 ![i] x*jet g 1 ![j] x),
      abs_add_le (jet f 2 ![i,j] x*g x+jet f 1 ![j] x*jet g 1 ![i] x+
        jet f 1 ![i] x*jet g 1 ![j] x) (f x*jet g 2 ![i,j] x),
      ht (hfb.second i j) hgb.value, ht (hfb.first j) (hgb.first i),
      ht (hfb.first i) (hgb.first j), ht hfb.value (hgb.second i j)]

end C2Bound

/-- A first jet of a coordinate jet is the corresponding next jet. -/
theorem jet_of_jet_one {f : FubiniBase → ℝ} {U : Set FubiniBase} {N : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {n : ℕ}
    (hn : ((n+1:ℕ):WithTop ℕ∞) ≤ N) (α : Fin n → Fin 3)
    {x : FubiniBase} (hx : x ∈ U) (i : Fin 3) :
    jet (fun y => jet f n α y) 1 ![i] x = jet f (n+1) (Fin.cons i α) x := by
  have hs : ContDiffOn ℝ 1 (fun y => jet f n α y) U :=
    contDiffOn_jet hU hf (by convert hn using 1; push_cast; ring) α
  exact (hasDerivAt_coordinate_value hU hs (by norm_num) x hx i).unique
    (hasDerivAt_coordinate_jet hU hf hn α x hx i)

/-- Second jets of coordinate jets are actual fourth or higher jets. -/
theorem jet_of_jet_two {f : FubiniBase → ℝ} {U : Set FubiniBase} {N : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {n : ℕ}
    (hn : ((n+2:ℕ):WithTop ℕ∞) ≤ N) (α : Fin n → Fin 3)
    {x : FubiniBase} (hx : x ∈ U) (i j : Fin 3) :
    jet (fun y => jet f n α y) 2 ![i,j] x = jet f (n+2) (Fin.cons i (Fin.cons j α)) x := by
  have hh := Submission.Obl.k4_approximate_conic_taylor_decomposition.iteratedFDeriv_two_iteratedFDeriv_apply_const
    hU hf hn hx (fun k => basis (α k)) (basis i) (basis j)
  unfold jet
  convert hh using 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun _ => rfl) k

/-- The determinant of a three-by-three C² matrix has a fixed cubic C² bound. -/
theorem det_C2_bound {H : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ} (hb : ∀ i j, C2Bound (fun y => H y i j) K x) :
    C2Bound (fun y => (H y).det) (96*K^3) x := by
  have ht (a b c d e f : Fin 3) :
      C2Bound (fun y => H y a b*H y c d*H y e f) (16*K^3) x := by
    have hh := (hb a b).mul hU (hH a b) (hH c d) hx (hb c d)
    have hh' := hh.mul hU ((hH a b).mul (hH c d)) (hH e f) hx (hb e f)
    convert hh' using 1 <;> ring
  have hs (a b c d e f : Fin 3) :
      ContDiffOn ℝ 2 (fun y => H y a b*H y c d*H y e f) U :=
    ((hH a b).mul (hH c d)).mul (hH e f)
  have h1 := (ht 0 0 1 1 2 2).sub hU (hs 0 0 1 1 2 2) (hs 0 0 1 2 2 1) hx (ht 0 0 1 2 2 1)
  have s1 := (hs 0 0 1 1 2 2).sub (hs 0 0 1 2 2 1)
  have h2 := h1.sub hU s1 (hs 0 1 1 0 2 2) hx (ht 0 1 1 0 2 2)
  have s2 := s1.sub (hs 0 1 1 0 2 2)
  have h3 := h2.add hU s2 (hs 0 1 1 2 2 0) hx (ht 0 1 1 2 2 0)
  have s3 := s2.add (hs 0 1 1 2 2 0)
  have h4 := h3.add hU s3 (hs 0 2 1 0 2 1) hx (ht 0 2 1 0 2 1)
  have s4 := s3.add (hs 0 2 1 0 2 1)
  have h5 := h4.sub hU s4 (hs 0 2 1 1 2 0) hx (ht 0 2 1 1 2 0)
  have he : (fun y => (H y).det) = fun y =>
      H y 0 0*H y 1 1*H y 2 2-H y 0 0*H y 1 2*H y 2 1-
      H y 0 1*H y 1 0*H y 2 2+H y 0 1*H y 1 2*H y 2 0+
      H y 0 2*H y 1 0*H y 2 1-H y 0 2*H y 1 1*H y 2 0 := by
    funext y
    exact Matrix.det_fin_three (H y)
  rw [he]
  convert h5 using 1 <;> ring

theorem det_contDiffOn {H : FubiniBase → Matrix (Fin 3) (Fin 3) ℝ} {U : Set FubiniBase}
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U) :
    ContDiffOn ℝ 2 (fun y => (H y).det) U := by
  simp only [Matrix.det_fin_three]
  fun_prop

end FubiniJets

namespace FubiniHessian

/-- Norm bounds through fourth order bound the Hessian determinant and its
first two coordinate derivatives by a fixed cubic polynomial. -/
theorem hessian_det_C2_bound {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) {x : FubiniBase} (hx : x ∈ U)
    {K : ℝ} (hb : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ‖iteratedFDeriv ℝ n f x‖ ≤ K) :
    C2Bound (fun y => (hessian f y).det) (96*K^3) x := by
  apply det_C2_bound hU (fun i j => contDiffOn_jet hU hf (by norm_num) ![i,j]) hx
  intro i j
  refine ⟨coordinate_jet_bound (hb 2 (by decide) (by decide)) ![i,j], ?_, ?_⟩
  · intro p
    rw [jet_of_jet_one hU hf (by norm_num) ![i,j] hx p]
    exact coordinate_jet_bound (hb 3 (by decide) (by decide)) _
  · intro p l
    rw [jet_of_jet_two hU hf (by norm_num) ![i,j] hx p l]
    exact coordinate_jet_bound (hb 4 (by decide) (by decide)) _

/-- C² conditioning of the scalar denominator used to remove the cleared
canonical tensor's determinant factor. -/
theorem canonical_denominator_C2_bound
    {f w : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (hw : ContDiffOn ℝ 2 w U)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ}
    (hb : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hwb : C2Bound w K x) :
    C2Bound (fun y => 5*w y*(hessian f y).det) (1920*K^4) x := by
  have hh := hwb.mul hU hw
    (det_contDiffOn (fun i j => contDiffOn_jet hU hf (by norm_num) ![i,j])) hx
    (hessian_det_C2_bound hU hf hx hb)
  have hh' := hh.const_mul hU
    (hw.mul (det_contDiffOn (fun i j => contDiffOn_jet hU hf (by norm_num) ![i,j]))) hx 5
  convert hh' using 1
  · funext y
    change 5*w y*(hessian f y).det = 5*(w y*(hessian f y).det)
    ring
  · norm_num
    ring

/-- One polynomial budget simultaneously bounds the denominator jets and
the reciprocal of its value on a regular implicit graph patch. -/
theorem canonical_denominator_conditioned
    {f w : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (hw : ContDiffOn ℝ 2 w U)
    {x : FubiniBase} (hx : x ∈ U) {K : ℝ} (hK : 1 ≤ K)
    (hb : ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hwb : C2Bound w K x) (hwreg : K⁻¹ ≤ |w x|)
    (hHreg : K⁻¹ ≤ |(hessian f x).det|) :
    (2000*K^4)⁻¹ ≤ |5*w x*(hessian f x).det| ∧
      C2Bound (fun y => 5*w y*(hessian f y).det) (2000*K^4) x := by
  have hK0 : 0 < K := by linarith
  have hK24 : K^2 ≤ K^4 := pow_le_pow_right₀ hK (by decide : 2 ≤ 4)
  have hbudget : K^2 ≤ 2000*K^4 := by nlinarith [pow_nonneg hK0.le 4]
  refine ⟨?_, (canonical_denominator_C2_bound hU hf hw hx hb hwb).mono
    (by nlinarith [pow_nonneg hK0.le 4])⟩
  have hlower : 5*(K⁻¹)^2 ≤ |5*w x*(hessian f x).det| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
    convert mul_le_mul_of_nonneg_left (mul_le_mul hwreg hHreg
      (inv_nonneg.mpr hK0.le) (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 5) using 1 <;> ring
  calc
    _ ≤ (K^2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hK0 2) hbudget
    _ = (K⁻¹)^2 := (inv_pow K 2).symm
    _ ≤ 5*(K⁻¹)^2 := by nlinarith [sq_nonneg (K⁻¹)]
    _ ≤ _ := hlower

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
