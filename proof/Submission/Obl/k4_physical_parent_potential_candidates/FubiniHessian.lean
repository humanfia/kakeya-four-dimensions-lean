import Submission.Obl.k4_physical_parent_potential_candidates.FubiniLogDet

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open scoped BigOperators

noncomputable section

namespace FubiniHessian

open FubiniJets

private theorem cons_empty (i : Fin 3) :
    Fin.cons i (fun j : Fin 0 => Fin.elim0 j) = ![i] := by
  funext j
  fin_cases j
  rfl

def hessian (f : FubiniBase → ℝ) (x : FubiniBase) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => jet f 2 ![i,j] x

def cubic (f : FubiniBase → ℝ) (x : FubiniBase) (i j k : Fin 3) : ℝ :=
  jet f 3 ![i,j,k] x

def potential (f : FubiniBase → ℝ) (x : FubiniBase) : ℝ := fubiniLogPotential (hessian f x)

def form (f : FubiniBase → ℝ) (x : FubiniBase) (i : Fin 3) : ℝ := jet (potential f) 1 ![i] x

def density (f : FubiniBase → ℝ) (x : FubiniBase) : ℝ := Real.exp (-potential f x)

def canonical (f : FubiniBase → ℝ) (x : FubiniBase) (i : Fin 3) : ℝ :=
  (∑ j : Fin 3, ∑ k : Fin 3, (hessian f x)⁻¹ j k*cubic f x i j k)/5

theorem hessian_symmetric
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) {x : FubiniBase} (hx : x ∈ U) : (hessian f x).IsSymm := by
  apply Matrix.IsSymm.ext_iff.mpr
  intro i j
  exact jet_two_symmetric hU hf (by norm_num) hx j i

theorem potential_smooth
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0) :
    ContDiffOn ℝ 4 (potential f) U := by
  apply contDiffOn_fubiniLogPotential ?_ hdet
  intro i j
  exact contDiffOn_jet hU hf (by norm_num : (4:WithTop ℕ∞)+2 ≤ 6) ![i,j]

theorem hasDerivAt_coordinate_potential
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) {x : FubiniBase} (hx : x ∈ U)
    (hdet : (hessian f x).det ≠ 0) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => potential f (x+s • basis i)) (canonical f x i) 0 := by
  have hH : ∀ j k : Fin 3,
      HasDerivAt (fun s : ℝ => hessian f (x+s • basis i) j k) (cubic f x i j k) 0 := by
    intro j k
    exact hasDerivAt_coordinate_jet hU hf (by norm_num) ![j,k] x hx i
  have hh := hasDerivAt_fubiniLogPotential hH (by simpa using hdet)
  simp only [zero_smul, add_zero] at hh
  convert hh using 1
  · rfl
  · unfold canonical
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [(hessian_symmetric hU hf hx).inv.apply j k]

/-- The contraction-defined one-form is the gradient of one actual smooth
logarithmic potential. Its first and second derivative symmetries follow. -/
theorem form_eq_canonical
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (i : Fin 3) : form f x i = canonical f x i := by
  have hφ := potential_smooth hU hf hdet
  have hh := hasDerivAt_coordinate_jet hU hφ (n := 0) (by norm_num)
    (fun i : Fin 0 => Fin.elim0 i) x hx i
  have hform : HasDerivAt (fun s : ℝ => potential f (x+s • basis i)) (form f x i) 0 := by
    simpa only [jet, form, iteratedFDeriv_zero_apply, Nat.zero_add, cons_empty] using hh
  exact hform.unique (hasDerivAt_coordinate_potential hU hf hx (hdet x hx) i)

theorem hasDerivAt_radial_density
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    (x : FubiniBase) (t : ℝ) (ht : t • x ∈ U) :
    HasDerivAt (fun s : ℝ => density f (s • x))
      (-density f (t • x)*(∑ i : Fin 3, form f (t • x) i*x i)) t := by
  have hφ := potential_smooth hU hf hdet
  have hh := hasDerivAt_radial_jet hU hφ (n := 0) (by norm_num)
    (fun i : Fin 0 => Fin.elim0 i) x t ht
  have hφd : HasDerivAt (fun s : ℝ => potential f (s • x))
      (∑ i : Fin 3, form f (t • x) i*x i) t := by
    simpa only [jet, form, iteratedFDeriv_zero_apply, Nat.zero_add, cons_empty] using hh
  convert hφd.neg.exp using 1 <;> dsimp [density] <;> ring

theorem form_first_derivatives_symmetric
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (i j : Fin 3) :
    jet (potential f) 2 ![i,j] x = jet (potential f) 2 ![j,i] x :=
  jet_two_symmetric hU (potential_smooth hU hf hdet) (by norm_num) hx i j

theorem form_second_derivatives_symmetric
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (i j k : Fin 3) :
    jet (potential f) 3 ![i,j,k] x = jet (potential f) 3 ![j,i,k] x :=
  jet_three_first_two_symmetric hU (potential_smooth hU hf hdet) (by norm_num) hx i j k

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
