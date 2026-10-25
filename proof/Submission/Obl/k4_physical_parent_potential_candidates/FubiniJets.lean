import Submission.Obl.k4_physical_parent_potential_candidates.FubiniGraph
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Symm
import Submission.Obl.k4_seven_direction_local_degree_restoration.GraphTaylor

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open Submission.Obl.k4_approximate_conic_taylor_decomposition

noncomputable section

namespace FubiniJets

def basis (i : Fin 3) : FubiniBase := EuclideanSpace.basisFun (Fin 3) ℝ i

def jet (f : FubiniBase → ℝ) (n : ℕ) (α : Fin n → Fin 3) (x : FubiniBase) : ℝ :=
  iteratedFDeriv ℝ n f x (fun i => basis (α i))

/-- Radial differentiation of an actual coordinate jet, with no abstract
formal derivative standing in for the graph's derivatives. -/
theorem hasDerivAt_radial_jet
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    {n : ℕ} (hn : ((n+1:ℕ):WithTop ℕ∞) ≤ N)
    (α : Fin n → Fin 3) (x : FubiniBase) (t : ℝ) (ht : t • x ∈ U) :
    HasDerivAt (fun s => jet f n α (s • x))
      (∑ i : Fin 3, jet f (n+1) (Fin.cons i α) (t • x)*x i) t := by
  have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ n f z (fun i => basis (α i))) (t • x) :=
    (differentiableAt_iteratedFDeriv_of_isOpen hU hf hn ht).continuousMultilinear_apply_const _
  have hrad : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hh := hd.hasFDerivAt.comp_hasDerivAt t hrad
  convert hh using 1
  · rfl
  · change _ = (fderiv ℝ (fun z => iteratedFDeriv ℝ n f z (fun i => basis (α i))) (t • x)) x
    rw [← Submission.Obl.k4_seven_direction_local_degree_restoration.linear_coordinates]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_iteratedFDeriv_apply_const hU hf hn ht]
    rfl


theorem contDiffOn_jet
    {f : FubiniBase → ℝ} {N M : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    {n : ℕ} (hn : M+(n:WithTop ℕ∞) ≤ N) (α : Fin n → Fin 3) :
    ContDiffOn ℝ M (jet f n α) U := by
  apply hU.contDiffOn_iff.mpr
  intro x hx
  have hh : ContDiffAt ℝ M (iteratedFDeriv ℝ n f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right hn
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => FubiniBase) ℝ
    (fun i => basis (α i))).contDiff.contDiffAt.comp x hh

/-- A coordinate derivative of an actual jet is the next coordinate jet. -/
theorem hasDerivAt_coordinate_jet
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    {n : ℕ} (hn : ((n+1:ℕ):WithTop ℕ∞) ≤ N)
    (α : Fin n → Fin 3) (x : FubiniBase) (hx : x ∈ U) (i : Fin 3) :
    HasDerivAt (fun s => jet f n α (x+s • basis i))
      (jet f (n+1) (Fin.cons i α) x) (0:ℝ) := by
  have hd : DifferentiableAt ℝ (fun z => iteratedFDeriv ℝ n f z (fun i => basis (α i))) x :=
    (differentiableAt_iteratedFDeriv_of_isOpen hU hf hn hx).continuousMultilinear_apply_const _
  have hcurve : HasDerivAt (fun s : ℝ => x+s • basis i) (basis i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (basis i)).const_add x
  have hd' : HasFDerivAt
      (fun z => iteratedFDeriv ℝ n f z (fun i => basis (α i)))
      (fderiv ℝ (fun z => iteratedFDeriv ℝ n f z (fun i => basis (α i))) x)
      (x+(0:ℝ) • basis i) := by simpa using hd.hasFDerivAt
  have hh := hd'.comp_hasDerivAt (f := fun s : ℝ => x+s • basis i) (0:ℝ) hcurve
  convert hh using 1
  · rfl
  · rw [fderiv_iteratedFDeriv_apply_const hU hf hn hx]
    rfl


private theorem cons_empty_value (i : Fin 3) :
    Fin.cons i (fun j : Fin 0 => Fin.elim0 j) = ![i] := by
  funext j
  fin_cases j
  rfl

theorem hasDerivAt_coordinate_value
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hn : (1:WithTop ℕ∞) ≤ N)
    (x : FubiniBase) (hx : x ∈ U) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => f (x+s • basis i)) (jet f 1 ![i] x) 0 := by
  have hh := hasDerivAt_coordinate_jet hU hf (n := 0) (by simpa using hn)
    (fun j : Fin 0 => Fin.elim0 j) x hx i
  simpa only [jet, iteratedFDeriv_zero_apply, Nat.zero_add, cons_empty_value] using hh


theorem hasDerivAt_radial_value
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hn : (1:WithTop ℕ∞) ≤ N)
    (x : FubiniBase) (t : ℝ) (ht : t • x ∈ U) :
    HasDerivAt (fun s : ℝ => f (s • x))
      (∑ i : Fin 3, jet f 1 ![i] (t • x)*x i) t := by
  have hh := hasDerivAt_radial_jet hU hf (n := 0) (by simpa using hn)
    (fun j : Fin 0 => Fin.elim0 j) x t ht
  simpa only [jet, iteratedFDeriv_zero_apply, Nat.zero_add, cons_empty_value] using hh

/-- Actual coordinate jets inherit full permutation symmetry from smoothness. -/
theorem jet_permute
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    {n : ℕ} (hn : (n:WithTop ℕ∞) ≤ N) {x : FubiniBase} (hx : x ∈ U)
    (α : Fin n → Fin 3) (σ : Equiv.Perm (Fin n)) :
    jet f n (α ∘ σ) x = jet f n α x :=
  iteratedFDeriv_comp_perm hU hf n hn x hx σ (fun i => basis (α i))

theorem jet_two_symmetric
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (hn : (2:WithTop ℕ∞) ≤ N) {x : FubiniBase} (hx : x ∈ U) (i j : Fin 3) :
    jet f 2 ![i,j] x = jet f 2 ![j,i] x := by
  have heq : (![j,i] : Fin 2 → Fin 3) ∘ Equiv.swap (0:Fin 2) 1 = ![i,j] := by
    funext k
    fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [← heq]
  exact jet_permute hU hf hn hx _ _

theorem jet_three_first_two_symmetric
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (hn : (3:WithTop ℕ∞) ≤ N) {x : FubiniBase} (hx : x ∈ U) (i j k : Fin 3) :
    jet f 3 ![i,j,k] x = jet f 3 ![j,i,k] x := by
  have heq : (![j,i,k] : Fin 3 → Fin 3) ∘ Equiv.swap (0:Fin 3) 1 = ![i,j,k] := by
    funext l
    fin_cases l <;> simp [Equiv.swap_apply_def]
  rw [← heq]
  exact jet_permute hU hf hn hx _ _


theorem jet_four_first_two_symmetric
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (hn : (4:WithTop ℕ∞) ≤ N) {x : FubiniBase} (hx : x ∈ U) (i j k l : Fin 3) :
    jet f 4 ![i,j,k,l] x = jet f 4 ![j,i,k,l] x := by
  have heq : (![j,i,k,l] : Fin 4 → Fin 3) ∘ Equiv.swap (0:Fin 4) 1 = ![i,j,k,l] := by
    funext v
    fin_cases v <;> simp [Equiv.swap_apply_def]
  rw [← heq]
  exact jet_permute hU hf hn hx _ _

end FubiniJets

end

end Submission.Obl.k4_physical_parent_potential_candidates
