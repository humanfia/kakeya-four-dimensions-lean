import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry
import Submission.Obl.k4_horizon_chart_assembly.Packets

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped BigOperators ENNReal
open Submission.Obl.k4_eligibility_sign_description
open Submission.Lib.K4FinitePlankAtlases (PhysicalPlank firstAssignment)

noncomputable section

/-- An arbitrary Boolean operation on finitely many sign descriptions uses their
concatenated polynomial list. -/
theorem signRep_combine {σ X : Type*} {v : X → σ → ℝ} {n m d : ℕ}
    {P : Fin n → X → Prop} (h : ∀ i, SignRep v m d (P i))
    (B : (Fin n → Prop) → Prop) :
    SignRep v (n * m) d (fun x => B (fun i => P i x)) := by
  classical
  choose p A hp hA using h
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  refine ⟨fun j => p (e.symm j).1 (e.symm j).2,
    {w | B (fun i => (fun j => w (e (i, j))) ∈ A i)}, fun j => hp _ _, ?_⟩
  intro x
  change B (fun i => (fun j => SignType.sign (eval (v x)
    (p (e.symm (e (i, j))).1 (e.symm (e (i, j))).2))) ∈ A i) ↔ _
  simp only [Equiv.symm_apply_apply]
  have heq : (fun i => (fun j => SignType.sign (eval (v x) (p i j))) ∈ A i) =
      (fun i => P i x) := funext (fun i => propext (hA i x))
  rw [heq]

/-- A coordinate box needs one quadratic sign test per coordinate. -/
theorem coefficient_box_signRep {n : ℕ} {H : ℝ} (hH : 0 ≤ H) :
    SignRep (fun x : Fin n → ℝ => x) n 4 (fun x => ∀ i, |x i| ≤ H) := by
  have hatom (i : Fin n) : SignRep (fun x : Fin n → ℝ => x) 1 4
      (fun x => |x i| ≤ H) := by
    let p : MvPolynomial (Fin n) ℝ := C (H ^ 2) - X i ^ 2
    have hp : p.totalDegree ≤ 4 := by
      apply degree_sub_le (by simp only [totalDegree_C]; omega)
      exact (totalDegree_pow _ _).trans (by simp)
    apply (SignRep.nonneg (fun x : Fin n → ℝ => x) p 4 hp).congr
    intro x
    simp only [p, map_sub, eval_C, map_pow, eval_X]
    constructor
    · intro hx
      nlinarith [sq_abs (x i), abs_nonneg (x i)]
    · intro hx
      nlinarith [sq_abs (x i), abs_nonneg (x i)]
  simpa using signRep_combine hatom (fun Q => ∀ i, Q i)

/-- Pointwise eligibility has the global native upper fits and the tempered
coordinate box. Its definition is independent of all density deletions. -/
def nativeEligible (P : MvPolynomial (Fin 4) ℝ) (B K H : ℝ) (l : Trajectory) : Prop :=
  (l.1 : ℝ) ≤ H ∧ (∀ e, |l.2 e| ≤ H) ∧
    WholeBlockFit P 1 0 0 K B 1 0 1 l.2

def nativeGroup (P : MvPolynomial (Fin 4) ℝ) (B K H s q a : ℝ)
    (Γ : (Fin 2 → ℤ) × ℤ) : Set Trajectory :=
  {l | nativeEligible P B K H l ∧ midpointGroupCode P s q a l.2 = Γ}

/-- Each native group has fifty-five sign tests, of degree at most four. -/
theorem nativeGroup_signRep (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (B s : ℝ) {K H q a : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hq : 0 < q) (ha : 0 < a) (Γ : (Fin 2 → ℤ) × ℤ) (i : ℕ) :
    SignRep (fun x : Fin 6 → ℝ => x) 55 4
      (fun x => (i, x) ∈ nativeGroup P B K H s q a Γ) := by
  have hind := SignRep.nonneg (fun x : Fin 6 → ℝ => x)
    (C (H - (i : ℝ))) 4 (by simp only [totalDegree_C]; omega)
  have hbox := coefficient_box_signRep (n := 6) hH
  have hwhole := wholeBlockFit_signRep P hP 1 0 0 K B 1 0 1 hK (by norm_num)
  have hgroup := midpointGroupCode_signRep P hP s hq ha Γ
  have h := (hind.and (hbox.and hwhole)).and hgroup
  apply h.congr
  intro x
  simp only [eval_C, nativeGroup, mem_setOf_eq, nativeEligible]
  exact and_congr (and_congr (by constructor <;> intro h <;> linarith) Iff.rfl) Iff.rfl

theorem nativeGroup_format (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (B s : ℝ) {K H q a : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hq : 0 < q) (ha : 0 < a) (Γ : (Fin 2 → ℤ) × ℤ)
    {N : ℝ} {M : ℕ} (hcount : (110 : ℝ) ≤ N ^ M) (i : ℕ) :
    PolynomialFormat N M 4 {x | (i, x) ∈ nativeGroup P B K H s q a Γ} := by
  exact polynomialFormat_of_signRep (nativeGroup_signRep P hP B s hK hH hq ha Γ i)
    (by simpa using hcount)

/-- The finite group universe contains every eligible trajectory at the midpoint. -/
theorem nativeGroup_mem_universe (P : MvPolynomial (Fin 4) ℝ) (B K H s q a : ℝ)
    (hq : 0 < q) (ha : 0 < a) (hK : 0 ≤ K) (hs : s ∈ Icc (0 : ℝ) 1)
    {l : Trajectory} (hl : nativeEligible P B K H l) :
    midpointGroupCode P s q a l.2 ∈ midpointGroupUniverse q a K := by
  have hh := hl.2.2 s hs
  have hy : ‖planarPoint l s‖ ≤ K := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, planarPoint] using hh.1
  have hval : |eval (graphPoint l s) P| ≤ K := by simpa [graphPoint] using hh.2.1
  exact midpointGroupCode_mem_universe P s hq ha hK l.2
    (by simpa only [planarPoint] using hy.trans (show K ≤ 2 * K by linarith)) hval

/-- Distinct midpoint labels give disjoint initial groups. -/
theorem nativeGroup_disjoint (P : MvPolynomial (Fin 4) ℝ) (B K H s q a : ℝ) :
    Pairwise (fun Γ Γ' => Disjoint (nativeGroup P B K H s q a Γ)
      (nativeGroup P B K H s q a Γ')) := by
  intro Γ Γ' hne
  apply Set.disjoint_left.mpr
  intro l hl hl'
  exact hne (hl.2.symm.trans hl'.2)

/-- Normalization of the original planar trajectory in one midpoint group. -/
def groupIntercept (q a s r : ℝ) (Γ : (Fin 2 → ℤ) × ℤ) (l : Trajectory) : Plane :=
  normalizedBlockIntercept (planarPoint l 0) (planarVelocity l) (midpointGroupCenter q Γ) s r

def groupVelocity (q r : ℝ) (l : Trajectory) : Plane :=
  normalizedBlockVelocity (planarVelocity l) q r

def groupInterceptPoly (s r : ℝ) (origin : Plane) : Fin 2 → MvPolynomial (Fin 6) ℝ :=
  fun e => C r⁻¹ * (X (Fin.castAdd 4 e) + C s * X (Fin.natAdd 3 e.castSucc) - C (origin e))

def groupVelocityPoly (q r : ℝ) : Fin 2 → MvPolynomial (Fin 6) ℝ :=
  fun e => C (q / r) * X (Fin.natAdd 3 e.castSucc)

theorem groupInterceptPoly_degree (s r : ℝ) (origin : Plane) (e : Fin 2) :
    (groupInterceptPoly s r origin e).totalDegree ≤ 1 := by
  apply (degree_C_mul_le _ _).trans
  apply degree_sub_le
  · apply degree_add_le (by simp)
    exact (degree_C_mul_le _ _).trans (by simp)
  · simp

theorem groupVelocityPoly_degree (q r : ℝ) (e : Fin 2) :
    (groupVelocityPoly q r e).totalDegree ≤ 1 := by
  exact (degree_C_mul_le _ _).trans (by simp)

theorem groupInterceptPoly_eval (q a s r : ℝ) (Γ : (Fin 2 → ℤ) × ℤ)
    (l : Trajectory) :
    polynomialPlane (groupInterceptPoly s r (midpointGroupCenter q Γ)) l.2 =
      groupIntercept q a s r Γ l := by
  ext e
  fin_cases e <;> simp [polynomialPlane, groupInterceptPoly, groupIntercept,
    normalizedBlockIntercept, planarPoint, planarVelocity]

theorem groupVelocityPoly_eval (q r : ℝ) (l : Trajectory) :
    polynomialPlane (groupVelocityPoly q r) l.2 = groupVelocity q r l := by
  ext e
  fin_cases e <;> simp [polynomialPlane, groupVelocityPoly, groupVelocity,
    normalizedBlockVelocity, planarVelocity]

/-- Finitely many first-fit predicates contribute eight sign tests per plank. -/
theorem packetAssignment_signRep {D m n d : ℕ} (U : Set Trajectory)
    (hU : ∀ i : ℕ, SignRep (fun x : Fin 6 → ℝ => x) n d (fun x => (i, x) ∈ U))
    (q a s r : ℝ) (Γ : (Fin 2 → ℤ) × ℤ)
    (p : Fin m → PhysicalPlank D) (j : Fin m) (i : ℕ) :
    SignRep (fun x : Fin 6 → ℝ => x) (n + m * 8) (max d 1)
      (fun x => (i, x) ∈ packetAssignment U (groupIntercept q a s r Γ) (groupVelocity q r) p j) := by
  have hatom (k : Fin m) := fullTracePlank_signRep
    (groupInterceptPoly s r (midpointGroupCenter q Γ)) (groupVelocityPoly q r)
    (groupInterceptPoly_degree s r _) (groupVelocityPoly_degree q r)
    (p k).center (p k).speed (p k).axis₁ (p k).axis₂ (p k).narrow (p k).wide
  have hfit := signRep_combine hatom (fun Q => Q j ∧ ∀ k, k < j → ¬Q k)
  apply ((hU i).and hfit).congr
  intro x
  rw [groupInterceptPoly_eval q a s r Γ (i, x), groupVelocityPoly_eval q r (i, x)]
  rfl

end
end Submission.Obl.k4_horizon_chart_assembly
