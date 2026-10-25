import Submission.Lib.K4ChartLifting.Basic
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Calculus of the Boolean sign format

`Fmt H D S`: the set `S ⊆ ℝⁿ` is a Boolean combination of at most `H` sign tests
`0 ≤ p(x)` with `deg p ≤ D`. `PolynomialFormat N M D S` is `Fmt (N ^ M) D S`.
Formats are preserved by preimages under maps of degree at most one, and
intersections add the numbers of tests.
-/

namespace Submission.Lib.K4ChartLifting

open MvPolynomial

/-- The Boolean sign format with an explicit bound `H` on the number of tests. -/
def Fmt {n : ℕ} (H : ℝ) (D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ H ∧
    ∃ p : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ i, (p i).totalDegree ≤ D) ∧ ∃ b : (Fin m → Bool) → Bool,
        ∀ x, x ∈ S ↔ b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true

theorem polynomialFormat_iff {n : ℕ} (N : ℝ) (M D : ℕ) (S : Set (Fin n → ℝ)) :
    PolynomialFormat N M D S ↔ Fmt (N ^ M) D S := Iff.rfl

namespace Fmt

variable {n k : ℕ}

theorem mono {H H' : ℝ} {D D' : ℕ} {S : Set (Fin n → ℝ)} (h : Fmt H D S) (hH : H ≤ H')
    (hD : D ≤ D') : Fmt H' D' S := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  exact ⟨m, hm.trans hH, p, fun i => (hp i).trans hD, b, hb⟩

theorem congr {H : ℝ} {D : ℕ} {S T : Set (Fin n → ℝ)} (h : Fmt H D S) (hST : S = T) :
    Fmt H D T := hST ▸ h

theorem univ {H : ℝ} (hH : 0 ≤ H) (D : ℕ) : Fmt H D (Set.univ : Set (Fin n → ℝ)) :=
  ⟨0, by simpa using hH, Fin.elim0, fun i => i.elim0, fun _ => true, fun x => by simp⟩

theorem empty {H : ℝ} (hH : 0 ≤ H) (D : ℕ) : Fmt H D (∅ : Set (Fin n → ℝ)) :=
  ⟨0, by simpa using hH, Fin.elim0, fun i => i.elim0, fun _ => false, fun x => by simp⟩

/-- A single sign test. -/
theorem sign {H : ℝ} (hH : 1 ≤ H) (p : MvPolynomial (Fin n) ℝ) :
    Fmt H p.totalDegree {x | 0 ≤ MvPolynomial.eval x p} :=
  ⟨1, by simpa using hH, fun _ => p, fun _ => le_rfl, fun v => v 0, fun x => by simp⟩

theorem compl {H : ℝ} {D : ℕ} {S : Set (Fin n → ℝ)} (h : Fmt H D S) : Fmt H D Sᶜ := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, p, hp, fun v => !(b v), fun x => ?_⟩
  simp [hb x]

theorem inter {H₁ H₂ : ℝ} {D₁ D₂ : ℕ} {S₁ S₂ : Set (Fin n → ℝ)} (h₁ : Fmt H₁ D₁ S₁)
    (h₂ : Fmt H₂ D₂ S₂) : Fmt (H₁ + H₂) (max D₁ D₂) (S₁ ∩ S₂) := by
  obtain ⟨m₁, hm₁, p₁, hp₁, b₁, hb₁⟩ := h₁
  obtain ⟨m₂, hm₂, p₂, hp₂, b₂, hb₂⟩ := h₂
  refine ⟨m₁ + m₂, by push_cast; linarith, Fin.append p₁ p₂, ?_,
    fun v => b₁ (fun i => v (Fin.castAdd m₂ i)) && b₂ (fun j => v (Fin.natAdd m₁ j)), ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact (hp₁ i).trans (le_max_left _ _)
    · rw [Fin.append_right]; exact (hp₂ j).trans (le_max_right _ _)
  · intro x
    simp only [Set.mem_inter_iff, hb₁ x, hb₂ x, Fin.append_left, Fin.append_right,
      Bool.and_eq_true]

theorem union {H₁ H₂ : ℝ} {D₁ D₂ : ℕ} {S₁ S₂ : Set (Fin n → ℝ)} (h₁ : Fmt H₁ D₁ S₁)
    (h₂ : Fmt H₂ D₂ S₂) : Fmt (H₁ + H₂) (max D₁ D₂) (S₁ ∪ S₂) := by
  have := (h₁.compl.inter h₂.compl).compl
  simpa [Set.compl_inter, compl_compl] using this

/-- Preimage under a polynomial map of degree at most one. -/
theorem preimage {H : ℝ} {D : ℕ} {S : Set (Fin n → ℝ)} (h : Fmt H D S)
    (σ : Fin n → MvPolynomial (Fin k) ℝ) (hσ : ∀ i, (σ i).totalDegree ≤ 1) :
    Fmt H D {x : Fin k → ℝ | (fun i => MvPolynomial.eval x (σ i)) ∈ S} := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, fun i => bind₁ σ (p i), fun i =>
    (totalDegree_bind₁_le_of_le_one σ hσ (p i)).trans (hp i), b, fun x => ?_⟩
  have : ∀ i, MvPolynomial.eval x (bind₁ σ (p i)) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (σ j)) (p i) := by
    intro i
    have := eval₂Hom_bind₁ (RingHom.id ℝ) x σ (p i)
    simpa [MvPolynomial.coe_eval₂Hom] using this
  simp only [Set.mem_ofPred_eq, hb, this]

end Fmt

end Submission.Lib.K4ChartLifting
