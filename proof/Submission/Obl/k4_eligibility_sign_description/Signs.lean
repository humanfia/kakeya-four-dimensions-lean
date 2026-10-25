import Mathlib

namespace Submission.Obl.k4_eligibility_sign_description

noncomputable section

variable {σ X : Type*}

/-- A sign description with specified format bounds, pulled back along coordinates. -/
def SignRep (v : X → σ → ℝ) (n d : ℕ) (E : X → Prop) : Prop :=
  ∃ (p : Fin n → MvPolynomial σ ℝ) (B : Set (Fin n → SignType)),
    (∀ i, (p i).totalDegree ≤ d) ∧
    ∀ x, (fun i => SignType.sign (MvPolynomial.eval (v x) (p i))) ∈ B ↔ E x

lemma SignRep.congr {v : X → σ → ℝ} {n d : ℕ} {E F : X → Prop}
    (h : SignRep v n d E) (hEF : ∀ x, E x ↔ F x) : SignRep v n d F := by
  obtain ⟨p, B, hp, hB⟩ := h
  exact ⟨p, B, hp, fun x => (hB x).trans (hEF x)⟩

lemma SignRep.not {v : X → σ → ℝ} {n d : ℕ} {E : X → Prop}
    (h : SignRep v n d E) : SignRep v n d (fun x => ¬ E x) := by
  obtain ⟨p, B, hp, hB⟩ := h
  exact ⟨p, Bᶜ, hp, fun x => not_congr (hB x)⟩

lemma SignRep.and {v : X → σ → ℝ} {n m d e : ℕ} {E F : X → Prop}
    (hE : SignRep v n d E) (hF : SignRep v m e F) :
    SignRep v (n + m) (max d e) (fun x => E x ∧ F x) := by
  obtain ⟨p, B, hp, hB⟩ := hE
  obtain ⟨q, A, hq, hA⟩ := hF
  refine ⟨Fin.addCases p q,
    {w | (fun i => w (Fin.castAdd m i)) ∈ B ∧ (fun i => w (Fin.natAdd n i)) ∈ A},
    ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using (hp j).trans (le_max_left d e)
    · simpa only [Fin.addCases_right] using (hq j).trans (le_max_right d e)
  · intro x
    simpa only [Set.mem_setOf_eq, Fin.addCases_left, Fin.addCases_right] using
      and_congr (hB x) (hA x)

lemma SignRep.atom (v : X → σ → ℝ) (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.totalDegree ≤ d) (T : Set SignType) :
    SignRep v 1 d (fun x => SignType.sign (MvPolynomial.eval (v x) p) ∈ T) := by
  refine ⟨fun _ => p, {w | w 0 ∈ T}, fun _ => hp, fun _ => Iff.rfl⟩

lemma SignRep.nonneg (v : X → σ → ℝ) (p : MvPolynomial σ ℝ) (d : ℕ)
    (hp : p.totalDegree ≤ d) :
    SignRep v 1 d (fun x => 0 ≤ MvPolynomial.eval (v x) p) := by
  refine (SignRep.atom v p d hp {z | 0 ≤ z}).congr ?_
  intro x
  exact sign_nonneg_iff

lemma degree_add_le {p q : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p + q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

lemma degree_sub_le {p q : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p - q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

lemma degree_C_mul_le (a : ℝ) (p : MvPolynomial σ ℝ) :
    (MvPolynomial.C a * p).totalDegree ≤ p.totalDegree := by
  simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C a) p

lemma degree_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) : (∑ i ∈ s, f i).totalDegree ≤ d :=
  MvPolynomial.totalDegree_finsetSum_le hf

/-- Affine substitution does not increase total degree. -/
lemma degree_aeval_le {τ : Type*} (p : MvPolynomial τ ℝ)
    (f : τ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  change (MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree
  apply (degree_C_mul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

end
end Submission.Obl.k4_eligibility_sign_description
