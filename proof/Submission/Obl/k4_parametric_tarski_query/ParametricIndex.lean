import Submission.Obl.k4_parametric_tarski_query.MonicRemainder
import Submission.Obl.k4_parametric_tarski_query.TarskiQuery

/-!
Adapted from the same LOT tree, obligation o050, session x0159,
commit f99d6af7e8420c51ce38439aeede86aba6326413, file `Submission/Obl/k4_sign_projection/ParametricIndex.lean`.
The declarations and imports have been moved to this obligation's namespace.
-/

namespace Submission.Obl.k4_parametric_tarski_query

open Polynomial

variable {ι : Type}

private theorem infinity_signs_of_data (p q : Polynomial ℝ)
    (hd : p.natDegree = q.natDegree)
    (hl : SignType.sign p.leadingCoeff = SignType.sign q.leadingCoeff) :
    topSign p = topSign q ∧ botSign p = botSign q := by
  have ht : topSign p = topSign q := congrArg (fun s : SignType => (s : ℤ)) hl
  exact ⟨ht, by rw [botSign_eq, botSign_eq, hd, ht]⟩

/-- Euclidean recursion with the remainder chosen before inversion. -/
private theorem cauchyIndex_mod_rec (p q : Polynomial ℝ) :
    cauchyIndex p q = topSign ((p % q) * q) - botSign ((p % q) * q) -
      cauchyIndex q (p % q) := by
  have h := cauchyIndex_reciprocity (p % q) q
  rw [cauchyIndex_mod] at h
  omega

/-- Fixed finite polynomial sign tests determine Cauchy indices in a parameter family. -/
theorem specialize_cauchyIndex_bounded (N : ℕ) :
    ∀ p q : Polynomial (RFun ι), q.natDegree ≤ N →
      SignDetermined (fun x => cauchyIndex (specialize p x) (specialize q x)) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro p q hq
    let r : Fin (N + 1) → Polynomial (RFun ι) := fun n => branchRemainder p q n
    let data (f : Polynomial (RFun ι)) (x : ι → ℝ) :=
      ((specialize f x).support, (specialize f x).natDegree,
        SignType.sign (specialize f x).leadingCoeff)
    have hindex (n : Fin (N + 1)) :
        SignDetermined (fun x => cauchyIndex (specialize q x) (specialize (r n) x)) := by
      by_cases hn : (n : ℕ) = 0
      · simpa only [r, branchRemainder, monicNormalizer, hn, pow_zero, Finset.range_zero,
          Finset.sum_empty, add_zero, modByMonic_one, specialize, Polynomial.map_zero,
          cauchyIndex_zero_right] using SignDetermined.const (ι := ι) (0 : ℤ)
      · have hnpos : 0 < (n : ℕ) := Nat.pos_of_ne_zero hn
        have hr : (r n).natDegree < N :=
          (branchRemainder_degree p q n hnpos).trans_le (Nat.le_of_lt_succ n.isLt)
        exact ih (r n).natDegree hr q (r n) le_rfl
    have htest : SignDetermined (fun x => (data q x,
        fun n : Fin (N + 1) => (data (r n) x,
          cauchyIndex (specialize q x) (specialize (r n) x)))) :=
      (specialize_data q).prod (SignDetermined.pi _
        (fun n => (specialize_data (r n)).prod (hindex n)))
    apply SignDetermined.of_fibers htest
    intro x y hxy
    have hdq : data q x = data q y := congrArg Prod.fst hxy
    have hsup : (specialize q x).support = (specialize q y).support := congrArg Prod.fst hdq
    have hdeg : (specialize q x).natDegree = (specialize q y).natDegree :=
      congrArg (fun z => z.2.1) hdq
    have hlead : SignType.sign (specialize q x).leadingCoeff =
        SignType.sign (specialize q y).leadingCoeff := congrArg (fun z => z.2.2) hdq
    have hzero : specialize q x = 0 ↔ specialize q y = 0 := by
      rw [← support_eq_empty, ← support_eq_empty, hsup]
    by_cases hx : specialize q x = 0
    · rw [hx, hzero.mp hx, cauchyIndex_zero_right, cauchyIndex_zero_right]
    have hy : specialize q y ≠ 0 := fun hy => hx (hzero.mpr hy)
    have hbound : (specialize q x).natDegree ≤ N :=
      (natDegree_map_le).trans hq
    let n : Fin (N + 1) := ⟨(specialize q x).natDegree, Nat.lt_succ_of_le hbound⟩
    have hrx : specialize (r n) x = specialize p x % specialize q x :=
      specialize_branchRemainder p q n x hx rfl
    have hry : specialize (r n) y = specialize p y % specialize q y :=
      specialize_branchRemainder p q n y hy hdeg.symm
    have hd : (data (r n) x, cauchyIndex (specialize q x) (specialize (r n) x)) =
        (data (r n) y, cauchyIndex (specialize q y) (specialize (r n) y)) :=
      congrFun (congrArg Prod.snd hxy) n
    have hdr := congrArg Prod.fst hd
    have hIdx := congrArg Prod.snd hd
    dsimp only at hIdx
    obtain ⟨hqt, hqb⟩ := infinity_signs_of_data _ _ hdeg hlead
    obtain ⟨hrt, hrb⟩ := infinity_signs_of_data _ _
      (congrArg (fun z => z.2.1) hdr) (congrArg (fun z => z.2.2) hdr)
    have hrecx := cauchyIndex_mod_rec (specialize p x) (specialize q x)
    have hrecy := cauchyIndex_mod_rec (specialize p y) (specialize q y)
    rw [← hrx, topSign_mul, botSign_mul] at hrecx
    rw [← hry, topSign_mul, botSign_mul] at hrecy
    rw [hqt, hqb, hrt, hrb, hIdx] at hrecx
    exact hrecx.trans hrecy.symm

theorem specialize_cauchyIndex (p q : Polynomial (RFun ι)) :
    SignDetermined (fun x => cauchyIndex (specialize p x) (specialize q x)) :=
  specialize_cauchyIndex_bounded q.natDegree p q le_rfl

end Submission.Obl.k4_parametric_tarski_query
