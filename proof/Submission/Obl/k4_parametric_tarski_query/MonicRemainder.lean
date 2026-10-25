import Submission.Obl.k4_parametric_tarski_query.CoefficientSigns

/-!
Adapted from the same LOT tree, obligation o050, session x0159,
commit f99d6af7e8420c51ce38439aeede86aba6326413, file `Submission/Obl/k4_sign_projection/MonicRemainder.lean`.
The declarations and imports have been moved to this obligation's namespace.
-/

namespace Submission.Obl.k4_parametric_tarski_query

open Polynomial
open scoped BigOperators

variable {ι : Type}

/-- A fixed-degree monic normalization. It is defined even where the chosen coefficient vanishes. -/
noncomputable def monicNormalizer (q : Polynomial (RFun ι)) (n : ℕ) : Polynomial (RFun ι) :=
  X ^ n + ∑ k ∈ Finset.range n, monomial k (q.coeff k * (q.coeff n)⁻¹)

lemma coeff_monicNormalizer (q : Polynomial (RFun ι)) (n k : ℕ) :
    (monicNormalizer q n).coeff k =
      (if n = k then 1 else 0) + (if k < n then q.coeff k * (q.coeff n)⁻¹ else 0) := by
  classical
  simp [monicNormalizer, coeff_monomial, eq_comm]

lemma monicNormalizer_degree_le (q : Polynomial (RFun ι)) (n : ℕ) :
    (monicNormalizer q n).degree ≤ n := by
  rw [degree_le_iff_coeff_zero]
  intro k hk
  rw [coeff_monicNormalizer]
  have hk' : n < k := by exact_mod_cast hk
  simp [hk'.ne, not_lt_of_ge hk'.le]

lemma monicNormalizer_monic (q : Polynomial (RFun ι)) (n : ℕ) :
    (monicNormalizer q n).Monic := by
  apply monic_of_degree_le n (monicNormalizer_degree_le q n)
  simp [coeff_monicNormalizer]

lemma monicNormalizer_natDegree (q : Polynomial (RFun ι)) (n : ℕ) :
    (monicNormalizer q n).natDegree = n := by
  apply natDegree_eq_of_degree_eq_some
  apply degree_eq_of_le_of_coeff_ne_zero (monicNormalizer_degree_le q n)
  simp [coeff_monicNormalizer]

/-- On the branch where the specialized degree is `n`, this is the usual normalization. -/
lemma specialize_monicNormalizer (q : Polynomial (RFun ι)) (n : ℕ) (x : ι → ℝ)
    (hq : specialize q x ≠ 0) (hn : (specialize q x).natDegree = n) :
    specialize (monicNormalizer q n) x =
      specialize q x * C ((specialize q x).leadingCoeff)⁻¹ := by
  classical
  have hlead : (specialize q x).coeff n ≠ 0 := by
    rw [← hn, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hq
  have hlead' : (specialize q x).leadingCoeff = RFun.at x (q.coeff n) := by
    rw [leadingCoeff, hn, specialize_coeff]
  ext k
  rw [specialize_coeff, coeff_monicNormalizer, map_add, coeff_mul_C, specialize_coeff]
  rcases lt_trichotomy k n with hk | rfl | hk
  · simp [hk, hk.ne', map_mul, RFun.at_inv, hlead']
  · simp [hlead', mul_inv_cancel₀ (by simpa only [specialize_coeff] using hlead)]
  · have hk0 : RFun.at x (q.coeff k) = 0 := by
      rw [← specialize_coeff]
      exact coeff_eq_zero_of_natDegree_lt (by simpa only [hn] using hk)
    simp [hk.not_gt, hk.ne, hk0]

/-- A symbolic remainder with a degree bound that is uniform over all parameter values. -/
noncomputable def branchRemainder (p q : Polynomial (RFun ι)) (n : ℕ) : Polynomial (RFun ι) :=
  p %ₘ monicNormalizer q n

lemma branchRemainder_degree (p q : Polynomial (RFun ι)) (n : ℕ) (hn : 0 < n) :
    (branchRemainder p q n).natDegree < n := by
  have hne : monicNormalizer q n ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    rw [monicNormalizer_natDegree, natDegree_one] at hd
    omega
  have h := natDegree_modByMonic_lt p (monicNormalizer_monic q n) hne
  rwa [monicNormalizer_natDegree] at h

lemma specialize_branchRemainder (p q : Polynomial (RFun ι)) (n : ℕ) (x : ι → ℝ)
    (hq : specialize q x ≠ 0) (hn : (specialize q x).natDegree = n) :
    specialize (branchRemainder p q n) x = specialize p x % specialize q x := by
  rw [specialize, branchRemainder, map_modByMonic _ (monicNormalizer_monic q n)]
  change specialize p x %ₘ specialize (monicNormalizer q n) x = _
  rw [specialize_monicNormalizer q n x hq hn, mod_def]

end Submission.Obl.k4_parametric_tarski_query
