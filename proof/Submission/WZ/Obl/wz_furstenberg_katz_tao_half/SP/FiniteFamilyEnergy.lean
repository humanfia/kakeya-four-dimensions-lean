-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.FiniteFamilyEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.NearFarCounting
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RatioGapFrostman

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The intersection energy of a finite family is bounded below by
Cauchy-Schwarz on the union supporting it. -/
theorem finite_family_intersection_energy {I X : Type*} [Fintype I] [DecidableEq X]
    (F : I → Finset X) (S : Finset X) (hsub : ∀ i, F i ⊆ S) :
    (∑ i, ((F i).card : ℝ)) ^ 2 ≤ (S.card : ℝ) *
      (∑ i, ∑ j, ((F i ∩ F j).card : ℝ)) := by
  classical
  have hfilter (i : I) : S.filter (fun z => z ∈ F i) = F i := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hz => ⟨hsub i hz, hz⟩⟩
  have hfilterPair (i j : I) : S.filter (fun z => z ∈ F i ∧ z ∈ F j) = F i ∩ F j := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun hz => hz.2, fun hz => ⟨hsub i hz.1, hz⟩⟩
  have hrow (i : I) : ((F i).card : ℝ) = ∑ z ∈ S, if z ∈ F i then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hfilter]
  have hpair (i j : I) : ((F i ∩ F j).card : ℝ) =
      ∑ z ∈ S, if z ∈ F i ∧ z ∈ F j then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hfilterPair]
  have hsum : (∑ i, ((F i).card : ℝ)) = ∑ z ∈ S, ∑ i : I, if z ∈ F i then (1 : ℝ) else 0 := by
    simp_rw [hrow]
    exact Finset.sum_comm
  have hsquare (z : X) : (∑ i : I, if z ∈ F i then (1 : ℝ) else 0) ^ 2 =
      ∑ i : I, ∑ j : I, if z ∈ F i ∧ z ∈ F j then (1 : ℝ) else 0 := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hzi : z ∈ F i <;> by_cases hzj : z ∈ F j <;> simp [hzi, hzj]
  have henergy : (∑ i, ∑ j, ((F i ∩ F j).card : ℝ)) =
      ∑ z ∈ S, (∑ i : I, if z ∈ F i then (1 : ℝ) else 0) ^ 2 := by
    simp_rw [hpair]
    calc
      _ = ∑ i : I, ∑ z ∈ S, ∑ j : I, if z ∈ F i ∧ z ∈ F j then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ z ∈ S, ∑ i : I, ∑ j : I, if z ∈ F i ∧ z ∈ F j then (1 : ℝ) else 0 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun z _ => (hsquare z).symm)
  rw [hsum, henergy]
  exact sq_sum_le_card_mul_sum_sq

/-- A uniformly large family in a small support has large total intersections. -/
theorem finite_family_energy_lower {I X : Type*} [Fintype I] [DecidableEq X] [Nonempty I]
    (F : I → Finset X) (S : Finset X) {q K : ℝ} (hq : 0 ≤ q) (hK : 0 < K)
    (hsub : ∀ i, F i ⊆ S)
    (hrow : ∀ i, q * (Fintype.card I : ℝ) ≤ ((F i).card : ℝ))
    (hS : (S.card : ℝ) ≤ K * (Fintype.card I : ℝ)) :
    (q ^ 2 / K) * (Fintype.card I : ℝ) ^ 3 ≤
      ∑ i, ∑ j, ((F i ∩ F j).card : ℝ) := by
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : q * (Fintype.card I : ℝ) ^ 2 ≤ ∑ i, ((F i).card : ℝ) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hrow i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    convert hh using 1 <;> ring
  have henergy := finite_family_intersection_energy F S hsub
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ q * (Fintype.card I : ℝ) ^ 2) hs 2
  have hepos : 0 ≤ ∑ i, ∑ j, ((F i ∩ F j).card : ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_right hS hepos
  apply (mul_le_mul_iff_right₀ (mul_pos hK hN)).mp
  have hid : (K * (Fintype.card I : ℝ)) * ((q ^ 2 / K) * (Fintype.card I : ℝ) ^ 3) =
      (q * (Fintype.card I : ℝ) ^ 2) ^ 2 := by field_simp <;> ring
  rw [hid]
  exact hsq.trans (henergy.trans hbound)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
