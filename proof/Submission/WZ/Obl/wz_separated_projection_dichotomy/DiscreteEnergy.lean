-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.DiscreteEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Basic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem dyadic_weight_identity {A R γ : ℝ} (hR : 0 < R) (n : ℕ) :
    (A * (R * (1 / 2 : ℝ) ^ n)) * (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (-γ) =
      (A * R * (R / 2) ^ (-γ)) * ((1 / 2 : ℝ) ^ (1 - γ)) ^ n := by
  have hn : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have hscale : R * (1 / 2 : ℝ) ^ (n + 1) = (R / 2) * (1 / 2 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  have hpow : (1 / 2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ (-γ) =
      ((1 / 2 : ℝ) ^ (1 - γ)) ^ n := by
    calc (1 / 2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ (-γ) =
          ((1 / 2 : ℝ) ^ n) ^ (1 - γ) := by
            rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
      _ = ((1 / 2 : ℝ) ^ (1 - γ)) ^ n := by
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
          Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hscale, Real.mul_rpow (by positivity : 0 ≤ R / 2) hn.le]
  calc _ = (A * R * (R / 2) ^ (-γ)) *
      ((1 / 2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ (-γ)) := by ring
    _ = _ := by rw [hpow]

/-- A finite counting Frostman bound controls every energy exponent below
one. The argument sums geometric annuli and has no logarithmic remainder. -/
theorem sum_rpow_neg_le_of_count {X : Type*} [Fintype X] (f : X → ℝ)
    {A R γ : ℝ} (hA : 0 ≤ A) (hR : 0 < R) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ∀ x, 0 < f x ∧ f x ≤ R)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun x => f x ≤ r)).card : ℝ) ≤ A * r) :
    ∑ x, (f x) ^ (-γ) ≤
      (A * R * (R / 2) ^ (-γ)) / (1 - (1 / 2 : ℝ) ^ (1 - γ)) := by
  classical
  have hchoose : ∀ x : X, ∃ n : ℕ,
      R * (1 / 2 : ℝ) ^ (n + 1) < f x ∧ f x ≤ R * (1 / 2 : ℝ) ^ n := by
    intro x
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one
      (div_pos (hf x).1 hR) ((div_le_one hR).mpr (hf x).2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_, ?_⟩
    · have ht := (lt_div_iff₀ hR).mp hn
      nlinarith
    · have ht := (div_le_iff₀ hR).mp hn'
      nlinarith
  choose k hk using hchoose
  let N : Finset ℕ := Finset.univ.image k
  let W : ℝ := A * R * (R / 2) ^ (-γ)
  let q : ℝ := (1 / 2 : ℝ) ^ (1 - γ)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hsum : ∑ x, (f x) ^ (-γ) =
      ∑ n ∈ N, ∑ x ∈ Finset.univ.filter (fun x => k x = n), (f x) ^ (-γ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) _
  have hshell (n : ℕ) :
      ∑ x ∈ Finset.univ.filter (fun x => k x = n), (f x) ^ (-γ) ≤ W * q ^ n := by
    let B : Finset X := Finset.univ.filter (fun x => k x = n)
    have hBn : (B.card : ℝ) ≤ A * (R * (1 / 2 : ℝ) ^ n) := by
      have hsub : B ⊆ Finset.univ.filter (fun x => f x ≤ R * (1 / 2 : ℝ) ^ n) := by
        intro x hx
        have hkn := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hkn] using (hk x).2⟩
      have hcard : (B.card : ℝ) ≤
          ((Finset.univ.filter (fun x => f x ≤ R * (1 / 2 : ℝ) ^ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hcount _ (by positivity))
    calc ∑ x ∈ B, (f x) ^ (-γ) ≤
          ∑ _x ∈ B, (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (-γ) := by
            apply Finset.sum_le_sum
            intro x hx
            have hkn := (Finset.mem_filter.mp hx).2
            have hlow : R * (1 / 2 : ℝ) ^ (n + 1) < f x := by
              simpa only [hkn] using (hk x).1
            exact Real.rpow_le_rpow_of_nonpos (by positivity) hlow.le (neg_nonpos.mpr hγ)
      _ = (B.card : ℝ) * (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (-γ) := by simp
      _ ≤ (A * (R * (1 / 2 : ℝ) ^ n)) *
          (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (-γ) :=
            mul_le_mul_of_nonneg_right hBn (by positivity)
      _ = W * q ^ n := dyadic_weight_identity hR n
  have hgeom : ∑ n ∈ N, q ^ n ≤ (1 - q)⁻¹ := by
    have ht := (summable_geometric_of_lt_one hq hq1).sum_le_tsum N (fun n _ => pow_nonneg hq n)
    simpa only [tsum_geometric_of_lt_one hq hq1] using ht
  calc ∑ x, (f x) ^ (-γ) =
        ∑ n ∈ N, ∑ x ∈ Finset.univ.filter (fun x => k x = n), (f x) ^ (-γ) := hsum
    _ ≤ ∑ n ∈ N, W * q ^ n := Finset.sum_le_sum (fun n _ => hshell n)
    _ = W * ∑ n ∈ N, q ^ n := (Finset.mul_sum _ _ _).symm
    _ ≤ W * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hgeom hW
    _ = _ := by rw [div_eq_mul_inv]

end WangZahlLot.Obl.wz_separated_projection_dichotomy
