-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.Double.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Mono

/-!
# Changing the coarse radius of a broad cover

`Broad` at radius `ρ` gives `Broad` at any radius `ρ' ∈ [ρ, 2ρ]` after a constant loss in the
error: for `r ≤ ρ` the input bound loses `(ρ'/ρ)^β ≤ 2`, and for `ρ < r ≤ ρ'` the bound is
trivial once `δ^(-h') ≥ 2`, since `(r/ρ')^β ≥ 1/2` for `β ≤ 1`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

theorem broad_enlarge {ω ζ d h h' ρ ρ' : ℝ} {n N : ℕ} {v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hd : 0 < d) (hω : 0 < ω) (hω1 : ω ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hρ : 0 < ρ) (hρρ' : ρ ≤ ρ') (hρ'2 : ρ' ≤ 2 * ρ)
    (hloss : 2 * d ^ (-h) ≤ d ^ (-h')) (htwo : 2 ≤ d ^ (-h'))
    (hb : Broad ω ζ d h ρ n N v S Z f) : Broad ω ζ d h' ρ' n N v S Z f := by
  intro k p u r hu hdr hrρ'
  have hr : 0 < r := hd.trans_le hdr
  have hρ' : 0 < ρ' := hρ.trans_le hρρ'
  set β := ω * ζ / 100 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : β ≤ 1 := by
    have : ω * ζ ≤ 1 * 1 := mul_le_mul hω1 hζ1 hζ.le zero_le_one
    rw [hβ]; linarith
  set tot := q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} with htot
  have htot0 : 0 ≤ tot := Nat.cast_nonneg _
  have hsub : q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤ tot := by
    show (Set.ncard _ : ℝ) ≤ (Set.ncard _ : ℝ)
    have hss : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ⊆
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := fun i hi => ⟨hi.1, hi.2.1, hi.2.2.1⟩
    exact_mod_cast Set.ncard_le_ncard hss (Set.toFinite _)
  by_cases hrρ : r ≤ ρ
  · -- the input bound, with (r/ρ)^β ≤ 2 (r/ρ')^β
    have h1 := hb k p u r hu hdr hrρ
    have hratio : (r / ρ) ^ β ≤ 2 * (r / ρ') ^ β := by
      have hsplit : r / ρ = (ρ' / ρ) * (r / ρ') := by field_simp
      rw [hsplit, Real.mul_rpow (by positivity) (by positivity)]
      have hq : (ρ' / ρ) ^ β ≤ 2 := by
        have h2 : ρ' / ρ ≤ 2 := by rw [div_le_iff₀ hρ]; linarith
        have h1' : 1 ≤ ρ' / ρ := by rw [le_div_iff₀ hρ]; linarith
        calc (ρ' / ρ) ^ β ≤ (ρ' / ρ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1' hβ1
          _ = ρ' / ρ := Real.rpow_one _
          _ ≤ 2 := h2
      exact mul_le_mul_of_nonneg_right hq (by positivity)
    calc _ ≤ d ^ (-h) * (r / ρ) ^ β * tot := h1
      _ ≤ d ^ (-h) * (2 * (r / ρ') ^ β) * tot := by
          gcongr
      _ = (2 * d ^ (-h)) * (r / ρ') ^ β * tot := by ring
      _ ≤ d ^ (-h') * (r / ρ') ^ β * tot := by
          gcongr
  · -- trivial range: (r/ρ')^β ≥ 1/2
    rw [not_le] at hrρ
    have hhalf : (1 / 2 : ℝ) ≤ (r / ρ') ^ β := by
      have hge : 1 / 2 ≤ r / ρ' := by
        rw [le_div_iff₀ hρ']; linarith
      have hle1 : r / ρ' ≤ 1 := by rw [div_le_one hρ']; exact hrρ'
      calc (1 / 2 : ℝ) ≤ r / ρ' := hge
        _ = (r / ρ') ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (r / ρ') ^ β := Real.rpow_le_rpow_of_exponent_ge (by linarith) hle1 hβ1
    calc _ ≤ tot := hsub
      _ = 1 * tot := (one_mul _).symm
      _ ≤ (d ^ (-h') * (r / ρ') ^ β) * tot := by
          apply mul_le_mul_of_nonneg_right _ htot0
          calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
            _ ≤ d ^ (-h') * (r / ρ') ^ β := mul_le_mul htwo hhalf (by norm_num) (by positivity)
      _ = d ^ (-h') * (r / ρ') ^ β * tot := by ring

end WangZahlLot.Obl.wz_coarse_grains_assembly
