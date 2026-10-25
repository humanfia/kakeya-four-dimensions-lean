-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.PowerCountingEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.TruncatedEnergy

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- Snowflaking converts a power counting estimate into the linear
counting estimate used by the geometric-annulus energy lemma. -/
theorem sum_rpow_neg_mul_le_of_power_count {X : Type*} [Fintype X] (f : X → ℝ)
    {C s γ : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hf : ∀ x, 0 < f x ∧ f x ≤ 1)
    (hcount : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun x => f x ≤ r)).card : ℝ) ≤ C * r ^ s) :
    ∑ x, (f x) ^ (-(s * γ)) ≤ C * energyConstant γ := by
  classical
  have htrans : ∀ r : ℝ, 0 < r →
      ((Finset.univ.filter (fun x => (f x) ^ s ≤ r)).card : ℝ) ≤ C * r := by
    intro r hr
    have hsub : Finset.univ.filter (fun x => (f x) ^ s ≤ r) ⊆
        Finset.univ.filter (fun x => f x ≤ r ^ s⁻¹) := by
      intro x hx
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg (hf x).1.le s)
        (Finset.mem_filter.mp hx).2 (inv_nonneg.mpr hs.le)
      have hid : ((f x) ^ s) ^ s⁻¹ = f x := by
        rw [← Real.rpow_mul (hf x).1.le, mul_inv_cancel₀ hs.ne', Real.rpow_one]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hid] at hh⟩
    have hh := (show ((Finset.univ.filter (fun x => (f x) ^ s ≤ r)).card : ℝ) ≤
        ((Finset.univ.filter (fun x => f x ≤ r ^ s⁻¹)).card : ℝ) by exact_mod_cast Finset.card_le_card hsub).trans
      (hcount _ (Real.rpow_pos_of_pos hr _))
    rwa [← Real.rpow_mul hr.le, inv_mul_cancel₀ hs.ne', Real.rpow_one] at hh
  have hh := sum_rpow_neg_le_of_count (fun x => (f x) ^ s) (R := 1) hC (by norm_num) hγ hγ1
    (fun x => ⟨Real.rpow_pos_of_pos (hf x).1 s, Real.rpow_le_one (hf x).1.le (hf x).2 hs.le⟩) htrans
  have heq (x : X) : ((f x) ^ s) ^ (-γ) = (f x) ^ (-(s * γ)) := by
    rw [← Real.rpow_mul (hf x).1.le]; congr 1; ring
  simpa only [heq, one_div, mul_one, energyConstant, div_eq_mul_inv, mul_assoc] using hh

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
