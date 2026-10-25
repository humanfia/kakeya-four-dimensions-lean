-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RatioGapFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RatioExpansion
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DenseRatioProducts

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

attribute [local instance] Classical.propDecidable

theorem finset_subtype_filter_card {X : Type*} (A : Finset X) (P : X → Prop) :
    (Finset.univ.filter (fun x : A => P x)).card = (A.filter P).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_coe_sort A (fun x => if P x then (1 : ℕ) else 0)

/-- A slope outside the truncated ratio family expands the Cartesian
product, with both local Frostman losses recorded. -/
theorem ratio_gap_frostman_count {δ ρ q C σ t : ℝ} (hδ : 0 < δ)
    (hδρ : δ ≤ ρ) (hδq : δ ≤ q) (hC : 0 ≤ C) (A : Finset ℝ) (hA : A.Nonempty)
    (hAF : RealFiniteFrostman δ C σ A)
    (hgap : ∀ s ∈ LargeDenominatorRatios q A, 2 * ρ / q < dist t s)
    {m : ℕ} (cc : Fin m → ℝ)
    (hcov : Covers ρ ((fun p : ℝ × ℝ => p.1 + t * p.2) ''
      (↑(A ×ˢ A) : Set (ℝ × ℝ))) cc) :
    1 ≤ (m : ℝ) * C ^ 2 * (ρ * q) ^ σ := by
  classical
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hq : 0 < q := hδ.trans_le hδq
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hlocal (s : ℝ) (hs : δ ≤ s) (z : ℝ) :
      ((Finset.univ.filter (fun x : A => |(x : ℝ) - z| ≤ s)).card : ℝ) ≤
        C * s ^ σ * (A.card : ℝ) := by
    rw [finset_subtype_filter_card A (fun x : ℝ => |x - z| ≤ s)]
    simpa only [Real.dist_eq] using hAF z s hs
  have hgap' (i i' j j' : A) (hjj : q ≤ |(j : ℝ) - j'|) :
      2 * ρ / q < |t - ((i : ℝ) - i') / ((j' : ℝ) - j)| := by
    have hratio : ((i : ℝ) - i') / ((j' : ℝ) - j) ∈ LargeDenominatorRatios q A :=
      ⟨i, i.property, i', i'.property, j', j'.property, j, j.property,
        by simpa only [abs_sub_comm] using hjj, rfl⟩
    simpa only [Real.dist_eq] using hgap _ hratio
  have hcov' : Covers ρ (Set.range (fun p : A × A => (p.1 : ℝ) + t * (p.2 : ℝ))) cc := by
    rintro z ⟨p, rfl⟩
    exact hcov ⟨((p.1 : ℝ), (p.2 : ℝ)), Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩, rfl⟩
  have hc := ratio_gap_cover_bound (fun x : A => (x : ℝ)) (fun x : A => (x : ℝ))
    hρ.le hq (by positivity : 0 ≤ C * ρ ^ σ * (A.card : ℝ))
    (by positivity : 0 ≤ C * q ^ σ * (A.card : ℝ))
    (hlocal ρ hδρ) (hlocal q hδq) hgap' m cc hcov'
  simp only [Fintype.card_coe] at hc
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (A.card : ℝ) ^ 2)).mp
  calc 1 * (A.card : ℝ) ^ 2 = (A.card : ℝ) * (A.card : ℝ) := by ring
    _ ≤ (m : ℝ) * ((C * ρ ^ σ * (A.card : ℝ)) * (C * q ^ σ * (A.card : ℝ))) := hc
    _ = ((m : ℝ) * C ^ 2 * (ρ * q) ^ σ) * (A.card : ℝ) ^ 2 := by
      rw [Real.mul_rpow hρ.le hq.le]
      ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
