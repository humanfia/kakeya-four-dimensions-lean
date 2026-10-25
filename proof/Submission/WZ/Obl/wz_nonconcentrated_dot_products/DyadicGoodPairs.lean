-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.DyadicGoodPairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.ThinFromCaps

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Discarding the union of scale-wise heavy pairs leaves a single relation
that satisfies the thin-tube estimate at every radius. -/
theorem exists_dyadic_good_pairs {I J : Type*} [Fintype I] [Fintype J]
    (f : I → Plane) (g : J → Plane) {δ K a c : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hK : 1 ≤ K) (hlast : dyadicRadius (n + 1) < δ)
    (hsep : ∀ i j, 1 / 4 ≤ ‖f i - g j‖)
    (hscales : ∀ k ∈ Finset.range (n + 1),
      ((Finset.univ.filter (fun p : I × J =>
        HeavyRelation f g (dyadicRadius k) (K * (dyadicRadius k) ^ (1 / 4 : ℝ)) p.1 p.2)).card : ℝ) ≤
          a * (Fintype.card I : ℝ) * (Fintype.card J : ℝ))
    (hbudget : ((n + 1 : ℕ) : ℝ) * a ≤ c) :
    ∃ R : I → J → Prop,
      ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
        c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ∧
      ∀ (i : I) (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
        ((Finset.univ.filter (fun j => R i j ∧ |inner ℝ (g j - f i) u| < r)).card : ℝ) ≤
          32 * K * r ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) := by
  classical
  let B (k : ℕ) : Finset (I × J) := Finset.univ.filter (fun p =>
    HeavyRelation f g (dyadicRadius k) (K * (dyadicRadius k) ^ (1 / 4 : ℝ)) p.1 p.2)
  let R (i : I) (j : J) : Prop := ∀ k ∈ Finset.range (n + 1), (i, j) ∉ B k
  have hsub : Finset.univ.filter (fun p : I × J => ¬R p.1 p.2) ⊆
      (Finset.range (n + 1)).biUnion B := by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2
    simp only [R, not_forall, Classical.not_imp, not_not] at hh
    obtain ⟨k, hk, hp⟩ := hh
    exact Finset.mem_biUnion.mpr ⟨k, hk, hp⟩
  refine ⟨R, ?_, ?_⟩
  · have hcount : ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
        ∑ k ∈ Finset.range (n + 1), ((B k).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hfinal : ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
        c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by
      calc ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
            ∑ k ∈ Finset.range (n + 1), ((B k).card : ℝ) := hcount
        _ ≤ ∑ _k ∈ Finset.range (n + 1), a * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) :=
          Finset.sum_le_sum hscales
        _ = (((n + 1 : ℕ) : ℝ) * a) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by simp; ring
        _ ≤ c * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by gcongr
    convert hfinal using 1 <;> congr 2 <;> ext p <;> simp
  · intro i
    apply radial_thin_of_good_caps g (R i) (f i) hδ hK hlast (hsep i)
    intro j hj k hk
    have hh := hj k hk
    have hn : ¬HeavyRelation f g (dyadicRadius k)
        (K * (dyadicRadius k) ^ (1 / 4 : ℝ)) i j := by
      intro h
      exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact lt_of_not_ge hn

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
