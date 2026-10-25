-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.QuarterThinTubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.SeedBudget
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.DyadicGoodPairs
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.LineCounting

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

/-- Elementary seed for radial projection bootstrapping. Weak line
nonconcentration gives quarter-dimensional thin tubes after discarding a
small fraction of endpoint pairs. This is the finite counting analogue of
sticky Lemma 8.8, with an explicit absolute constant. -/
theorem exists_quarter_thin_tubes {ℓ ζ α : ℝ} (hℓ : 0 < ℓ) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hα : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (I J : Type) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
        (f : I → Plane) (g : J → Plane),
      IndexedFrostman δ (δ ^ (-ℓ)) f → IndexedFrostman δ (δ ^ (-ℓ)) g →
      IndexedLineFrostman δ (δ ^ (-ℓ)) ζ g →
      (∀ i j, 1 / 4 ≤ ‖f i - g j‖ ∧ ‖f i - g j‖ ≤ 8) →
      ∃ R : I → J → Prop,
        ((Finset.univ.filter (fun p : I × J => ¬R p.1 p.2)).card : ℝ) ≤
          δ ^ α * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) ∧
        ∀ (i : I) (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
          ((Finset.univ.filter (fun j => R i j ∧ |inner ℝ (g j - f i) u| < r)).card : ℝ) ≤
            (32 * δ ^ (-(ℓ + 3 * α / ζ))) * r ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) := by
  classical
  let A := ℓ + 3 * α / ζ
  have hApos : 0 < A := by dsimp [A]; positivity
  by_cases hA : A < 1 / 4
  · obtain ⟨δ₁, hδ₁, hδ₁1, hseed⟩ := exists_seed_budget hℓ hζ hζ1 hα hA
    obtain ⟨δ₂, hδ₂, hδ₂1, hdepth⟩ := exists_dyadic_depth_budget (p := α / 4) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁1, ?_⟩
    intro δ hδ hsmall I J _ _ _ _ f g hF hG hline hpoints
    have hδ1 := (hsmall.trans (min_le_left _ _)).trans hδ₁1
    obtain ⟨hδq, hδs, hqs, hsmallK, hgain⟩ := hseed δ hδ (hsmall.trans (min_le_left _ _))
    obtain ⟨n, hn, hn', hnum⟩ := hdepth δ hδ (hsmall.trans (min_le_right _ _))
    let K := δ ^ (-A)
    have hK : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    have hscales (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
        ((Finset.univ.filter (fun p : I × J =>
          HeavyRelation f g (dyadicRadius k) (K * (dyadicRadius k) ^ (1 / 4 : ℝ)) p.1 p.2)).card : ℝ) ≤
            δ ^ (5 * α / 4) * (Fintype.card I : ℝ) * (Fintype.card J : ℝ) := by
      have hδr : δ ≤ dyadicRadius k := hn.trans
        (dyadicRadius_antitone (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
      exact (quarter_heavy_relation_card_lt f g hF hG hδ (by positivity)
        (by positivity : 0 < δ ^ (ℓ + 3 * α))
        (by positivity : 0 < δ ^ (ℓ + 3 * α / ζ)) (by positivity : 0 < K)
        (by positivity : 0 ≤ (δ ^ (-ℓ) * δ ^ (ℓ + 3 * α / ζ)) ^ ζ)
        (by positivity : 0 < δ ^ (5 * α / 4)) hδq hδr hqs hsmallK hpoints
        (fun i i' hii => hline.joining_line_count (f i) (f i') hii hδs) hgain).le
    have hbudget : ((n + 1 : ℕ) : ℝ) * δ ^ (5 * α / 4) ≤ δ ^ α := by
      have heq : δ ^ (5 * α / 4) = δ ^ (α / 4) * δ ^ α := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      rw [heq, ← mul_assoc]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ δ ^ α)
    exact exists_dyadic_good_pairs f g hδ hK hn' (fun i j => (hpoints i j).1) hscales hbudget
  · refine ⟨1, zero_lt_one, le_rfl, ?_⟩
    intro δ hδ hδ1 I J _ _ _ _ f g hF hG hline hpoints
    let R : I → J → Prop := fun _ _ => True
    refine ⟨R, ?_, ?_⟩
    · simp only [R, not_true_eq_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
      positivity
    · intro i u r hu hr
      have hpow : 1 ≤ δ ^ (-A) * δ ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hδ]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
      have hp : δ ^ (1 / 4 : ℝ) ≤ r ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hδ.le hr (by norm_num)
      have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ δ ^ (-A))
      have hfac : 1 ≤ 32 * δ ^ (-A) * r ^ (1 / 4 : ℝ) := by nlinarith
      have hc : ((Finset.univ.filter (fun j => R i j ∧ |inner ℝ (g j - f i) u| < r)).card : ℝ) ≤
          (Fintype.card J : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset J) _).trans_eq Finset.card_univ
      have hb : (Fintype.card J : ℝ) ≤
          (32 * δ ^ (-A)) * r ^ (1 / 4 : ℝ) * (Fintype.card J : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
      convert hc.trans hb using 1 <;> congr 2 <;> ext p <;> simp [R]

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
