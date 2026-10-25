-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FactorDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatQuantitative
import Submission.WZ.Obl.wz_concentrated_convex_factorization
import Submission.WZ.Obl.wz_tube_packing_bound

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file FactorDichotomy.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

/-- Apply the accepted quantitative convex factorization, using the accepted
four-dimensional tube-packing bound for its polynomial cardinality hypothesis. -/
theorem exists_long_factor (ν : ℝ) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → δ ≤ d →
      ∀ (m : ℝ), 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → Space),
      0 < n → (∀ i, ‖v i‖ = 1) →
      (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
      Distinct (fun i => Tube δ (x i) (v i)) →
      KatzTao δ m (fun i => Tube δ (x i) (v i)) →
      ∃ a b : ℝ, δ ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧
        LongFactor ν δ a b (fun i => Tube δ (x i) (v i)) := by
  obtain ⟨C, hC, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  obtain ⟨d, hd, hfactor⟩ := WangZahlLot.wz_concentrated_convex_factorization C ν hC hν
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ100 hδd m hm n x v hn hv hball hsep hKT
  obtain ⟨a, b, hδa, hab, hb, k, g, hg, hk, hsize, c, hc, hcm, hKT', p, hp,
    W, hshape, hcover, hdegree, hbalance, hsat, habove, hbelow⟩ :=
    hfactor δ hδ hδ100 hδd m hm n x v hn hv hball hsep
      (hpack δ hδ hδ100 n x v hv hball hsep) hKT
  exact ⟨a, b, hδa, hab, hb, k, g, hg, hk, hsize, c, hc, hKT', p,
    W, hshape, hcover, hdegree, hsat⟩

lemma exists_mul_rpow_cutoff {α C : ℝ} (hα : 0 < α) (hC : 0 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * δ ^ α ≤ 1 := by
  refine ⟨(1 / C) ^ α⁻¹, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro δ hδ hδd
  have hh : δ ^ α ≤ 1 / C := by
    calc
      _ ≤ ((1 / C) ^ α⁻¹) ^ α := Real.rpow_le_rpow hδ.le hδd hα.le
      _ = 1 / C := Real.rpow_inv_rpow (by positivity) hα.ne'
  calc
    _ ≤ C * (1 / C) := mul_le_mul_of_nonneg_left hh hC.le
    _ = 1 := by field_simp

/-- All globally flat factors are now handled.  The remaining alternative has
nonflat factors together with a quantified convex-factorization certificate. -/
theorem flat_output_or_nonflat_factor {ζ ζ₂ ζ₃ θ : ℝ}
    (hζ : 0 ≤ ζ) (hζ₂ : 0 < ζ₂) (hgap : ζ < ζ₃) (hθ : 0 < θ)
    (η : ℝ) (hη : 0 < η) :
    ∃ ν : ℝ, 0 < ν ∧ ν ≤ η ∧ ν ≤ θ / 2 ∧ ν ≤ (ζ₃ - ζ) / 10 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ (ζ₁ : ℝ) (n : ℕ) (x v : Fin n → Space),
        0 < n → (∀ i, ‖v i‖ = 1) →
        (∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
        Distinct (fun i => Tube δ (x i) (v i)) →
        Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)) →
        Output ζ₁ ζ₂ ζ₃ δ θ (fun i => Tube δ (x i) (v i)) ∨
          ∃ a b : ℝ, δ ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧
            δ ^ (ζ₂ / 100) * b < a ∧
            LongFactor ν δ a b (fun i => Tube δ (x i) (v i)) := by
  let ν := min η (min (θ / 2) ((ζ₃ - ζ) / 10))
  have hν : 0 < ν := lt_min hη (lt_min (by positivity) (by linarith))
  have hνη : ν ≤ η := min_le_left _ _
  have hνθ : ν ≤ θ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hνgap : ν ≤ (ζ₃ - ζ) / 10 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨dF, hdF, hfactor⟩ := exists_long_factor ν hν
  obtain ⟨dS, hdS, hscale⟩ := exists_mul_rpow_cutoff
    (show 0 < ζ₂ / 200 by positivity) (show (0 : ℝ) < 2 by norm_num)
  obtain ⟨dE, hdE, herror⟩ := exists_mul_rpow_cutoff
    (show 0 < ζ₃ - ζ - 5 * ν by linarith) (show (0 : ℝ) < 8192 by norm_num)
  obtain ⟨dR, hdR, hretain⟩ := exists_mul_rpow_cutoff
    (show 0 < θ - ν by linarith) (show (0 : ℝ) < 4 by norm_num)
  refine ⟨ν, hν, hνη, hνθ, hνgap, min (1 / 100) (min dF (min dS (min dE dR))),
    lt_min (by norm_num) (lt_min hdF (lt_min hdS (lt_min hdE hdR))), ?_⟩
  intro δ hδ hδ₀ ζ₁ n x v hn hv hball hsep hF
  have hδ100 : δ ≤ 1 / 100 := hδ₀.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hrest := hδ₀.trans (min_le_right _ _)
  have hδF : δ ≤ dF := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hδS : δ ≤ dS := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hδE : δ ≤ dE := hrest''.trans (min_le_left _ _)
  have hδR : δ ≤ dR := hrest''.trans (min_le_right _ _)
  let m := max 1 (δ ^ (-ζ) * n * δ ^ 2)
  have hKT : KatzTao δ m (fun i => Tube δ (x i) (v i)) :=
    (hF.katzTao (Real.rpow_nonneg hδ.le _)).mono (le_max_right _ _)
  obtain ⟨a, b, hδa, hab, hb, hfac⟩ := hfactor δ hδ hδ100 hδF m
    (le_max_left _ _) n x v hn hv hball hsep hKT
  by_cases hflat : a ≤ δ ^ (ζ₂ / 100) * b
  · exact Or.inl (output_of_flat_long_factor _ hδ hδ1 hν.le hζ hδa hab hb hflat
      (hscale δ hδ hδS) (herror δ hδ hδE) (hretain δ hδ hδR) hball hF hfac)
  · exact Or.inr ⟨a, b, hδa, hab, hb, lt_of_not_ge hflat, hfac⟩

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
