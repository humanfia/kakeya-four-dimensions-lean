-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.PowerFromLinearity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridMassParameters
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.VerticalHeight
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.VerticalRefinement

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

/-- Once single-scale affine selection is available, all remaining extraction
steps follow: iterate at interior scales, remove nearly horizontal tubes, prune
height grids, and smooth the successive affine differences. -/
theorem powerApproximation_of_singleScaleLinearity {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hlinearity : SingleScaleLinearity σ) :
    PowerApproximation σ := by
  obtain ⟨C, hC, hsmooth⟩ := smooth_shadings_from_affine_fits
  intro κ hκ hκ1
  obtain ⟨N, ζ, θ, d₁, hN, hζ, hθ, _, _, hd₁, hparams⟩ :=
    exists_interior_scale_parameters hκ hκ1 hC
  obtain ⟨β, d₂, hβ, hβκ, hd₂, hmassparams⟩ := exists_grid_mass_parameters hκ hκ1 hζ hN
  obtain ⟨ηv, d₃, hηv, hηvβ, hd₃, hvertical⟩ := vertical_refinement hσ0 hσ1 hβ
  let scale : Fin N → ℝ → ℝ := fun k δ => (δ ^ (1 - κ)) ^ (((k : ℝ) + 1) / N)
  obtain ⟨η, d₄, hη, hηηv, hd₄, hfits⟩ :=
    finite_scale_linearity hθ hd₁ hlinearity Finset.univ scale
      (fun k δ hδ hδd hδ1 => (hparams δ hδ hδd hδ1).1 k) ηv hηv
  refine ⟨η, min d₁ (min d₂ (min d₃ d₄)), hη, by linarith,
    lt_min hd₁ (lt_min hd₂ (lt_min hd₃ hd₄)), ?_⟩
  intro δ hδ hδd hδ100 n x v Y f P hfamily hf hfb hgrains
  have hδ1 : δ ≤ 1 := by linarith
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ : δ ≤ d₃ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₄ : δ ≤ d₄ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let G : SlopeGeometry := ⟨n, x, v, f, P⟩
  have hregular : RegularGrainFamily σ η δ G Y := ⟨hδ100, hfamily, hgrains, hf, hfb⟩
  obtain ⟨Y₁, hY₁Y, hY₁regular, hfit₁⟩ := hfits δ hδ hδd₄ G Y hregular
  obtain ⟨Y₂, hY₂Y₁, hY₂family, hY₂grains, hY₂vertical⟩ :=
    hvertical δ hδ hδd₃ hδ100 n x v Y₁ f P hY₁regular.2.1 hf hY₁regular.2.2.1
  have hfit₂ : ∀ k : Fin N, AffineSlopeFit (scale k δ) f Y₂ :=
    fun k => (hfit₁ k (Finset.mem_univ k)).mono hY₂Y₁
  have hY₂ball : (⋃ i, Y₂ i) ⊆ Metric.ball (0 : Space) 1 := by
    apply iUnion_subset
    intro i
    exact (hY₂family.1.2.2.2.2.2.1 i).trans (hY₂family.1.2.2.1 i)
  let t := δ ^ (1 - κ)
  let L := 24 * n * δ ^ 2 / (δ ^ β) ^ 2
  have ht : 0 < t := Real.rpow_pos_of_pos hδ _
  have ht1 : t ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hθv : 0 < δ ^ β := Real.rpow_pos_of_pos hδ _
  have hθv1 : δ ^ β ≤ 1 := Real.rpow_le_one hδ.le hδ1 hβ.le
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hheight : ∀ l u : ℝ, shadingHeightMeasure Y₂ (Icc l u) ≤
      ENNReal.ofReal L * ENNReal.ofReal (u - l) := by
    intro l u
    apply vertical_shadingHeightMeasure hδ hθv hθv1 hY₂family.1.2.1
      hY₂family.1.2.2.2.2.1 hY₂family.1.2.2.2.2.2.1
    intro i
    by_cases hi : Y₂ i = ∅
    · exact Or.inl hi
    · exact Or.inr (hY₂vertical i hi)
  obtain ⟨Z, g, hZY₂, hZcompact, hmass, hg, hgf, hgb⟩ :=
    hsmooth N t ζ L n Y₂ f hN ht ht1 hζ.le hL hY₂family.2.2.1 hY₂ball hheight hfb hfit₂
  let A := δ ^ β * n * δ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have herror : 55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ)))) ≤ A / 2 :=
    (hmassparams δ hδ hδd₂ hδ1).2 n
  have hhalf : ENNReal.ofReal (A / 2) ≤ ∑ i, volume (Z i) := by
    apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal (A / 2) + ENNReal.ofReal (A / 2) = ENNReal.ofReal A := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ ∑ i, volume (Y₂ i) := hY₂family.1.2.2.2.2.2.2
      _ ≤ (∑ i, volume (Z i)) +
          ENNReal.ofReal (55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) := hmass
      _ ≤ (∑ i, volume (Z i)) + ENNReal.ofReal (A / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal herror)
  have hmassY : (∑ i, volume (Y i)) ≤ ENNReal.ofReal (384 * n * δ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (384 * δ ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact (measure_mono (hfamily.1.2.2.2.2.2.1 i)).trans
          (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 _ _ (hfamily.1.2.1 i))
      _ = ENNReal.ofReal (384 * n * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show 384 * (n : ℝ) * δ ^ 2 = (n : ℝ) * (384 * δ ^ 2) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hretain : ENNReal.ofReal (δ ^ κ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
    apply le_trans _ hhalf
    calc
      _ ≤ ENNReal.ofReal (δ ^ κ) * ENNReal.ofReal (384 * n * δ ^ 2) :=
        mul_le_mul' le_rfl hmassY
      _ = ENNReal.ofReal (384 * δ ^ κ * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (A / 2) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (δ ^ β / 2) * n * δ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hmassparams δ hδ hδd₂ hδ1).1 (Nat.cast_nonneg _))
              (sq_nonneg _)
          _ = A / 2 := by dsimp [A]; ring
  have hbudget : C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ≤ δ ^ (-κ) :=
    (hparams δ hδ hδd₁ hδ1).2
  exact ⟨Z, g, fun i => (hZY₂ i).trans ((hY₂Y₁ i).trans (hY₁Y i)),
    fun i => (hZcompact i).measurableSet, hretain, hg.of_le (by simp),
    fun z => ⟨(hgb z).1.trans hbudget, (hgb z).2.1.trans hbudget, (hgb z).2.2.trans hbudget⟩,
    fun p hp => by simpa only [abs_sub_comm] using hgf p hp⟩

theorem smoothExamples_of_singleScaleLinearity {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hlinearity : SingleScaleLinearity σ)
    (hL : LipschitzExamples σ) : SmoothExamples σ :=
  smoothExamples_of_powerApproximation hσ0.le hσ1.le
    (powerApproximation_of_singleScaleLinearity hσ0 hσ1 hlinearity) hL

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
