-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.VerticalRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.NearHorizontal
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.LogCutoff
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.VerticalRestrictions

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- Every tube carrying shading has a quantitatively nonzero vertical component. -/
def Vertical (η δ : ℝ) {n : ℕ} (v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∀ i, Y i ≠ ∅ → δ ^ η ≤ |v i 2|

/-- Removing almost-horizontal tubes costs an arbitrarily small power of the scale. -/
theorem vertical_refinement {σ ε : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
        (f : ℝ → ℝ) (P : Space → Space),
        ExtremalFamily σ η δ n x v Y → LipschitzWith 1 f →
        Grains σ δ (δ ^ (-η)) v Y f P →
        ∃ Z : Fin n → Set Space, (∀ i, Z i ⊆ Y i) ∧
          ExtremalFamily σ ε δ n x v Z ∧
          Grains σ δ (δ ^ (-ε)) v Z f P ∧ Vertical ε δ v Z := by
  classical
  obtain ⟨K, hK, hnear⟩ := near_horizontal_mass_unbounded
  let c : ℝ := min (ε / 2) (1 / 2)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcε : c ≤ ε / 2 := min_le_left _ _
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  let η : ℝ := c * σ / 32
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by
    have hcs : c * σ < c := by nlinarith
    dsimp [η]
    linarith
  have hgap : η < c * σ / 4 - 2 * η := by
    dsimp [η]
    nlinarith [mul_pos hc hσ0]
  obtain ⟨d₁, hd₁, hlog⟩ := exists_log_power_comparison K
    (B := 1 / 2) (by norm_num) hgap
  obtain ⟨d₂, hd₂, hsmall⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hc
      (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨d₃, hd₃, hhalf⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff (sub_pos.mpr hηε)
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨η, min d₁ (min d₂ d₃), hη, hηε.le,
    lt_min hd₁ (lt_min hd₂ hd₃), ?_⟩
  intro δ hδ hδd hδ100 n x v Y f P hfamily hf hgrains
  have hδ1 : δ ≤ 1 := by linarith
  have hδd₁ : δ ≤ d₁ := hδd.trans (min_le_left _ _)
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₃ : δ ≤ d₃ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδθ : δ ≤ δ ^ c := by
    conv_lhs => rw [← Real.rpow_one δ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hθ100 : δ ^ c ≤ 1 / 100 := hsmall δ hδ hδd₂
  have hcoefficient : K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) *
      (δ ^ c) ^ (σ / 4) ≤ (1 / 2 : ℝ) * δ ^ η := by
    calc
      K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4)
          = K * (1 + Real.log (1 / δ)) *
              (δ ^ (-2 * η) * (δ ^ c) ^ (σ / 4)) := by ring
      _ = K * (1 + Real.log (1 / δ)) * δ ^ (c * σ / 4 - 2 * η) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ _ := hlog δ hδ hδd₁
  have hbasic : BasicFamily δ n x v Y :=
    ⟨hfamily.1.2.1, hfamily.1.2.2.1, hfamily.1.2.2.2.2.1,
      hfamily.1.2.2.2.2.2.1⟩
  have hcount := WangZahlLot.Obl.wz_grains_nonsingular_slices.globalCount_of_strong
    hδ hδ1 hfamily.2.1
  have hbad : ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < δ ^ c), volume (Y i) ≤
      (1 / 2 : ENNReal) * ∑ i, volume (Y i) := by
    calc
      _ ≤ ENNReal.ofReal (K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) *
          (δ ^ c) ^ (σ / 4) * n * δ ^ 2) :=
        hnear σ η (δ ^ c) δ hσ0 hσ1 hη hδ hδ100 hδθ hθ100 n x v Y
          hbasic hcount f hf hgrains.1
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (δ ^ η * n * δ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ ((1 / 2 : ℝ) * δ ^ η) * n * δ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg _)) (sq_nonneg _)
          _ = _ := by ring
      _ = (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := mul_le_mul' le_rfl hfamily.1.2.2.2.2.2.2
  let Z : Fin n → Set Space := fun i => if |v i 2| < δ ^ c then ∅ else Y i
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i
    dsimp [Z]
    split_ifs <;> simp
  have hZcompact : ∀ i, IsCompact (Z i) := by
    intro i
    dsimp [Z]
    split_ifs
    · exact isCompact_empty
    · exact hfamily.2.2.1 i
  have hmass : (1 / 2 : ENNReal) * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) := by
    have h := half_mass_after_deletion (fun i => volume (Y i))
      (fun i => |v i 2| < δ ^ c) (fun i => (hfamily.2.2.1 i).measure_lt_top.ne) hbad
    simpa only [Finset.sum_filter, ite_not, Z, apply_ite, measure_empty] using h
  have hhalf' : ENNReal.ofReal (δ ^ (ε - η)) ≤ (1 / 2 : ENNReal) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal (hhalf δ hδ hδd₃)
  refine ⟨Z, hZY, hfamily.restrict hδ hδ1 hηε.le (by linarith) hZY hZcompact
    ((mul_le_mul' hhalf' le_rfl).trans hmass),
    hgrains.restrict_mono hδ
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε.le)) hZY, ?_⟩
  intro i hi
  have hnot : ¬ |v i 2| < δ ^ c := by
    intro hlt
    exact hi (by simp [Z, hlt])
  exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : c ≤ ε)).trans
    (le_of_not_gt hnot)


end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
