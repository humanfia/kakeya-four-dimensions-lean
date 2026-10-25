-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.PowerTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.CoarsePerturb
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.CompactSelection
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomMain

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal

/-- Compact shading restriction preserves the family with the stated density loss. -/
theorem ExtremalFamily.restrict {σ η a ε δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y Z : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) (hbudget : η + a ≤ ε)
    (h : ExtremalFamily σ η δ n x v Y)
    (hZY : ∀ i, Z i ⊆ Y i) (hZ : ∀ i, IsCompact (Z i))
    (hmass : ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    ExtremalFamily σ ε δ n x v Z := by
  refine ⟨dense_restrict hδ hδ1 hbudget h.1 hZY (fun i => (hZ i).measurableSet) hmass,
    strong_mono_error hδ hδ1 hηε h.2.1, hZ, ?_⟩
  exact (measure_mono (iUnion_mono hZY)).trans (h.2.2.2.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (sub_le_sub_left hηε σ))))

/-- Measurable selections and a coarser approximation suffice for the exact family
and grains conditions; compact approximation costs one further small power. -/
theorem compact_power_slope_transfer {η a b ε σ δ κ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hηε : η ≤ ε) (hmassbudget : η + (a + b) ≤ ε)
    (hcoverbudget : 18 * δ ^ (-(η + κ)) ≤ δ ^ (-ε)) (hcompactbudget : δ ^ b ≤ 1 / 2)
    (hfamily : ExtremalFamily σ η δ n x v Y)
    (hgrains : Grains σ δ (δ ^ (-η)) v Y f P)
    (hZ : ∀ i, Z i ⊆ Y i) (hmeas : ∀ i, MeasurableSet (Z i))
    (hmass : ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (happrox : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ ^ (1 - κ)) :
    ∃ K : Fin n → Set Space, (∀ i, K i ⊆ Z i) ∧
      ExtremalFamily σ ε δ n x v K ∧ Grains σ δ (δ ^ (-ε)) v K g P := by
  have hball : (⋃ i, Y i) ⊆ ball (0 : Space) 1 := by
    apply iUnion_subset
    intro i
    exact (hfamily.1.2.2.2.2.2.1 i).trans (hfamily.1.2.2.1 i)
  have hfinite : ∀ i, volume (Z i) ≠ ⊤ := fun i =>
    ((measure_mono ((hZ i).trans ((subset_iUnion Y i).trans hball))).trans_lt
      measure_ball_lt_top).ne
  obtain ⟨K, hKZ, hK, hKmass⟩ := compact_shadings Z hmeas hfinite
  have hhalf : ENNReal.ofReal (δ ^ b) ≤ (1 / 2 : ENNReal) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hcompactbudget
  have hretained : ENNReal.ofReal (δ ^ (a + b)) * (∑ i, volume (Y i)) ≤
      ∑ i, volume (K i) := by
    calc
      ENNReal.ofReal (δ ^ (a + b)) * (∑ i, volume (Y i))
          = ENNReal.ofReal (δ ^ b) *
              (ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i))) := by
                rw [Real.rpow_add hδ, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
                ac_rfl
      _ ≤ (1 / 2 : ENNReal) * (∑ i, volume (Z i)) := mul_le_mul' hhalf hmass
      _ ≤ ∑ i, volume (K i) := hKmass
  have hKY : ∀ i, K i ⊆ Y i := fun i => (hKZ i).trans (hZ i)
  refine ⟨K, hKZ, hfamily.restrict hδ hδ1 hηε hmassbudget hKY hK hretained, ?_⟩
  apply hgrains.replace_slope_power hδ hδ1 hκ hσ0 hσ1
    (Real.rpow_nonneg hδ.le _) ?_ hKY
    (coordinate_bound_of_subset_ball ((iUnion_mono hKY).trans hball))
    (fun p hp => happrox p ((iUnion_mono hKZ) hp))
  convert hcoverbudget using 1
  rw [mul_assoc, ← Real.rpow_add hδ]
  congr 2
  ring

/-- The remaining geometric input may stop short of the finest scale. Its slope
error, derivative bounds, and mass loss are all controlled by an arbitrarily small
power. The selected shadings need only be measurable. -/
def PowerApproximation (σ : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 1 → ∃ η d₁ : ℝ, 0 < η ∧ η ≤ κ ∧ 0 < d₁ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₁ → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
      (f : ℝ → ℝ) (P : Space → Space),
      ExtremalFamily σ η δ n x v Y → LipschitzWith 1 f →
      (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 3) →
      Grains σ δ (δ ^ (-η)) v Y f P →
      ∃ (Z : Fin n → Set Space) (g : ℝ → ℝ),
        (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet (Z i)) ∧
        ENNReal.ofReal (δ ^ κ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
        ContDiff ℝ 2 g ∧
        (∀ z, |g z| ≤ δ ^ (-κ) ∧ |deriv g z| ≤ δ ^ (-κ) ∧
          |deriv (deriv g) z| ≤ δ ^ (-κ)) ∧
        (∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ ^ (1 - κ))

/-- The coarse approximation input yields the weak smooth examples needed by
normalization, with every covering estimate still at the original tube scale. -/
theorem weakSmoothExamples_of_powerApproximation {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : PowerApproximation σ)
    (hL : LipschitzExamples σ) : WeakSmoothExamples σ := by
  intro ε d₀ hε hd₀
  let κ := min (ε / 4) (1 / 4)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκe : κ ≤ ε / 4 := min_le_left _ _
  have hκ1 : κ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨η, d₁, hη, hηκ, hd₁, happrox⟩ := hA κ hκ hκ1
  have hgap : 0 < ε - (η + κ) := by linarith
  obtain ⟨d₂, hd₂, hconstant⟩ := cut_le_one hgap 18
  obtain ⟨d₃, hd₃, hcompact⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hκ
      (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hfamily, f, P, hf, hfb, hgrains⟩ :=
    hL.bounded_slope η (min d₀ (min d₁ (min d₂ d₃))) hη
      (lt_min hd₀ (lt_min hd₁ (lt_min hd₂ hd₃)))
  have hδ1 : δ ≤ 1 := by linarith
  have hδd₀ : δ ≤ d₀ := hδd.trans (min_le_left _ _)
  have hδd₁ : δ ≤ d₁ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₃ : δ ≤ d₃ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Z, g, hZY, hZm, hmass, hg, hgb, hgf⟩ :=
    happrox δ hδ hδd₁ hδ100 n x v Y f P hfamily hf hfb hgrains
  have hcover : 18 * δ ^ (-(η + κ)) ≤ δ ^ (-ε) := by
    have heq : δ ^ (-(η + κ)) = δ ^ (ε - (η + κ)) * δ ^ (-ε) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [heq, ← mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (hconstant δ hδ hδd₂) (Real.rpow_nonneg hδ.le (-ε))
  obtain ⟨K, hKZ, hKF, hKG⟩ := compact_power_slope_transfer
    (a := κ) (b := κ) hδ hδ1 hκ.le hσ0 hσ1 (by linarith) (by linarith)
    hcover (hcompact δ hδ hδd₃) hfamily hgrains hZY hZm hmass hgf
  have hpow : δ ^ (-κ) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact ⟨δ, hδ, hδd₀, hδ100, n, x, v, K, hKF, g, P,
    ⟨hg, fun z => ⟨(hgb z).1.trans hpow, (hgb z).2.1.trans hpow,
      (hgb z).2.2.trans hpow⟩⟩, hKG⟩

/-- All analytic and normalization steps of the frozen conclusion follow from
power-accurate smooth approximation on retained shadings. -/
theorem smoothExamples_of_powerApproximation {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : PowerApproximation σ)
    (hL : LipschitzExamples σ) : SmoothExamples σ :=
  normalize hσ0 hσ1 (weakSmoothExamples_of_powerApproximation hσ0 hσ1 hA hL)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
