-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.Transfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.Normalization
import Submission.WZ.Obl.wz_separated_cover_refinement

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Dense := WangZahlLot.Obl.wz_separated_cover_refinement.Dense
abbrev Strong := WangZahlLot.Obl.wz_separated_cover_refinement.Strong
abbrev CoverAt := WangZahlLot.Obl.wz_separated_cover_refinement.CoverAt

/-- Increasing the covering constant leaves every geometric condition unchanged. -/
theorem coverAt_mono {δ ρ K K' : ℝ} {n k : ℕ}
    {x v : Fin n → Space} {z w : Fin k → Space}
    (h : CoverAt δ K ρ x v z w) (hKK' : K ≤ K') :
    CoverAt δ K' ρ x v z w := by
  obtain ⟨hunit, hsep, huniq, hfull, hbalance, hconvex⟩ := h
  refine ⟨hunit, hsep, huniq, hfull, ?_, ?_⟩
  · intro j j'
    exact (hbalance j j').trans (mul_le_mul_of_nonneg_right hKK' (Nat.cast_nonneg _))
  · intro j W hW
    exact (hconvex j W hW).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK' (Nat.cast_nonneg _))) le_rfl)

/-- Separated all-scale covers are monotone in the error exponent. -/
theorem strong_mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε)
    (h : Strong η δ n x v) : Strong ε δ n x v := by
  have hpow : δ ^ (-η) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hηε)
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hcover, hsep⟩ := h r hδr hr1
  refine ⟨ρ, hrρ, hρ1, hρr.trans ?_, k, hk, z, w,
    coverAt_mono hcover hpow, hsep⟩
  exact mul_le_mul_of_nonneg_right hpow (hδ.le.trans hδr)

/-- Restricting shadings loses exactly the exponent prescribed by its mass retention.
All tubes and all their incidence relations remain the same. -/
theorem dense_restrict {η a ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y Z : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbudget : η + a ≤ ε)
    (h : Dense η δ n x v Y) (hZ : ∀ i, Z i ⊆ Y i)
    (hmeas : ∀ i, MeasurableSet (Z i))
    (hmass : ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    Dense ε δ n x v Z := by
  obtain ⟨hn, hv, hball, hsep, hYmeas, hY, hYmass⟩ := h
  refine ⟨hn, hv, hball, hsep, hmeas, (fun i => (hZ i).trans (hY i)), ?_⟩
  calc
    ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal (δ ^ (η + a) * (n : ℝ) * δ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget) (Nat.cast_nonneg _))
            (sq_nonneg _)
    _ = ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
          congr 1
          ring
    _ ≤ ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) := mul_le_mul' le_rfl hYmass
    _ ≤ ∑ i, volume (Z i) := hmass

/-- The family hypotheses that do not involve the choice of slope or plane field. -/
def ExtremalFamily (σ η δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  Dense η δ n x v Y ∧ Strong η δ n x v ∧
  (∀ i, IsCompact (Y i)) ∧ volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η))

/-- Transfer the full frozen family after a compact shading restriction and a
normalized smooth approximation. The hypotheses separate the geometric selection
from the algebraic losses in density and covering constants. -/
theorem regularize_family {σ η a ε δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y Z : Fin n → Set Space}
    {f g : ℝ → ℝ} {P : Space → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hηε : η ≤ ε) (hmassbudget : η + a ≤ ε)
    (hcoverbudget : 6 * δ ^ (-η) ≤ δ ^ (-ε))
    (hfamily : ExtremalFamily σ η δ n x v Y)
    (hgrains : Grains σ δ (δ ^ (-η)) v Y f P)
    (hZ : ∀ i, Z i ⊆ Y i) (hcompact : ∀ i, IsCompact (Z i))
    (hmass : ENNReal.ofReal (δ ^ a) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i))
    (hg : NormalizedC2Slope g)
    (happrox : ∀ p ∈ ⋃ i, Z i, |g (p 2) - f (p 2)| ≤ δ) :
    ExtremalFamily σ ε δ n x v Z ∧ NormalizedC2Slope g ∧
      Grains σ δ (δ ^ (-ε)) v Z g P := by
  obtain ⟨hD, hS, hYcompact, hvol⟩ := hfamily
  have hsubset : (⋃ i, Z i) ⊆ ⋃ i, Y i := iUnion_mono hZ
  have hball : (⋃ i, Y i) ⊆ ball 0 1 := by
    apply iUnion_subset
    intro i
    exact (hD.2.2.2.2.2.1 i).trans (hD.2.2.1 i)
  refine ⟨⟨dense_restrict hδ hδ1 hmassbudget hD hZ
      (fun i => (hcompact i).measurableSet) hmass,
    strong_mono_error hδ hδ1 hηε hS, hcompact, ?_⟩, hg,
    hgrains.replace_slope_rpow hδ hσ0 hσ1 hcoverbudget hZ hball happrox⟩
  exact (measure_mono hsubset).trans (hvol.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (sub_le_sub_left hηε σ))))

/-- The Lipschitz examples in the frozen premise, using the existing named conditions. -/
def LipschitzExamples (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      ExtremalFamily σ η δ n x v Y ∧ ∃ (f : ℝ → ℝ) (P : Space → Space),
        LipschitzWith 1 f ∧ Grains σ δ (δ ^ (-η)) v Y f P

/-- The smooth examples in the frozen conclusion. -/
def SmoothExamples (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      ExtremalFamily σ η δ n x v Y ∧ ∃ (f : ℝ → ℝ) (P : Space → Space),
        NormalizedC2Slope f ∧ Grains σ δ (δ ^ (-η)) v Y f P

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
