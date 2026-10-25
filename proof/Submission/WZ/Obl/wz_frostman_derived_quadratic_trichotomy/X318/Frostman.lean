-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.Frostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.OneScale

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file Frostman.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open scoped ENNReal

lemma tube_convex (δ : ℝ) (x v : Space) : Convex ℝ (Tube δ x v) :=
  (convex_segment (𝕜 := ℝ) x (x + v)).thickening δ

lemma tube_volume_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
  have hh := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Icc 0 1) Subset.rfl (r := δ) (A := 1) hδ zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have he : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [he] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ]))

/-- Testing the Frostman bound on one input tube gives the cardinality lower bound. -/
lemma frostman_card_lower {δ ζ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i))) :
    δ ^ ζ ≤ 384 * (n : ℝ) * δ ^ 2 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hcount : 1 ≤ ncard {j | Tube δ (x j) (v j) ⊆ Tube δ (x i) (v i)} :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, Subset.rfl⟩
  have he : (1 : ENNReal) ≤ ENNReal.ofReal (δ ^ (-ζ) * n * (384 * δ ^ 2)) := by
    calc
      1 ≤ ENNReal.ofReal (ncard {j | Tube δ (x j) (v j) ⊆ Tube δ (x i) (v i)} : ℝ) := by
        simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ ncard _ by exact_mod_cast hcount)
      _ ≤ ENNReal.ofReal (δ ^ (-ζ) * n) * volume (Tube δ (x i) (v i)) :=
        hF _ (tube_convex _ _ _)
      _ ≤ ENNReal.ofReal (δ ^ (-ζ) * n) * ENNReal.ofReal (384 * δ ^ 2) :=
        mul_le_mul' le_rfl (tube_volume_upper hδ hδ1 _ _ (hv i))
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hreal : 1 ≤ δ ^ (-ζ) * n * (384 * δ ^ 2) := by
    rw [← ENNReal.ofReal_one] at he
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have hprod : δ ^ ζ * δ ^ (-ζ) = 1 := by rw [← Real.rpow_add hδ]; simp
  calc
    δ ^ ζ = δ ^ ζ * 1 := by ring
    _ ≤ δ ^ ζ * (δ ^ (-ζ) * n * (384 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hδ.le _)
    _ = 384 * (n : ℝ) * δ ^ 2 := by
      calc
        _ = (δ ^ ζ * δ ^ (-ζ)) * (384 * (n : ℝ) * δ ^ 2) := by ring
        _ = _ := by rw [hprod, one_mul]

lemma density_lower_of_frostman {δ ζ ζ₂ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (habsorb : 384 * δ ^ (ζ₂ - ζ) ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i))) :
    δ ^ ζ₂ * (1 / δ) ^ 2 ≤ (n : ℝ) := by
  have hh := frostman_card_lower hδ hδ1 x v hn hv hF
  have hp : δ ^ ζ₂ = δ ^ (ζ₂ - ζ) * δ ^ ζ := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hm : δ ^ ζ₂ ≤ (n : ℝ) * δ ^ 2 := by
    calc
      δ ^ ζ₂ = δ ^ (ζ₂ - ζ) * δ ^ ζ := hp
      _ ≤ δ ^ (ζ₂ - ζ) * (384 * (n : ℝ) * δ ^ 2) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hδ.le _)
      _ = (384 * δ ^ (ζ₂ - ζ)) * ((n : ℝ) * δ ^ 2) := by ring
      _ ≤ (n : ℝ) * δ ^ 2 := mul_le_of_le_one_left (by positivity) habsorb
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp
  calc
    (δ ^ ζ₂ * (1 / δ) ^ 2) * δ ^ 2 = δ ^ ζ₂ := by field_simp
    _ ≤ (n : ℝ) * δ ^ 2 := hm

/-- The easy alternative of the trichotomy, with its cardinality supplied by Frostman. -/
theorem separated_scales_of_frostman_and_katz_tao {δ ζ ζ₁ ζ₂ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hζ₁ : ζ₁ ≤ 1) (hζ₂ : 0 ≤ ζ₂)
    (habsorb : 384 * δ ^ (ζ₂ - ζ) ≤ 1)
    {n : ℕ} (x v : Fin n → Space) (hn : 0 < n) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hsep : Distinct (fun i => Tube δ (x i) (v i)))
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)))
    (hKT : KatzTao δ (δ ^ (-ζ₂)) (fun i => Tube δ (x i) (v i))) :
    SeparatedScales ζ₁ ζ₂ δ (fun i => Tube δ (x i) (v i)) :=
  separated_scales_of_katz_tao hδ hδ1 hζ₁ hζ₂ x v hn hv hball hsep hKT
    (density_lower_of_frostman hδ hδ1.le habsorb x v hn hv hF)

lemma KatzTao.mono {n : ℕ} {δ K L : ℝ} {A : Fin n → Set Space}
    (h : KatzTao δ K A) (hKL : K ≤ L) : KatzTao δ L A := by
  intro W hW
  exact (h W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hKL) le_rfl)

/-- Global Frostman control is KT control with coefficient K*n*delta^2. -/
lemma Frostman.katzTao {n : ℕ} {δ K : ℝ} {A : Fin n → Set Space}
    (h : Frostman K A) (hK : 0 ≤ K) : KatzTao δ (K * n * δ ^ 2) A := by
  intro W hW
  calc
    ENNReal.ofReal ((ncard {i | A i ⊆ W} : ℝ) * δ ^ 2) =
        ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (ncard {i | A i ⊆ W} : ℝ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_comm]
    _ ≤ ENNReal.ofReal (δ ^ 2) * (ENNReal.ofReal (K * n) * volume W) :=
      mul_le_mul' le_rfl (h W hW)
    _ = ENNReal.ofReal (K * n * δ ^ 2) * volume W := by
      rw [ENNReal.ofReal_mul (mul_nonneg hK (Nat.cast_nonneg n))]
      ring

lemma card_lower_of_not_katzTao {δ ζ ζ₂ : ℝ} (hδ : 0 ≤ δ)
    {n : ℕ} {A : Fin n → Set Space} (hF : Frostman (δ ^ (-ζ)) A)
    (hKT : ¬ KatzTao δ (δ ^ (-ζ₂)) A) :
    δ ^ (-ζ₂) < δ ^ (-ζ) * n * δ ^ 2 := by
  apply lt_of_not_ge
  intro hle
  exact hKT ((hF.katzTao (Real.rpow_nonneg hδ _)).mono hle)

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
