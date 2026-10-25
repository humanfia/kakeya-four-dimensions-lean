-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.SeedBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- Power reserves for the elementary quarter-dimensional thin-tube seed.
The complementary range of parameters gives a trivial seed. -/
theorem exists_seed_budget {ℓ ζ α : ℝ} (hℓ : 0 < ℓ) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (hα : 0 < α) (hA : ℓ + 3 * α / ζ < 1 / 4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      let C := δ ^ (-ℓ)
      let q := δ ^ (ℓ + 3 * α)
      let s := δ ^ (ℓ + 3 * α / ζ)
      let K := δ ^ (-(ℓ + 3 * α / ζ))
      δ ≤ q ∧ δ ≤ s ∧ q * s ≤ 4096 ∧
      1 / K ^ (4 : ℕ) ≤ q * s / 256 ∧
      C * q + (C * s) ^ ζ + 2560000 * C / (K ^ (4 : ℕ) * q * s) <
        (δ ^ (5 * α / 4)) ^ (2 : ℕ) := by
  let A := ℓ + 3 * α / ζ
  have hquot : 3 * α ≤ 3 * α / ζ := by
    apply (le_div_iff₀ hζ).mpr
    nlinarith
  have hApos : 0 < A := by dsimp [A]; positivity
  have hres : ℓ + 3 * α + A < 4 * A := by dsimp [A]; nlinarith
  obtain ⟨δ₁, hδ₁, hδ₁1, hsmall⟩ := exists_monomial_bound 256 hres
  obtain ⟨δ₂, hδ₂, hδ₂1, hgain⟩ :=
    exists_monomial_bound 5120004 (a := 3 * α) (b := 5 * α / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁1, ?_⟩
  intro δ hδ hδsmall
  let C := δ ^ (-ℓ)
  let q := δ ^ (ℓ + 3 * α)
  let s := δ ^ A
  let K := δ ^ (-A)
  have hδ1 : δ ≤ 1 := (hδsmall.trans (min_le_left _ _)).trans hδ₁1
  have hq : δ ≤ q := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ q := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hs : δ ≤ s := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ s := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [A]; linarith)
  have hq1 : q ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hs1 : s ≤ 1 := Real.rpow_le_one hδ.le hδ1 hApos.le
  have hqs : q * s ≤ 4096 := by
    have hh := mul_le_mul hq1 hs1 (by positivity : 0 ≤ s) (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at hh
    linarith
  have hqs_eq : q * s = δ ^ (ℓ + 3 * α + A) := by
    exact (Real.rpow_add hδ _ _).symm
  have hK4 : K ^ (4 : ℕ) = δ ^ (-4 * A) := by
    dsimp [K]
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  have hinv : 1 / K ^ (4 : ℕ) = δ ^ (4 * A) := by
    rw [hK4, show -4 * A = -(4 * A) by ring, one_div, Real.rpow_neg hδ.le, inv_inv]
  have hsmall' : 1 / K ^ (4 : ℕ) ≤ q * s / 256 := by
    rw [hinv, hqs_eq]
    have hh := hsmall δ hδ (hδsmall.trans (min_le_left _ _))
    linarith
  have hCq : C * q = δ ^ (3 * α) := by
    dsimp [C, q]
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hCs : (C * s) ^ ζ = δ ^ (3 * α) := by
    dsimp [C, s, A]
    rw [← Real.rpow_add hδ, ← Real.rpow_mul hδ.le]
    congr 1
    field_simp
    <;> ring
  have hcost : C / (K ^ (4 : ℕ) * q * s) = δ ^ (3 * A - 2 * ℓ - 3 * α) := by
    rw [hK4, mul_assoc, hqs_eq]
    dsimp [C]
    rw [← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 1
    ring
  have hcost_le : C / (K ^ (4 : ℕ) * q * s) ≤ δ ^ (3 * α) := by
    rw [hcost]
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    dsimp [A]
    nlinarith
  refine ⟨hq, hs, hqs, hsmall', ?_⟩
  change C * q + (C * s) ^ ζ + 2560000 * C / (K ^ (4 : ℕ) * q * s) < _
  have hsquare : (δ ^ (5 * α / 4)) ^ (2 : ℕ) = δ ^ (5 * α / 2) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
    <;> ring
  rw [hCq, hCs, mul_div_assoc, hsquare]
  have hg := hgain δ hδ (hδsmall.trans (min_le_right _ _))
  have hh := mul_le_mul_of_nonneg_left hcost_le (by norm_num : (0 : ℝ) ≤ 2560000)
  have hp : 0 < δ ^ (5 * α / 2) := by positivity
  nlinarith

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
