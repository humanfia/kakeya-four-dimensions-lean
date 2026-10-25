-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridMassParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.InteriorParameters

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

/-- Choose a verticality/density exponent after the hierarchy has been fixed.
Both the absolute height-mass error and the comparison with the original tube
mass then fit the desired retention power. -/
theorem exists_grid_mass_parameters {κ ζ : ℝ} {N : ℕ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hζ : 0 < ζ) (hN : 0 < N) :
    ∃ β d₀ : ℝ, 0 < β ∧ β ≤ κ / 4 ∧ 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ 1 →
        (384 * δ ^ κ ≤ δ ^ β / 2) ∧
        ∀ n : ℕ,
          55 * N * (24 * n * δ ^ 2 / (δ ^ β) ^ 2) *
              ((δ ^ (1 - κ)) ^ ζ + (δ ^ (1 - κ)) ^ (1 / (2 * (N : ℝ)))) ≤
            δ ^ β * n * δ ^ 2 / 2 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let e := min ((1 - κ) * ζ) ((1 - κ) / (2 * N))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  let β := min (κ / 4) (e / 8)
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  have hβκ : β ≤ κ / 4 := min_le_left _ _
  have hβe : β ≤ e / 8 := min_le_right _ _
  have hgap : 0 < e - 3 * β := by linarith
  have hgapκ : 0 < κ - β := by linarith
  obtain ⟨d₁, hd₁, hcut₁⟩ := cut_le_one hgap (5280 * N)
  obtain ⟨d₂, hd₂, hcut₂⟩ := cut_le_one hgapκ 768
  refine ⟨β, min d₁ d₂, hβ, hβκ, lt_min hd₁ hd₂, ?_⟩
  intro δ hδ hδd hδ1
  have hcutmass := hcut₁ δ hδ (hδd.trans (min_le_left _ _))
  have hcutretain := hcut₂ δ hδ (hδd.trans (min_le_right _ _))
  have hβpow : 0 < δ ^ β := Real.rpow_pos_of_pos hδ _
  constructor
  · have heq : 384 * δ ^ κ = (768 * δ ^ (κ - β)) * (δ ^ β / 2) := by
      have hh : δ ^ (κ - β) * δ ^ β = δ ^ κ := by
        rw [← Real.rpow_add hδ, sub_add_cancel]
      calc
        384 * δ ^ κ = 384 * (δ ^ (κ - β) * δ ^ β) := by rw [hh]
        _ = _ := by ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hcutretain (by positivity)).trans_eq (one_mul _)
  · intro n
    have hs₁ : (δ ^ (1 - κ)) ^ ζ ≤ δ ^ e := by
      rw [← Real.rpow_mul hδ.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)
    have hs₂ : (δ ^ (1 - κ)) ^ (1 / (2 * (N : ℝ))) ≤ δ ^ e := by
      rw [← Real.rpow_mul hδ.le]
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      simpa only [e, div_eq_mul_inv, one_mul] using
        (min_le_right ((1 - κ) * ζ) ((1 - κ) / (2 * N)))
    have hratio : δ ^ e / (δ ^ β) ^ 2 = δ ^ (e - 3 * β) * δ ^ β := by
      have hsquare : (δ ^ β) ^ 2 = δ ^ (β * 2) := by
        rw [Real.rpow_mul hδ.le, Real.rpow_two]
      rw [hsquare, ← Real.rpow_sub hδ, ← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ ≤ 55 * N * (24 * n * δ ^ 2 / (δ ^ β) ^ 2) * (2 * δ ^ e) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity
      _ = (5280 * N * δ ^ (e - 3 * β)) * (δ ^ β * n * δ ^ 2 / 2) := by
        calc
          _ = (2640 * N * n * δ ^ 2) * (δ ^ e / (δ ^ β) ^ 2) := by ring
          _ = _ := by rw [hratio]; ring
      _ ≤ δ ^ β * n * δ ^ 2 / 2 := by
        exact (mul_le_mul_of_nonneg_right hcutmass (by positivity)).trans_eq (one_mul _)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
