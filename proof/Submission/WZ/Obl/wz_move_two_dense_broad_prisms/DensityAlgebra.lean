-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.DensityAlgebra.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PowerBudgets
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.EnlargedPrism

/-! The large multiplicity pays for all costs of the enlarged prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- The enlarged prism has enough incidence mass for density `d^(-omega/2)`.
The numerical margin also absorbs the exceptional three-dimensional grid. -/
theorem enlarged_density_budget {d a c ρ ω β η b : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hω : 0 < ω) (hβ : 0 < β) (hη : 0 < η)
    (hηω : η ≤ ω/1000) (hηβ : η ≤ β*ω/1000) (hb : b ≤ ω/1000)
    (ha : a ≤ 2*d^(1-b))
    (hsmall : (10:ℝ)^40*d^(η/2) ≤ 1) :
    let L := d^(-ω/100)*c
    d^(-ω/2) * (10000*a*(10000*enlargedSlope (ρ*c) c*L)*L) *
      (320000000000000000000*d*(L/c)^3) ≤
      (d^η*d^(-24*ω/25)*c*(ρ*d^(4*η/β))) * (d^η*L*d^2/256) := by
  dsimp only
  let L := d^(-ω/100)*c
  let u := 2-b-11*ω/20
  let v := 2+2*η+4*η/β-97*ω/100
  have hR : enlargedSlope (ρ*c) c ≤ ρ := by
    exact (min_le_left _ _).trans_eq (mul_div_cancel_right₀ ρ hc.ne')
  have hR0 : 0 ≤ enlargedSlope (ρ*c) c := le_min (by positivity) (by norm_num)
  have hLp : 0 < L := by dsimp [L]; positivity
  have hLc : L/c = d^(-ω/100) := by dsimp [L]; field_simp
  have hD3 : (d^(-ω/100))^3 = d^(-3*ω/100) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    congr 1
    ring
  have hpowleft : d^(-ω/2)*d^(1-b)*d^(-ω/100)*d^(-ω/100)*d^(1:ℝ)*d^(-3*ω/100) = d^u := by
    rw [← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd,
      ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    dsimp [u]
    ring
  have hpowright : d^η*d^(-24*ω/25)*d^(4*η/β)*d^η*d^(-ω/100)*d^(2:ℝ) = d^v := by
    rw [← Real.rpow_add hd, ← Real.rpow_add hd, ← Real.rpow_add hd,
      ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    dsimp [v]
    ring
  have hgap : η/2 ≤ u-v := by
    have hfrac : 4*η/β ≤ ω/250 := (div_le_iff₀ hβ).mpr (by nlinarith)
    dsimp [u, v]
    linarith
  have hbudget := small_power_budget hd hd1 hsmall hgap
    (by positivity : 0 ≤ (10:ℝ)^35) (by norm_num : (10:ℝ)^35 ≤ (10:ℝ)^40)
  have hpowers : (10:ℝ)^35*d^u ≤ d^v := by
    calc
      _ = d^v*((10:ℝ)^35*d^(u-v)) := by
        rw [← mul_assoc, mul_comm (d^v) ((10:ℝ)^35), mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ d^v*1 := mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := mul_one _
  have hleft : d^(-ω/2)*(10000*a*(10000*enlargedSlope (ρ*c) c*L)*L)*
      (320000000000000000000*d*(L/c)^3) ≤
      (2*10000^2*320000000000000000000)*ρ*c^2*d^u := by
    calc
      _ ≤ d^(-ω/2)*(10000*(2*d^(1-b))*(10000*ρ*L)*L)*
          (320000000000000000000*d*(L/c)^3) := by gcongr
      _ = (2*10000^2*320000000000000000000)*ρ*c^2*
          (d^(-ω/2)*d^(1-b)*d^(-ω/100)*d^(-ω/100)*d^(1:ℝ)*d^(-3*ω/100)) := by
        rw [hLc, hD3]
        dsimp [L]
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [hpowleft]
  have hright : (d^η*d^(-24*ω/25)*c*(ρ*d^(4*η/β))) * (d^η*L*d^2/256) =
      (ρ*c^2/256)*d^v := by
    calc
      _ = (ρ*c^2/256)*(d^η*d^(-24*ω/25)*d^(4*η/β)*d^η*d^(-ω/100)*d^(2:ℝ)) := by
        dsimp [L]
        rw [Real.rpow_two]
        ring
      _ = _ := by rw [hpowright]
  change d^(-ω/2)*(10000*a*(10000*enlargedSlope (ρ*c) c*L)*L)*
      (320000000000000000000*d*(L/c)^3) ≤ _
  rw [hright]
  calc
    _ ≤ (2*10000^2*320000000000000000000)*ρ*c^2*d^u := hleft
    _ ≤ ((10:ℝ)^35/256)*ρ*c^2*d^u := by gcongr <;> norm_num
    _ = (ρ*c^2/256)*((10:ℝ)^35*d^u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpowers (by positivity)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
