-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CarrierMap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CarrierMap.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0708 commit 170d089, CarrierMap.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CarrierLinear

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (diagonalMap diagonalMap_norm_le coordinateAffine coordinateAffine_volume)

/-- The centre uses the enclosing slab's normal coordinate and the old
block's tangential coordinates. -/
def carrierChart (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) : V ≃ᵃⁱ[ℝ] V :=
  ((AffineIsometryEquiv.constVAdd ℝ V
    (-(z₀ + g (z'-z₀) 0 • boxAxis g 0))).trans g.toAffineIsometryEquiv).symm

def carrierScales (S c ρ : ℝ) : Fin 3 → ℝ := ![ρ/(4*S),(4*c)⁻¹,(4*c)⁻¹]

theorem carrierScales_pos {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (i : Fin 3) : 0 < carrierScales S c ρ i := by
  fin_cases i <;> dsimp [carrierScales] <;> positivity

/-- Normalize the enclosing short coordinate to `rho A/(4S)`, retaining
uniform tangential scale. The useful choice is `S = min A (rho*c)`. -/
def carrierAffine {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) : V ≃ᵃ[ℝ] V :=
  coordinateAffine (carrierChart z₀ z' g) (carrierScales S c ρ)
    (fun i => (carrierScales_pos hS hc hρ i).ne')

theorem carrierAffine_apply {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) (p : V) :
    carrierAffine hS hc hρ z₀ z' g p =
      diagonalMap (carrierScales S c ρ) (g (p-(z₀+g (z'-z₀) 0 • boxAxis g 0))) := by
  change diagonalMap _ (g (-(z₀+g (z'-z₀) 0 • boxAxis g 0)+p)) = _
  congr 2
  abel

theorem carrierAffine_linear {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) (v : V) (i : Fin 3) :
    (carrierAffine hS hc hρ z₀ z' g).linear v i = carrierScales S c ρ i * g v i := rfl

theorem carrierAffine_coordinates {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) (p : V) :
    carrierAffine hS hc hρ z₀ z' g p 0 = (ρ/(4*S))*g (p-z') 0 ∧
    ∀ i : Fin 3, i ≠ 0 →
      carrierAffine hS hc hρ z₀ z' g p i = (4*c)⁻¹*g (p-z₀) i := by
  have he : g (p-(z₀+g (z'-z₀) 0 • boxAxis g 0)) =
      g (p-z₀) - g (z'-z₀) 0 • EuclideanSpace.basisFun (Fin 3) ℝ 0 := by
    rw [show p-(z₀+g (z'-z₀) 0 • boxAxis g 0) =
      (p-z₀)-g (z'-z₀) 0 • boxAxis g 0 by module, map_sub, map_smul]
    simp only [boxAxis, g.apply_symm_apply]
  rw [carrierAffine_apply, he]
  constructor
  · simp [carrierScales, EuclideanSpace.basisFun_apply]
    ring
  · intro i hi
    fin_cases i <;> simp_all [carrierScales, EuclideanSpace.basisFun_apply] <;> ring

theorem carrierAffine_volume {S c ρ : ℝ} (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) (U : Set V) :
    μ (carrierAffine hS hc hρ z₀ z' g '' U) = O (ρ/(64*S*c^2))*μ U := by
  have hh := coordinateAffine_volume (carrierChart z₀ z' g) (carrierScales S c ρ)
    (carrierScales_pos hS hc hρ) U
  change μ (carrierAffine hS hc hρ z₀ z' g '' U) = O (∏ i, carrierScales S c ρ i)*μ U at hh
  rw [hh]
  congr 2
  simp only [Fin.prod_univ_three]
  dsimp [carrierScales]
  field_simp
  ring

/-- The original block supplies tangential localization; the enclosed slab
supplies the short localization. Thus no enlarged physical diameter enters
the normalized unit-ball hypothesis. -/
theorem carrierAffine_ball_and_slab {S c ρ A B C : ℝ}
    (hS : 0 < S) (hc : 0 < c) (hρ : 0 < ρ) (hα : ρ*A/(4*S) ≤ 1/8)
    (z₀ z' : V) (g : V ≃ₗᵢ[ℝ] V) :
    carrierAffine hS hc hρ z₀ z' g '' (P A B C z' g ∩ ball z₀ (2*c)) ⊆
      ball (0 : V) 1 ∩ {p | |p 0| ≤ (ρ*A/(4*S))/2} := by
  rintro _ ⟨p, hp, rfl⟩
  let f := carrierAffine hS hc hρ z₀ z' g
  obtain ⟨h0, ht⟩ := carrierAffine_coordinates hS hc hρ z₀ z' g p
  have hshort : |f p 0| ≤ (ρ*A/(4*S))/2 := by
    change |carrierAffine hS hc hρ z₀ z' g p 0| ≤ _
    rw [h0, abs_mul, abs_of_pos (by positivity : 0 < ρ/(4*S))]
    calc
      _ ≤ (ρ/(4*S))*(A/2) := mul_le_mul_of_nonneg_left hp.1.1 (by positivity)
      _ = _ := by ring
  refine ⟨?_, hshort⟩
  let v := g (p-z₀)
  let w := diagonalMap ![0,1,1] v
  have hw : ‖w‖ ≤ ‖v‖ := by
    have hh := diagonalMap_norm_le (by norm_num : (0 : ℝ) ≤ 1)
      (s := ![0,1,1]) (by intro i; fin_cases i <;> norm_num) v
    simpa only [one_mul] using hh
  have he : f p = (f p 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 + (4*c)⁻¹ • w := by
    ext i
    fin_cases i
    · simp [w, EuclideanSpace.basisFun_apply]
    · simpa [w, v, EuclideanSpace.basisFun_apply] using ht 1 (by decide)
    · simpa [w, v, EuclideanSpace.basisFun_apply] using ht 2 (by decide)
  have hpball : ‖v‖ < 2*c := by simpa only [v, g.norm_map, mem_ball, dist_eq_norm] using hp.2
  change ‖f p - 0‖ < 1
  rw [sub_zero, he]
  calc
    _ ≤ ‖(f p 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0‖ + ‖(4*c)⁻¹ • w‖ := norm_add_le _ _
    _ = |f p 0| + (4*c)⁻¹*‖w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (4*c)⁻¹)]
      simp
    _ ≤ (ρ*A/(4*S))/2 + (4*c)⁻¹*‖v‖ := add_le_add hshort
      (mul_le_mul_of_nonneg_left hw (by positivity))
    _ < (ρ*A/(4*S))/2 + (4*c)⁻¹*(2*c) :=
      by gcongr
    _ < 1 := by
      have heq : (4*c)⁻¹*(2*c) = (1/2 : ℝ) := by field_simp <;> norm_num
      rw [heq]
      linarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
