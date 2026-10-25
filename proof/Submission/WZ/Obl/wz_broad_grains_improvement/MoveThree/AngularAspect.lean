-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AngularAspect.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AngularAspect.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AngularDensityScalar

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- The summed angular estimate and the ambient density cap force a flat
packet prism. The angular multiplicity is paid only once. -/
theorem packet_aspect_of_density_bounds
    {δ σ ζ ε t β M P r θ C K X : ℝ} {U : ENNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ) (hζ : 0 < ζ)
    (hε : ε ≤ ζ / 16) (ht : t + β ≤ ζ * σ / 16)
    (hM : δ ^ (-ζ) ≤ M) (hP : 0 < P) (hPmax : P ≤ δ ^ (-ε))
    (hβ : 0 ≤ β) (hθ : δ ≤ θ) (hC : 0 < C) (hK : 0 < K) (hX : 0 < X)
    (hcut : δ ^ (3 * ζ * σ / 16) ≤ C / (4 * K))
    (hlo : O (C * δ ^ t * M ^ (σ / 2) * P ^ (-σ) * r ^ (σ / 2) * X) ≤
      O (2 * θ ^ (-β)) * U)
    (hup : U ≤ O (K * δ ^ (-(ζ * σ / 16)) * X)) :
    r < δ ^ (ζ / 4) := by
  have hθpos : 0 < θ := hδ.trans_le hθ
  have hθpow : θ ^ (-β) ≤ δ ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hδ hθ (by linarith)
  have hμ : O (2 * θ ^ (-β)) * U ≤
      O ((2 * δ ^ (-β)) * (K * δ ^ (-(ζ * σ / 16)) * X)) := by
    calc
      _ ≤ O (2 * δ ^ (-β)) * O (K * δ ^ (-(ζ * σ / 16)) * X) :=
        mul_le_mul (ENNReal.ofReal_le_ofReal (by linarith)) hup (by positivity) (by positivity)
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hreal : C * δ ^ t * M ^ (σ / 2) * P ^ (-σ) * r ^ (σ / 2) ≤
      2 * δ ^ (-β) * (K * δ ^ (-(ζ * σ / 16))) := by
    have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hlo.trans hμ)
    apply (mul_le_mul_iff_left₀ hX).mp
    convert hh using 1 <;> ring
  have hcancel : δ ^ (-β) * δ ^ β = 1 := by rw [← Real.rpow_add hδ]; simp
  have htimes : C * (δ ^ (t + β) * M ^ (σ / 2) * P ^ (-σ) * r ^ (σ / 2)) ≤
      2 * K * δ ^ (-(ζ * σ / 16)) := by
    have hh := mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg hδ.le β)
    rw [Real.rpow_add hδ]
    calc
      _ = (C * δ ^ t * M ^ (σ / 2) * P ^ (-σ) * r ^ (σ / 2)) * δ ^ β := by ring
      _ ≤ (2 * δ ^ (-β) * (K * δ ^ (-(ζ * σ / 16)))) * δ ^ β := hh
      _ = (2 * K * δ ^ (-(ζ * σ / 16))) * (δ ^ (-β) * δ ^ β) := by ring
      _ = _ := by rw [hcancel, mul_one]
  by_contra hn
  have hfactor := sharp_nonflat_density_factor hδ hδ1 hζ hσ hε ht hM hP hPmax
    (le_of_not_gt hn)
  have hineq : C * δ ^ (-(ζ * σ / 4)) ≤ 2 * K * δ ^ (-(ζ * σ / 16)) :=
    (mul_le_mul_of_nonneg_left hfactor hC.le).trans htimes
  have hid₁ : δ ^ (-(ζ * σ / 4)) * δ ^ (ζ * σ / 4) = 1 := by
    rw [← Real.rpow_add hδ]; simp
  have hid₂ : δ ^ (-(ζ * σ / 16)) * δ ^ (ζ * σ / 4) = δ ^ (3 * ζ * σ / 16) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hineq (Real.rpow_nonneg hδ.le (ζ * σ / 4))
  rw [mul_assoc, hid₁, mul_one, mul_assoc, hid₂] at hh
  have hcut' := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp hcut
  nlinarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
