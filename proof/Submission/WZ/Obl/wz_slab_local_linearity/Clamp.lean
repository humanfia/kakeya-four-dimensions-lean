-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.Clamp.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights
import Submission.WZ.Obl.wz_slab_local_linearity.CubeVolume

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set MeasureTheory

/-- Extend a slope from a closed interval by holding its endpoint values fixed. -/
noncomputable def clampSlope (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (x : ℝ) : ℝ :=
  f (projIcc a b hab x)

lemma clampSlope_eq {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b) :
    clampSlope f a b hab x = f x := by
  simp only [clampSlope, projIcc_of_mem hab hx]

lemma clampSlope_lipschitz {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ |x - y|) :
    LipschitzWith 1 (clampSlope f a b hab) := by
  have hsub : LipschitzWith 1 (fun x : Icc a b => f x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using hf x x.property y y.property
  change LipschitzWith 1 (fun x => f (projIcc a b hab x))
  simpa only [one_mul, Function.comp_def] using hsub.comp (LipschitzWith.projIcc hab)

lemma clampSlope_bound {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, |f x| ≤ C) (x : ℝ) : |clampSlope f a b hab x| ≤ C :=
  hf (projIcc a b hab x) (projIcc a b hab x).property

/-- A volume lower bound for full lattice cubes is the corresponding cell-count
lower bound, with exactly the three powers of the side length removed. -/
lemma gridCubes_card_lower {ρ t : ℝ} (hρ : 0 < ρ) (K : Finset (Fin 3 → ℤ))
    (hvol : ENNReal.ofReal (ρ ^ t) ≤ volume (gridCubes ρ K)) :
    ρ ^ (t - 3) ≤ (K.card : ℝ) := by
  rw [gridCubes_volume hρ K] at hvol
  have hh : ρ ^ t ≤ (K.card : ℝ) * ρ ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol
  have he : ρ ^ (t - 3) * ρ ^ (3 : ℕ) = ρ ^ t := by
    rw [← Real.rpow_natCast ρ 3, ← Real.rpow_add hρ]
    congr 1
    norm_num
  apply le_of_mul_le_mul_right (show ρ ^ (t - 3) * ρ ^ (3 : ℕ) ≤ (K.card : ℝ) * ρ ^ (3 : ℕ) by
    rwa [he]) (by positivity : 0 < ρ ^ (3 : ℕ))

end WangZahlLot.Obl.wz_slab_local_linearity
