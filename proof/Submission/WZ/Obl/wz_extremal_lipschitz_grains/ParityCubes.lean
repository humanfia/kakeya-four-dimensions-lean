-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.ParityCubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CellPigeonhole

/-!
# Parity classes of grid cubes

Keeping one of the eight parity classes of grid cubes of side `s` retains an eighth of any measure,
and two kept points closer than `s` lie in the same cube (sticky Corollary 4.6).
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The points whose grid cube of side `s` has index of parity class `c`. -/
def parityClass (s : ℝ) (c : Fin 3 → ZMod 2) : Set Space :=
  {p | ∀ j, ((cubeIndex s p j : ℤ) : ZMod 2) = c j}

theorem measurableSet_parityClass {s : ℝ} (hs : 0 < s) (c : Fin 3 → ZMod 2) :
    MeasurableSet (parityClass s c) := by
  have : parityClass s c = ⋃ k ∈ {k : Fin 3 → ℤ | ∀ j, ((k j : ℤ) : ZMod 2) = c j},
      gridCube s k := by
    ext p
    simp only [parityClass, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · intro h; exact ⟨cubeIndex s p, h, mem_gridCube_cubeIndex hs p⟩
    · rintro ⟨k, hk, hp⟩; rw [cubeIndex_eq_of_mem hs hp]; exact hk
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun k _ => measurableSet_gridCube s k

/-- Two points of one parity class closer than `s` lie in the same grid cube. -/
theorem cubeIndex_eq_of_parity {s : ℝ} (hs : 0 < s) {c : Fin 3 → ZMod 2} {p q : Space}
    (hp : p ∈ parityClass s c) (hq : q ∈ parityClass s c) (hpq : dist p q < s) :
    cubeIndex s p = cubeIndex s q := by
  funext j
  have hpj := mem_gridCube_cubeIndex hs p j
  have hqj := mem_gridCube_cubeIndex hs q j
  have hcoord : |p j - q j| < s := by
    calc |p j - q j| = dist (p j) (q j) := (Real.dist_eq _ _).symm
      _ ≤ dist p q := by
          rw [EuclideanSpace.dist_eq]
          calc dist (p j) (q j) = Real.sqrt (dist (p j) (q j) ^ 2) := by
                rw [Real.sqrt_sq dist_nonneg]
            _ ≤ Real.sqrt (∑ i, dist (p i) (q i) ^ 2) :=
                Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => dist (p i) (q i) ^ 2)
                  (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
      _ < s := hpq
  have hpar : ((cubeIndex s p j : ℤ) : ZMod 2) = ((cubeIndex s q j : ℤ) : ZMod 2) :=
    (hp j).trans (hq j).symm
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hpar
  obtain ⟨m, hm⟩ := hpar
  have hlt : |cubeIndex s q j - cubeIndex s p j| < 2 := by
    obtain ⟨h1, h2⟩ := hpj
    obtain ⟨h3, h4⟩ := hqj
    rw [abs_lt] at hcoord ⊢
    have hA : (cubeIndex s q j - cubeIndex s p j : ℝ) < 2 := by
      have : s * (cubeIndex s q j - cubeIndex s p j : ℝ) < 2 * s := by nlinarith
      nlinarith
    have hB : -2 < (cubeIndex s q j - cubeIndex s p j : ℝ) := by
      have : -(2 * s) < s * (cubeIndex s q j - cubeIndex s p j : ℝ) := by nlinarith
      nlinarith
    have hA' : cubeIndex s q j - cubeIndex s p j < 2 := by exact_mod_cast hA
    have hB' : -2 < cubeIndex s q j - cubeIndex s p j := by exact_mod_cast hB
    exact ⟨hB', hA'⟩
  rw [hm] at hlt
  have : m = 0 := by
    rw [abs_lt] at hlt
    omega
  rw [this, mul_zero, sub_eq_zero] at hm
  exact hm.symm


/-- Some parity class carries an eighth of any measure. -/
theorem exists_heavy_parityClass (ν : Measure Space) (A : Set Space) (s : ℝ) :
    ∃ c : Fin 3 → ZMod 2, ν A ≤ 8 * ν (A ∩ parityClass s c) := by
  classical
  have hcover : A ⊆ ⋃ c ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)), A ∩ parityClass s c := by
    intro p hp
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion]
    exact ⟨fun j => ((cubeIndex s p j : ℤ) : ZMod 2), hp, fun j => rfl⟩
  have hle : ν A ≤ ∑ c ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)), ν (A ∩ parityClass s c) :=
    (measure_mono (μ := ν) hcover).trans (measure_biUnion_finset_le Finset.univ _)
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3 → ZMod 2))
    (fun c => ν (A ∩ parityClass s c)) Finset.univ_nonempty
  refine ⟨c, hle.trans ?_⟩
  calc ∑ c ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)), ν (A ∩ parityClass s c)
      ≤ ∑ _d ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)), ν (A ∩ parityClass s c) :=
        Finset.sum_le_sum fun d hd => hmax d hd
    _ = 8 * ν (A ∩ parityClass s c) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
