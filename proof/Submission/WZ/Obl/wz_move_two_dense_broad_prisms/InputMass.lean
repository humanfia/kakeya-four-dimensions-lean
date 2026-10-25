-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.InputMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal

lemma admissible_mass_pos {d h m l : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hA : A d h m l n x v Y) : 0 < ∑ i, μ (Y i) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hA.1
  exact (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos (Real.rpow_pos_of_pos hd h) hn)
    (sq_pos_of_pos hd))).trans_le hA.2.2.2.1

lemma admissible_finite_mass {d h m l : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hA : A d h m l n x v Y) (i : Fin n) : μ (Y i) ≠ ∞ :=
  measure_ne_top_of_subset (hA.2.1 i).2.2.2
    (wz_flat_cluster_slab_filling.tube_volume_ne_top d (x i) (v i))

lemma cover_has_point {d h m l ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hd : 0 < d) (hA : A d h m l n x v Y)
    (hC : C d h n x v Y S Z ρ N y w f True) :
    ∃ i ∈ S, ∃ p, p ∈ Z i := by
  classical
  have hpos : 0 < ∑ i ∈ S, μ (Z i) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd h)).ne'
      (admissible_mass_pos hd hA).ne').trans_le hC.2.1
  by_contra hnone
  push Not at hnone
  have hzero : ∀ i ∈ S, Z i = ∅ := fun i hi => Set.eq_empty_iff_forall_notMem.mpr (hnone i hi)
  have : ∑ i ∈ S, μ (Z i) = 0 := Finset.sum_eq_zero fun i hi => by
    rw [hzero i hi]; exact measure_empty
  exact hpos.ne' this

lemma cover_mass_all {d h ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V} {f : Fin n → Fin N}
    (hC : C d h n x v Y S Z ρ N y w f True) :
    O (d ^ h) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i) :=
  hC.2.1.trans (Finset.sum_le_univ_sum_of_nonneg fun _ => zero_le)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
