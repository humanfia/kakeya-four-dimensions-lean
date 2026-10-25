-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.Length.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/Length.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.GoodGrains
import Submission.WZ.Obl.wz_move_two_long_grains_gain.LevelBound

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/Length.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

/-!
# Broadness forces the grains to have short length

Broadness at the fine scale gives a lower bound on every occupied fibre count.
Combining it with the accepted Katz--Tao bound on the common multiplicity level
gives a quantitative upper bound on the grain length.  In particular the exact
unit-length endpoint obstruction cannot occur in an admissible stage state.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set

theorem broad_count_lower {ω ζ δ h ρ : ℝ} {n N : ℕ} {v : Fin n → V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hv : ∀ i, ‖v i‖ = 1)
    (hb : Broad ω ζ δ h ρ n N v S Z f) (k : Fin N) (p : V)
    (hp : ∃ i ∈ S, f i = k ∧ p ∈ Z i) :
    1 ≤ δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) *
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
  obtain ⟨i, hiS, hfi, hpi⟩ := hp
  have hi : i ∈ {j | j ∈ S ∧ f j = k ∧ p ∈ Z j ∧
      min ‖v j - v i‖ ‖v j + v i‖ ≤ δ} :=
    ⟨hiS, hfi, hpi, by simpa using hδ.le⟩
  have hcard := Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hi⟩)
  have hcard' : (1 : ℝ) ≤ q n {j | j ∈ S ∧ f j = k ∧ p ∈ Z j ∧
      min ‖v j - v i‖ ‖v j + v i‖ ≤ δ} := by
    exact_mod_cast hcard
  exact hcard'.trans (hb k p (v i) δ (hv i) le_rfl hδρ)

theorem broad_grains_length_bound {ω ζ δ h ρ a c g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hH : H δ h n x v S Z ρ N y w f a c 0 g) (h4 : 4 * δ ≤ c) :
    c ^ 2 ≤ 2985984 * δ ^ (-(3 * h)) * (δ / ρ) ^ (ω * ζ / 100) := by
  obtain ⟨L, z, e, Hs, γ, m, hHB⟩ := H_iff.mp hH
  have hpow : 0 < δ ^ h := Real.rpow_pos_of_pos hδ _
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hYpos : 0 < ∑ i, μ (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hA.2.2.2.1
  have hZpos : 0 < ∑ i ∈ S, μ (Z i) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hpow).ne' hYpos.ne').trans_le hC.2.1
  obtain ⟨i, hiS, hi⟩ := Finset.exists_lt_of_sum_lt (s := S)
    (f := fun _ => (0 : ENNReal)) (g := fun i => μ (Z i)) (by simpa using hZpos)
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
  have hlev := hHB.2.2.2.2.2.2.2.2.1 (f i) p ⟨i, hiS, rfl, hp⟩
  have hL : 0 < L := by
    have hp' : p ∈ {p | ∃ i' ∈ S, f i' = f i ∧ p ∈ Z i'} := ⟨i, hiS, rfl, hp⟩
    rw [← hHB.2.2.2.2.2.2.1 (f i)] at hp'
    obtain ⟨j, _, _⟩ := hp'
    exact Fin.pos j
  have hupper := WangZahlLot.Obl.wz_move_two_long_grains_gain.level_le_of_katz_tao
    hδ hA (Real.rpow_nonneg hδ.le _) hC hHB h4 hL
  have hlower := broad_count_lower hδ hδρ (fun i => (hA.2.1 i).1)
    hbr (f i) p ⟨i, hiS, rfl, hp⟩
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hcoeff : 0 ≤ δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) := by positivity
  have hm : 1 ≤ δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) * (2 * m) :=
    hlower.trans (mul_le_mul_of_nonneg_left hlev.2 hcoeff)
  have hinv : δ ^ (-h) * δ ^ h = 1 := by rw [← Real.rpow_add hδ]; simp
  have hmid : c ^ 2 * δ ^ h ≤
      2985984 * δ ^ (-h) * δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) := by
    calc c ^ 2 * δ ^ h = 1 * (c ^ 2 * δ ^ h) := (one_mul _).symm
      _ ≤ (δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100) * (2 * m)) * (c ^ 2 * δ ^ h) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = (2 * δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100)) * (m * δ ^ h * c ^ 2) := by ring
      _ ≤ (2 * δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100)) * (1492992 * δ ^ (-h)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = _ := by ring
  have hfinal := mul_le_mul_of_nonneg_right hmid (Real.rpow_nonneg hδ.le (-h))
  have hp3 : δ ^ (-h) * δ ^ (-h) * δ ^ (-h) = δ ^ (-(3 * h)) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  calc c ^ 2 = (c ^ 2 * δ ^ h) * δ ^ (-h) := by
        rw [mul_assoc, mul_comm (δ ^ h), hinv, mul_one]
    _ ≤ (2985984 * δ ^ (-h) * δ ^ (-h) * (δ / ρ) ^ (ω * ζ / 100)) * δ ^ (-h) := hfinal
    _ = 2985984 * (δ ^ (-h) * δ ^ (-h) * δ ^ (-h)) * (δ / ρ) ^ (ω * ζ / 100) := by ring
    _ = _ := by rw [hp3]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
