-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.FactorKT.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorBox
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

/-!
# The Katz–Tao convex constant of a finite family of `ρ`-tubes as a finite maximum

For a finite family `U` of unit `ρ`-tubes `tube k = thickening ρ (segment (y k) (y k + w k))`
inside `ball 0 R`, the supremum over convex `W` of `#{k ∈ U : tube k ⊆ W} ρ² / vol W` is attained
on the convex hull of the tubes of `U` lying in `W`. So it is the maximum `KT U` of the finitely
many ratios attached to the hulls of subfamilies `S ⊆ U`. This is the constant `C_KT-CW(U)` of WZ
(normalised by `ρ²` instead of the tube volume) used in Proposition 4.6.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical

noncomputable section

variable {N : ℕ} (R ρ : ℝ) (y w : Fin N → Space)

/-- The `k`-th tube. -/
def tube (k : Fin N) : Set Space := thickening ρ (segment ℝ (y k) (y k + w k))

/-- The standing hypotheses on the family. -/
structure Fam : Prop where
  pos : 0 < ρ
  le_one : ρ ≤ 1
  unit : ∀ k, ‖w k‖ = 1
  inBall : ∀ k, tube ρ y w k ⊆ ball 0 R

/-- The tubes of `U` contained in `W`. -/
def sub (U : Finset (Fin N)) (W : Set Space) : Finset (Fin N) :=
  U.filter fun k => tube ρ y w k ⊆ W

/-- The convex hull of the tubes of `S`. -/
def hull (S : Finset (Fin N)) : Set Space := convexHull ℝ (⋃ k ∈ S, tube ρ y w k)

/-- The Katz–Tao ratio of `U` on the hull of `S`. -/
def ratio (U S : Finset (Fin N)) : ℝ :=
  ((sub ρ y w U (hull ρ y w S)).card : ℝ) * ρ ^ 2 / (volume (hull ρ y w S)).toReal

/-- The Katz–Tao convex constant of `U` (normalised by `ρ²`). -/
def KT (U : Finset (Fin N)) : ℝ :=
  U.powerset.sup' U.powerset_nonempty (ratio ρ y w U)

variable {R ρ y w}

theorem mem_sub {U : Finset (Fin N)} {W : Set Space} {k : Fin N} :
    k ∈ sub ρ y w U W ↔ k ∈ U ∧ tube ρ y w k ⊆ W := by
  simp [sub]

theorem sub_subset (U : Finset (Fin N)) (W : Set Space) : sub ρ y w U W ⊆ U :=
  Finset.filter_subset _ _

theorem sub_mono {U U' : Finset (Fin N)} {W W' : Set Space} (hU : U ⊆ U') (hW : W ⊆ W') :
    sub ρ y w U W ⊆ sub ρ y w U' W' := by
  intro k hk
  rw [mem_sub] at hk ⊢
  exact ⟨hU hk.1, hk.2.trans hW⟩

theorem tube_convex (k : Fin N) : Convex ℝ (tube ρ y w k) :=
  (convex_segment _ _).thickening _

theorem tube_subset_hull {S : Finset (Fin N)} {k : Fin N} (hk : k ∈ S) :
    tube ρ y w k ⊆ hull ρ y w S :=
  (subset_biUnion_of_mem (u := fun k => tube ρ y w k) hk).trans (subset_convexHull ℝ _)

theorem hull_subset {S : Finset (Fin N)} {W : Set Space} (hW : Convex ℝ W)
    (h : ∀ k ∈ S, tube ρ y w k ⊆ W) : hull ρ y w S ⊆ W :=
  convexHull_min (iUnion₂_subset h) hW

theorem hull_convex (S : Finset (Fin N)) : Convex ℝ (hull ρ y w S) := convex_convexHull ℝ _

theorem hull_singleton (k : Fin N) : hull ρ y w {k} = tube ρ y w k := by
  simp only [hull, Finset.mem_singleton, iUnion_iUnion_eq_left]
  exact (tube_convex k).convexHull_eq

theorem Fam.hull_subset_ball (hF : Fam R ρ y w) (S : Finset (Fin N)) :
    hull ρ y w S ⊆ ball 0 R :=
  hull_subset (convex_ball 0 R) fun k _ => hF.inBall k

theorem Fam.tube_volume_lower (hF : Fam R ρ y w) (k : Fin N) :
    ENNReal.ofReal (ρ ^ 2) ≤ volume (tube ρ y w k) :=
  WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hF.pos _ _ (hF.unit k)

theorem Fam.tube_volume_upper (hF : Fam R ρ y w) (k : Fin N) :
    volume (tube ρ y w k) ≤ ENNReal.ofReal (384 * ρ ^ 2) :=
  WangZahlLot.Obl.wz_affine_packet_counting_transfer.tube_volume_upper hF.pos hF.le_one _ _
    (hF.unit k)

theorem Fam.hull_volume_lt_top (hF : Fam R ρ y w) (S : Finset (Fin N)) :
    volume (hull ρ y w S) < ⊤ :=
  (measure_mono (hF.hull_subset_ball S)).trans_lt measure_ball_lt_top

theorem Fam.hull_volume_lower (hF : Fam R ρ y w) {S : Finset (Fin N)} (hS : S.Nonempty) :
    ρ ^ 2 ≤ (volume (hull ρ y w S)).toReal := by
  obtain ⟨k, hk⟩ := hS
  have h := (hF.tube_volume_lower k).trans (measure_mono (tube_subset_hull (y := y) (w := w)
    (ρ := ρ) hk))
  exact (ENNReal.ofReal_le_iff_le_toReal (hF.hull_volume_lt_top S).ne).mp h

theorem Fam.hull_volume_pos (hF : Fam R ρ y w) {S : Finset (Fin N)} (hS : S.Nonempty) :
    0 < (volume (hull ρ y w S)).toReal :=
  (pow_pos hF.pos 2).trans_le (hF.hull_volume_lower hS)

theorem ratio_nonneg (U S : Finset (Fin N)) : 0 ≤ ratio ρ y w U S := by
  unfold ratio
  positivity

theorem ratio_le_KT {U S : Finset (Fin N)} (hS : S ⊆ U) : ratio ρ y w U S ≤ KT ρ y w U :=
  Finset.le_sup' (ratio ρ y w U) (Finset.mem_powerset.mpr hS)

theorem exists_ratio_eq_KT (U : Finset (Fin N)) :
    ∃ S ⊆ U, ratio ρ y w U S = KT ρ y w U := by
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_sup' U.powerset_nonempty (ratio ρ y w U)
  exact ⟨S, Finset.mem_powerset.mp hS, h.symm⟩

theorem KT_nonneg (U : Finset (Fin N)) : 0 ≤ KT ρ y w U :=
  (ratio_nonneg U ∅).trans (ratio_le_KT (Finset.empty_subset U))

/-- The Katz–Tao constant is at least `1/384` on a nonempty family. -/
theorem Fam.KT_lower (hF : Fam R ρ y w) {U : Finset (Fin N)} (hU : U.Nonempty) :
    1 / 384 ≤ KT ρ y w U := by
  obtain ⟨k, hk⟩ := hU
  refine le_trans ?_ (ratio_le_KT (Finset.singleton_subset_iff.mpr hk))
  unfold ratio
  rw [hull_singleton]
  have hcard : 1 ≤ ((sub ρ y w U (tube ρ y w k)).card : ℝ) := by
    have : k ∈ sub ρ y w U (tube ρ y w k) := mem_sub.mpr ⟨hk, subset_rfl⟩
    exact_mod_cast Finset.card_pos.mpr ⟨k, this⟩
  have hvpos : 0 < (volume (tube ρ y w k)).toReal := by
    have := hF.hull_volume_pos (S := {k}) (Finset.singleton_nonempty k)
    rwa [hull_singleton] at this
  have hvup : (volume (tube ρ y w k)).toReal ≤ 384 * ρ ^ 2 := by
    have h := hF.tube_volume_upper k
    exact ENNReal.toReal_le_of_le_ofReal (by have := hF.pos; positivity) h
  have hρ2 : 0 < ρ ^ 2 := pow_pos hF.pos 2
  rw [le_div_iff₀ hvpos]
  nlinarith

/-- The Katz–Tao constant is at most `#U`. -/
theorem Fam.KT_upper (hF : Fam R ρ y w) (U : Finset (Fin N)) : KT ρ y w U ≤ U.card := by
  obtain ⟨S, _, hS⟩ := exists_ratio_eq_KT (ρ := ρ) (y := y) (w := w) U
  rw [← hS]
  unfold ratio
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have : sub ρ y w U (hull ρ y w ∅) = ∅ := by
      ext k
      simp only [mem_sub, hull, Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
        convexHull_empty, subset_empty_iff, iff_false, not_and]
      intro _ h
      have hk := hF.hull_volume_pos (S := {k}) (Finset.singleton_nonempty k)
      rw [hull_singleton, h, measure_empty, ENNReal.toReal_zero] at hk
      exact lt_irrefl 0 hk
    simp [this]
  · have hvpos := hF.hull_volume_pos hne
    have hvlow := hF.hull_volume_lower hne
    have hcard : ((sub ρ y w U (hull ρ y w S)).card : ℝ) ≤ U.card := by
      exact_mod_cast Finset.card_le_card (sub_subset U _)
    rw [div_le_iff₀ hvpos]
    have hρ2 : 0 < ρ ^ 2 := pow_pos hF.pos 2
    calc ((sub ρ y w U (hull ρ y w S)).card : ℝ) * ρ ^ 2 ≤ U.card * ρ ^ 2 := by gcongr
      _ ≤ U.card * (volume (hull ρ y w S)).toReal := by gcongr

/-- The Katz–Tao constant is monotone. -/
theorem KT_mono {U U' : Finset (Fin N)} (h : U ⊆ U') : KT ρ y w U ≤ KT ρ y w U' := by
  obtain ⟨S, hSU, hS⟩ := exists_ratio_eq_KT (ρ := ρ) (y := y) (w := w) U
  rw [← hS]
  refine le_trans ?_ (ratio_le_KT (hSU.trans h))
  unfold ratio
  gcongr
  exact sub_mono h subset_rfl

/-- **The Katz–Tao bound.** Every convex set `W` contains at most `KT U · vol W / ρ²` tubes
of `U`. -/
theorem Fam.count_le (hF : Fam R ρ y w) (U : Finset (Fin N)) {W : Set Space}
    (hW : Convex ℝ W) :
    ((sub ρ y w U W).card : ℝ) * ρ ^ 2 ≤ KT ρ y w U * (volume W).toReal ∨
      volume W = ⊤ := by
  by_cases htop : volume W = ⊤
  · exact Or.inr htop
  left
  set S := sub ρ y w U W
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (KT_nonneg U) ENNReal.toReal_nonneg
  have hhW : hull ρ y w S ⊆ W := hull_subset hW fun k hk => (mem_sub.mp hk).2
  have hvol : (volume (hull ρ y w S)).toReal ≤ (volume W).toReal :=
    ENNReal.toReal_mono htop (measure_mono hhW)
  have hcard : (S.card : ℝ) ≤ (sub ρ y w U (hull ρ y w S)).card := by
    exact_mod_cast Finset.card_le_card fun k hk =>
      mem_sub.mpr ⟨(mem_sub.mp hk).1, tube_subset_hull hk⟩
  have hr := ratio_le_KT (ρ := ρ) (y := y) (w := w) (U := U) (S := sub ρ y w U W)
    (sub_subset (ρ := ρ) (y := y) (w := w) U W)
  unfold ratio at hr
  have hvpos := hF.hull_volume_pos hS
  rw [div_le_iff₀ hvpos] at hr
  calc (S.card : ℝ) * ρ ^ 2 ≤ (sub ρ y w U (hull ρ y w S)).card * ρ ^ 2 := by gcongr
    _ ≤ KT ρ y w U * (volume (hull ρ y w S)).toReal := hr
    _ ≤ KT ρ y w U * (volume W).toReal := by gcongr; exact KT_nonneg U

/-- The Katz–Tao bound in the form of the frozen statements. -/
theorem Fam.count_le_ennreal (hF : Fam R ρ y w) (U : Finset (Fin N)) {W : Set Space}
    (hW : Convex ℝ W) {m : ℝ} (hm : KT ρ y w U ≤ m) (hm0 : 0 < m) :
    ENNReal.ofReal (((sub ρ y w U W).card : ℝ) * ρ ^ 2) ≤ ENNReal.ofReal m * volume W := by
  rcases hF.count_le U hW with h | h
  · by_cases htop : volume W = ⊤
    · rw [htop, ENNReal.mul_top (by simpa using hm0)]; exact le_top
    calc ENNReal.ofReal (((sub ρ y w U W).card : ℝ) * ρ ^ 2)
        ≤ ENNReal.ofReal (m * (volume W).toReal) := by
          apply ENNReal.ofReal_le_ofReal
          exact h.trans (by gcongr)
      _ = ENNReal.ofReal m * volume W := by
          rw [ENNReal.ofReal_mul hm0.le, ENNReal.ofReal_toReal htop]
  · rw [h, ENNReal.mul_top (by simpa using hm0)]; exact le_top

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Factor
