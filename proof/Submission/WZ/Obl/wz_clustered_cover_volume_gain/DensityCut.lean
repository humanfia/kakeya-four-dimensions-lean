-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DensityCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

def ballDensity (U : Set Space) (r : ℝ) (p : Space) : ℝ :=
  (volume (U ∩ ball p r)).toReal / r ^ 3

lemma ballDensity_measurable {U : Set Space} (hU : MeasurableSet U) (r : ℝ) :
    Measurable (ballDensity U r) :=
  (measurable_ball_mass hU r).ennreal_toReal.div_const _

lemma ball_mass_finite (U : Set Space) (p : Space) (r : ℝ) :
    volume (U ∩ ball p r) ≠ ⊤ := ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)

lemma ballDensity_mass (U : Set Space) (p : Space) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (ballDensity U r p * r ^ 3) = volume (U ∩ ball p r) := by
  rw [ballDensity, div_mul_cancel₀ _ (pow_ne_zero _ hr.ne'), ENNReal.ofReal_toReal (ball_mass_finite U p r)]

lemma ballDensity_bounds (U : Set Space) (p : Space) {r : ℝ} (hr : 0 < r) :
    0 ≤ ballDensity U r p ∧ ballDensity U r p ≤ 8 := by
  constructor
  · exact div_nonneg ENNReal.toReal_nonneg (by positivity)
  · apply (div_le_iff₀ (pow_pos hr 3)).mpr
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((measure_mono (inter_subset_right.trans ball_subset_closedBall)).trans
        (closedBall_volume_upper p hr.le))

lemma sparse_ball_density_volume {U : Set Space} {r t : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 ≤ t) (hUball : U ⊆ ball 0 1) :
    volume {p | p ∈ U ∧ ballDensity U r p ≤ t} ≤ ENNReal.ofReal (4096 * t) := by
  let F := {p | p ∈ U ∧ ballDensity U r p ≤ t}
  let u := EuclideanSpace.basisFun (Fin 3) ℝ
  have hFball : F ⊆ ball 0 1 := fun p hp => hUball hp.1
  have hFtb : TotallyBounded F := (isCompact_closedBall (0 : Space) 1).totallyBounded.subset
    (hFball.trans ball_subset_closedBall)
  have hbox : F ⊆ orthogonalBox (fun _ => 1) 0 u := by
    intro p hp j
    have hh := abs_real_inner_le_norm (u j) (p - 0)
    rw [u.norm_eq_one, one_mul, sub_zero] at hh
    simpa only [sub_zero] using hh.trans (le_of_lt (by simpa using hFball hp))
  have hbound := ball_density_mass_in_box hr hFtb (fun p (hp : p ∈ F) => hp.1)
    (fun _ => 1) 0 u hbox (by
      intro p hp
      rw [← ballDensity_mass U p hr]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hp.2 (by positivity)))
  have hvol : volume (orthogonalBox (fun _ => 1 + r) 0 u) ≤ ENNReal.ofReal 64 := by
    rw [volume_orthogonalBox _ (by intro j; positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [Fin.prod_univ_three]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r) (by linarith : 1 + r ≤ 2) 3
    nlinarith
  apply hbound.trans
  apply le_trans (mul_le_mul' le_rfl hvol)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * t)]
  apply le_of_eq
  congr 1
  ring

/-- The measure that counts all incidences with a finite shading family. -/
def shadingMeasure {n : ℕ} (Y : Fin n → Set Space) : Measure Space :=
  Measure.sum (fun i => volume.restrict (Y i))

lemma shadingMeasure_apply {n : ℕ} (Y : Fin n → Set Space) {Z : Set Space}
    (hZ : MeasurableSet Z) : shadingMeasure Y Z = ∑ i, volume (Y i ∩ Z) := by
  rw [shadingMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply hZ, inter_comm]

lemma shadingMeasure_univ {n : ℕ} (Y : Fin n → Set Space) :
    shadingMeasure Y univ = ∑ i, volume (Y i) := by
  rw [shadingMeasure_apply Y MeasurableSet.univ]
  simp

lemma shadingMeasure_le {n : ℕ} (Y : Fin n → Set Space) {Z : Set Space}
    (hZ : MeasurableSet Z) : shadingMeasure Y Z ≤ (n : ℝ≥0∞) * volume Z := by
  rw [shadingMeasure_apply Y hZ]
  calc
    _ ≤ ∑ _i : Fin n, volume Z := Finset.sum_le_sum fun _ _ => measure_mono inter_subset_right
    _ = _ := by simp [nsmul_eq_mul]

/-- Discarding points of very low ball density at finitely many radii has a
uniformly small incidence cost. -/
lemma finite_density_cut {k n : ℕ} (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (hr1 : ∀ j, r j ≤ 1) {t : ℝ} (ht : 0 ≤ t) (U : Set Space)
    (hUm : MeasurableSet U) (hUball : U ⊆ ball 0 1) (Y : Fin n → Set Space)
    (hYU : ∀ i, Y i ⊆ U) :
    ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ U ∧
      (∀ p ∈ Z, ∀ j, t ≤ ballDensity U (r j) p) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (Y i ∩ Z)) + ENNReal.ofReal (4096 * k * n * t) := by
  classical
  let B : Set Space := ⋃ j : Fin k, {p | p ∈ U ∧ ballDensity U (r j) p ≤ t}
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun j =>
    hUm.inter (measurableSet_le (ballDensity_measurable hUm (r j)) measurable_const)
  have hBU : B ⊆ U := iUnion_subset fun _ _ hp => hp.1
  have hBvol : volume B ≤ ENNReal.ofReal (4096 * k * t) := by
    calc
      _ ≤ ∑ j : Fin k, volume {p | p ∈ U ∧ ballDensity U (r j) p ≤ t} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin k, ENNReal.ofReal (4096 * t) :=
        Finset.sum_le_sum fun j _ => sparse_ball_density_volume (hr j) (hr1 j) ht hUball
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
        congr 1
        ring
  refine ⟨U \ B, hUm.diff hBm, sdiff_subset, ?_, ?_⟩
  · intro p hp j
    by_contra hj
    exact hp.2 (mem_iUnion.mpr ⟨j, hp.1, (lt_of_not_ge hj).le⟩)
  · have hcover : U ⊆ (U \ B) ∪ B := by intro p hp; exact Classical.byCases (fun h => Or.inr h) (fun h => Or.inl ⟨hp, h⟩)
    have htotal : shadingMeasure Y U = ∑ i, volume (Y i) := by
      rw [shadingMeasure_apply Y hUm]
      apply Finset.sum_congr rfl
      intro i _
      rw [inter_eq_left.mpr (hYU i)]
    have hh := (measure_mono (μ := shadingMeasure Y) hcover).trans (measure_union_le _ _)
    rw [htotal, shadingMeasure_apply Y (hUm.diff hBm)] at hh
    apply hh.trans
    apply add_le_add le_rfl
    apply (shadingMeasure_le Y hBm).trans
    apply (mul_le_mul' le_rfl hBvol).trans_eq
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
