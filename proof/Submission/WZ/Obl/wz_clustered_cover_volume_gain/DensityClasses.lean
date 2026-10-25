-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.DensityClasses.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ScaleDyadic

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

/-- Simultaneous dyadic density classes retain a controlled fraction for any
finite measure, including the measure that counts shading incidences. -/
lemma finite_density_pigeonhole {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {k : ℕ} (f : Fin k → α → ℝ) (hf : ∀ j, Measurable (f j))
    {F : Set α} (hF : MeasurableSet F) {t M : ℝ} (ht : 0 < t) (hM : 0 < M) (htM : t ≤ M)
    (hbound : ∀ p ∈ F, ∀ j, t ≤ f j p ∧ f j p ≤ M) :
    ∃ (lam : Fin k → ℝ) (Z : Set α), MeasurableSet Z ∧ Z ⊆ F ∧
      (∀ j, t / 2 ≤ lam j ∧ lam j ≤ M / 2) ∧
      (∀ p ∈ Z, ∀ j, lam j ≤ f j p ∧ f j p ≤ 2 * lam j) ∧
      ν F ≤ (((Scale.dyExp M t + 1) ^ k : ℕ) : ℝ≥0∞) * ν Z := by
  classical
  let D := Scale.dyExp M t + 1
  let v : Fin D → ℝ := fun j => M / (2 * (2 : ℝ) ^ (j : ℕ))
  let C : (Fin k → Fin D) → Set α := fun g => F ∩
    {p | ∀ j, v (g j) ≤ f j p ∧ f j p ≤ 2 * v (g j)}
  have hCm (g : Fin k → Fin D) : MeasurableSet (C g) := by
    apply hF.inter
    have he : {p | ∀ j, v (g j) ≤ f j p ∧ f j p ≤ 2 * v (g j)} =
        ⋂ j, {p | v (g j) ≤ f j p ∧ f j p ≤ 2 * v (g j)} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_le measurable_const (hf j)).inter (measurableSet_le (hf j) measurable_const)
  have hcover : F ⊆ ⋃ g : Fin k → Fin D, C g := by
    intro p hp
    let g : Fin k → Fin D := fun j => ⟨Scale.dyExp M (f j p),
      Nat.lt_succ_of_le (Scale.dyExp_le hM ht (hbound p hp j).1)⟩
    refine mem_iUnion.mpr ⟨g, hp, ?_⟩
    intro j
    have hfp := ht.trans_le (hbound p hp j).1
    have hlow := Scale.le_dyUp hfp (hbound p hp j).2
    have hhi := Scale.dyUp_lt hfp hM
    change M / (2 * (2 : ℝ) ^ Scale.dyExp M (f j p)) ≤ f j p ∧
      f j p ≤ 2 * (M / (2 * (2 : ℝ) ^ Scale.dyExp M (f j p)))
    have he : M / (2 * (2 : ℝ) ^ Scale.dyExp M (f j p)) = Scale.dyUp M (f j p) / 2 := by
      dsimp [Scale.dyUp]
      ring
    rw [he]
    constructor <;> linarith
  have hD : 0 < D := Nat.succ_pos _
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨g, _, hg⟩ := Finset.exists_max_image Finset.univ (fun g : Fin k → Fin D => ν (C g))
    Finset.univ_nonempty
  refine ⟨fun j => v (g j), C g, hCm g, inter_subset_left, ?_, fun p hp => hp.2, ?_⟩
  · intro j
    have hge : (g j : ℕ) ≤ Scale.dyExp M t := Nat.le_of_lt_succ (g j).isLt
    have hden := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hge
    have hvlow : Scale.dyUp M t / 2 ≤ v (g j) := by
      dsimp [Scale.dyUp, v]
      rw [div_div]
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      nlinarith
    have hvhi : v (g j) ≤ M / 2 := by
      dsimp [v]
      apply div_le_div_of_nonneg_left hM.le (by norm_num)
      have hpow : (1 : ℝ) ≤ 2 ^ (g j : ℕ) := one_le_pow₀ (by norm_num)
      nlinarith
    have htl := Scale.le_dyUp ht htM
    exact ⟨(by linarith : t / 2 ≤ Scale.dyUp M t / 2).trans hvlow, hvhi⟩
  · calc
      ν F ≤ ∑ g : Fin k → Fin D, ν (C g) :=
        (measure_mono hcover).trans (measure_iUnion_fintype_le ν C)
      _ ≤ ∑ _g : Fin k → Fin D, ν (C g) := Finset.sum_le_sum fun h hh => hg h hh
      _ = _ := by simp [D, nsmul_eq_mul]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
