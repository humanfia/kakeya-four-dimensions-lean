-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The covering hypothesis in the frozen grains statements. -/
def AD (d α C : ℝ) (B : Set ℝ) : Prop :=
  ∀ r R a : ℝ, d ≤ r → r ≤ R → ∃ (m : ℕ) (c : Fin m → ℝ),
    B ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
      (m : ℝ) ≤ C * (R / r) ^ α

/-- Horizontal slices of the twisted projection. -/
def PS (f : ℝ → ℝ) (E : Set Space) (z : ℝ) : Set ℝ :=
  {u | (u, z) ∈ (fun p : Space => (p 0 + f (p 2) * p 1, p 2)) '' E}

/-- Global convex Frostman counts, with exactly the frozen normalization. -/
def GlobalCount (η δ : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ W : Set Space, Convex ℝ W →
    ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
      ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W

lemma ps_mono {f : ℝ → ℝ} {E E' : Set Space} (h : E ⊆ E') (z : ℝ) :
    PS f E z ⊆ PS f E' z := fun _ hu => image_mono h hu

lemma ad_mono {d α C : ℝ} {B B' : Set ℝ} (h : AD d α C B) (hB : B' ⊆ B) :
    AD d α C B' := by
  intro r R a hdr hrR
  obtain ⟨m, c, hc, hm⟩ := h r R a hdr hrR
  exact ⟨m, c, (inter_subset_inter_left _ hB).trans hc, hm⟩

lemma ps_subset_interval {f : ℝ → ℝ} {E : Set Space} {z : ℝ}
    (hE : E ⊆ ball 0 1) (hf : |f z| ≤ 1) : PS f E z ⊆ Icc (-2) 2 := by
  rintro u ⟨p, hp, he⟩
  obtain ⟨hu, hz⟩ := Prod.mk.inj he
  have hnorm : ‖p‖ ≤ 1 := (mem_ball_zero_iff.mp (hE hp)).le
  have h0 : |p 0| ≤ 1 := (PiLp.norm_apply_le p 0).trans hnorm
  have h1 : |p 1| ≤ 1 := (PiLp.norm_apply_le p 1).trans hnorm
  have hab : |u| ≤ 2 := by
    rw [← hu, hz]
    calc |p 0 + f z * p 1| ≤ |p 0| + |f z| * |p 1| := by
          simpa only [abs_mul] using abs_add_le (p 0) (f z * p 1)
      _ ≤ 1 + 1 * 1 := add_le_add h0 (mul_le_mul hf h1 (abs_nonneg _) zero_le_one)
      _ = 2 := by norm_num
  exact abs_le.mp hab

/-- A covering at the bottom scale bounds the length of the entire bounded slice. -/
lemma volume_le_of_ad {d α C a R : ℝ} {B : Set ℝ}
    (hd : 0 ≤ d) (hdR : d ≤ R) (hB : B ⊆ Icc a (a + R)) (h : AD d α C B) :
    volume B ≤ ENNReal.ofReal (2 * d * (C * (R / d) ^ α)) := by
  obtain ⟨m, c, hc, hm⟩ := h d R a le_rfl hdR
  have hcover : B ⊆ ⋃ j, closedBall (c j) d := by
    simpa only [inter_eq_left.mpr hB] using hc
  calc volume B ≤ volume (⋃ j, closedBall (c j) d) := measure_mono hcover
    _ ≤ ∑ j, volume (closedBall (c j) d) := measure_iUnion_fintype_le volume _
    _ = ENNReal.ofReal (2 * d * (m : ℝ)) := by
      simp only [Real.volume_closedBall, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hm (by positivity))

/-- The all-scale local counts imply the global convex count by summing the scale-one fibres. -/
lemma globalCount_of_strong {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : Strong η δ n x v) :
    GlobalCount η δ n x v := by
  classical
  obtain ⟨ρ, hρ, hρ1, _, k, _, z, w, hcov, _⟩ := hS 1 hδ1 le_rfl
  have hρeq : ρ = 1 := le_antisymm hρ1 hρ
  subst ρ
  obtain ⟨_, _, hu, _, _, hfrost⟩ := hcov
  choose a ha using fun i => (hu i).exists
  have haiff : ∀ i j, Tube δ (x i) (v i) ⊆ Tube 1 (z j) (w j) ↔ a i = j := by
    intro i j
    exact ⟨fun hij => (hu i).unique (ha i) hij, fun hij => hij ▸ ha i⟩
  have hsum (P : Fin n → Prop) :
      ∑ j : Fin k, ncard {i | Tube δ (x i) (v i) ⊆ Tube 1 (z j) (w j) ∧ P i} =
        ncard {i | P i} := by
    simp_rw [haiff, ncard_setOf]
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter P) (t := Finset.univ) (f := a) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.filter_filter, and_comm] using h.symm
  intro W hW
  calc ENNReal.ofReal (ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ)
      = ∑ j : Fin k, ENNReal.ofReal
          ((ncard {i | Tube δ (x i) (v i) ⊆ Tube 1 (z j) (w j) ∧
            Tube δ (x i) (v i) ⊆ W} : ℝ) * (1 : ℝ) ^ 2) := by
        simp only [one_pow, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _), ← Nat.cast_sum,
          hsum]
    _ ≤ ∑ j : Fin k, ENNReal.ofReal
          (δ ^ (-η) * (ncard {i | Tube δ (x i) (v i) ⊆ Tube 1 (z j) (w j)} : ℝ)) *
            volume W := Finset.sum_le_sum (fun j _ => hfrost j W hW)
    _ = ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← Finset.mul_sum, ← Nat.cast_sum]
      have hn := hsum (fun _ => True)
      simpa using congrArg (fun m : ℕ => ENNReal.ofReal (δ ^ (-η) * (m : ℝ)) * volume W) hn

end WangZahlLot.Obl.wz_grains_nonsingular_slices
