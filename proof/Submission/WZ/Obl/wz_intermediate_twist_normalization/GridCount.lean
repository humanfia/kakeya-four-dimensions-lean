-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.GridCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.TransLemmas
import Submission.WZ.Obl.wz_intermediate_twist_normalization.NormTube

/-!
# Translates of a tube on a grid

`sgrid h M a b = (h (a - M), h (b - M), 0)` for `a b : Fin (2M+1)`. If the grid spacing is at
most `ρ / 2`, the translates of a transverse `ρ`-tube contained in a set `P` contain pairwise
disjoint sheared prisms of volume `h² |v 2| ≥ h² / 2`, so their number is at most
`2 |P| / h²` (`grid_count`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube lineAt fib measurable_fib
  volume_eq_lintegral_fib lineAt_two)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two)
open WangZahlLot.Obl.wz_compact_offset_normalization (mem_tube_iff norm_sq_eq)

/-- The grid of horizontal translations. -/
noncomputable def sgrid (h : ℝ) (M : ℕ) (a b : Fin (2 * M + 1)) : Space :=
  WithLp.toLp 2 ![h * ((a : ℝ) - M), h * ((b : ℝ) - M), 0]

@[simp] theorem sgrid_zero (h : ℝ) (M : ℕ) (a b : Fin (2 * M + 1)) :
    sgrid h M a b 0 = h * ((a : ℝ) - M) := by simp [sgrid]

@[simp] theorem sgrid_one (h : ℝ) (M : ℕ) (a b : Fin (2 * M + 1)) :
    sgrid h M a b 1 = h * ((b : ℝ) - M) := by simp [sgrid]

@[simp] theorem sgrid_two (h : ℝ) (M : ℕ) (a b : Fin (2 * M + 1)) : sgrid h M a b 2 = 0 := by
  simp [sgrid]

/-- The sheared prism under a translated tube. -/
def prism (x v s : Space) (h : ℝ) : Set Space :=
  {p | p 2 ∈ Icc (nzlo x v) (nzlo x v + |v 2|) ∧
    p 0 - lineAt x v (p 2) 0 - s 0 ∈ Ico 0 h ∧ p 1 - lineAt x v (p 2) 1 - s 1 ∈ Ico 0 h}

theorem continuous_lineAt_coord (x v : Space) (i : Fin 3) :
    Continuous (fun p : Space => lineAt x v (p 2) i) := by
  have : (fun p : Space => lineAt x v (p 2) i) = fun p => x i + (p 2 - x 2) / v 2 * v i := by
    funext p; simp [lineAt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [this]
  fun_prop

theorem measurableSet_prism (x v s : Space) (h : ℝ) : MeasurableSet (prism x v s h) := by
  have h2 : Continuous fun p : Space => p 2 := by fun_prop
  have h0 : Continuous fun p : Space => p 0 - lineAt x v (p 2) 0 - s 0 :=
    ((by fun_prop : Continuous fun p : Space => p 0).sub (continuous_lineAt_coord x v 0)).sub
      continuous_const
  have h1 : Continuous fun p : Space => p 1 - lineAt x v (p 2) 1 - s 1 :=
    ((by fun_prop : Continuous fun p : Space => p 1).sub (continuous_lineAt_coord x v 1)).sub
      continuous_const
  have he : prism x v s h = (fun p : Space => p 2) ⁻¹' Icc (nzlo x v) (nzlo x v + |v 2|) ∩
      (fun p : Space => p 0 - lineAt x v (p 2) 0 - s 0) ⁻¹' Ico 0 h ∩
      (fun p : Space => p 1 - lineAt x v (p 2) 1 - s 1) ⁻¹' Ico 0 h := by
    ext p; simp [prism, and_assoc]
  rw [he]
  exact ((measurableSet_Icc.preimage h2.measurable).inter
    (measurableSet_Ico.preimage h0.measurable)).inter (measurableSet_Ico.preimage h1.measurable)

/-- The prism lies in the translated tube. -/
theorem prism_subset_tube {ρ h : ℝ} {x v s : Space} (hv2 : v 2 ≠ 0) (hs2 : s 2 = 0)
    (hhρ : h ≤ ρ / 2) : prism x v s h ⊆ tube ρ (x + s) v := by
  intro p ⟨hz, ha, hb⟩
  set z := p 2
  set t := (z - x 2) / v 2 with ht
  have hL : lineAt x v z = x + t • v := rfl
  have ht01 : t ∈ Icc (0 : ℝ) 1 := by
    have hlo := hz.1
    have hhi := hz.2
    simp only [nzlo] at hlo hhi
    rw [ht]
    rcases lt_or_gt_of_ne hv2 with hneg | hpos
    · rw [abs_of_neg hneg] at hhi
      have hmin : min (x 2) (x 2 + v 2) = x 2 + v 2 := min_eq_right (by linarith)
      rw [hmin] at hlo hhi
      constructor
      · exact div_nonneg_of_nonpos (by linarith) hneg.le
      · rw [div_le_one_of_neg hneg]; linarith
    · rw [abs_of_pos hpos] at hhi
      have hmin : min (x 2) (x 2 + v 2) = x 2 := min_eq_left (by linarith)
      rw [hmin] at hlo hhi
      constructor
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]; linarith
  refine mem_tube_iff.mpr ⟨t, ht01, ?_⟩
  rw [dist_eq_norm]
  have h0 : (p - (x + s + t • v)) 0 = p 0 - lineAt x v z 0 - s 0 := by
    rw [hL]; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have h1 : (p - (x + s + t • v)) 1 = p 1 - lineAt x v z 1 - s 1 := by
    rw [hL]; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have h2 : (p - (x + s + t • v)) 2 = 0 := by
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hs2]
    rw [ht]
    field_simp
    ring
  have hsq : ‖p - (x + s + t • v)‖ ^ 2 < ρ ^ 2 := by
    rw [norm_sq_eq, h0, h1, h2]
    have hρ0 : 0 < ρ := by linarith [ha.1, ha.2]
    have e0 : (p 0 - lineAt x v z 0 - s 0) ^ 2 < h ^ 2 :=
      pow_lt_pow_left₀ ha.2 ha.1 two_ne_zero
    have e1 : (p 1 - lineAt x v z 1 - s 1) ^ 2 < h ^ 2 :=
      pow_lt_pow_left₀ hb.2 hb.1 two_ne_zero
    have hh0 : 0 ≤ h := le_trans ha.1 ha.2.le
    have : h ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ hh0 hhρ 2
    nlinarith
  have hρ0 : 0 < ρ := by
    have := ha.1; have := ha.2; linarith
  exact lt_of_pow_lt_pow_left₀ 2 hρ0.le hsq

/-- Prisms of distinct grid points are disjoint. -/
theorem prism_disjoint {h : ℝ} (hh : 0 < h) {M : ℕ} {x v : Space}
    {a b a' b' : Fin (2 * M + 1)} (hne : (a, b) ≠ (a', b')) :
    Disjoint (prism x v (sgrid h M a b) h) (prism x v (sgrid h M a' b') h) := by
  rw [Set.disjoint_left]
  intro p ⟨_, ha, hb⟩ ⟨_, ha', hb'⟩
  simp only [sgrid_zero, sgrid_one] at ha hb ha' hb'
  apply hne
  have key : ∀ (c c' : Fin (2 * M + 1)) (w : ℝ), w - h * ((c : ℝ) - M) ∈ Ico 0 h →
      w - h * ((c' : ℝ) - M) ∈ Ico 0 h → c = c' := by
    intro c c' w hc hc'
    have h1 : h * ((c : ℝ) - c') < h := by linarith [hc.1, hc.2, hc'.1, hc'.2]
    have h2 : -h < h * ((c : ℝ) - c') := by linarith [hc.1, hc.2, hc'.1, hc'.2]
    have h3 : ((c : ℝ) - c') < 1 := by
      by_contra hcon; push Not at hcon; nlinarith
    have h4 : -1 < ((c : ℝ) - c') := by
      by_contra hcon; push Not at hcon; nlinarith
    have h5 : (c : ℕ) = c' := by
      have f1 : ((c : ℕ) : ℝ) < (c' : ℕ) + 1 := by linarith
      have f2 : ((c' : ℕ) : ℝ) < (c : ℕ) + 1 := by linarith
      have e1 : (c : ℕ) < c' + 1 := by exact_mod_cast f1
      have e2 : (c' : ℕ) < c + 1 := by exact_mod_cast f2
      omega
    exact Fin.ext h5
  rw [key a a' _ ha ha', key b b' _ hb hb']

/-- The volume of a prism. -/
theorem volume_prism_ge {h : ℝ} (hh : 0 < h) {x v s : Space} :
    ENNReal.ofReal (h ^ 2 * |v 2|) ≤ volume (prism x v s h) := by
  set f0 : ℝ → ℝ := fun _ => 0 with hf0
  have hf0c : Continuous f0 := continuous_const
  have hm := measurableSet_prism x v s h
  rw [volume_eq_lintegral_fib hf0c hm, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (measurable_fib hf0c hm)]
  set I := Icc (nzlo x v) (nzlo x v + |v 2|)
  have hlow : ∀ z u, I.indicator (fun z => (Ico (lineAt x v z 0 + s 0)
      (lineAt x v z 0 + s 0 + h)).indicator (fun _ => ENNReal.ofReal h) u) z ≤
      fib f0 (prism x v s h) (u, z) := by
    intro z u
    by_cases hz : z ∈ I
    · rw [indicator_of_mem hz]
      by_cases hu : u ∈ Ico (lineAt x v z 0 + s 0) (lineAt x v z 0 + s 0 + h)
      · rw [indicator_of_mem hu]
        have hsub : Ico (lineAt x v z 1 + s 1) (lineAt x v z 1 + s 1 + h) ⊆
            grainFib f0 (prism x v s h) u z := by
          intro y hy
          simp only [grainFib, mem_setOf_eq, prism, ofTwist_zero, ofTwist_one, ofTwist_two, hf0,
            zero_mul, sub_zero]
          refine ⟨hz, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ⟨by linarith [hy.1],
            by linarith [hy.2]⟩⟩
        calc ENNReal.ofReal h = volume (Ico (lineAt x v z 1 + s 1) (lineAt x v z 1 + s 1 + h)) := by
              rw [Real.volume_Ico]; congr 1; ring
          _ ≤ _ := measure_mono hsub
      · rw [indicator_of_notMem hu]; exact zero_le
    · rw [indicator_of_notMem hz]; exact zero_le
  calc ENNReal.ofReal (h ^ 2 * |v 2|)
      = ∫⁻ z, I.indicator (fun _ => ENNReal.ofReal h * ENNReal.ofReal h) z := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ ≤ ∫⁻ z, ∫⁻ u, fib f0 (prism x v s h) (u, z) := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ I
        · rw [indicator_of_mem hz]
          calc ENNReal.ofReal h * ENNReal.ofReal h
              = ∫⁻ u, (Ico (lineAt x v z 0 + s 0) (lineAt x v z 0 + s 0 + h)).indicator
                  (fun _ => ENNReal.ofReal h) u := by
                rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, mul_comm]
                congr 2; ring
            _ ≤ ∫⁻ u, fib f0 (prism x v s h) (u, z) := by
                refine lintegral_mono fun u => ?_
                have := hlow z u
                rwa [indicator_of_mem hz] at this
        · rw [indicator_of_notMem hz]; exact zero_le

open Classical in
/-- **Grid count.** -/
theorem grid_count {ρ h : ℝ} (hh : 0 < h) (hhρ : h ≤ ρ / 2) {x v : Space}
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (M : ℕ) (P : Set Space) :
    ENNReal.ofReal ((Finset.univ.filter (fun ab : Fin (2 * M + 1) × Fin (2 * M + 1) =>
      tube ρ (x + sgrid h M ab.1 ab.2) v ⊆ P)).card * (h ^ 2 / 2)) ≤ volume P := by
  classical
  set S := Finset.univ.filter (fun ab : Fin (2 * M + 1) × Fin (2 * M + 1) =>
      tube ρ (x + sgrid h M ab.1 ab.2) v ⊆ P)
  have hv2ne : v 2 ≠ 0 := by intro h0; rw [h0, abs_zero] at hv2; linarith
  have hsub : (⋃ ab ∈ S, prism x v (sgrid h M ab.1 ab.2) h) ⊆ P := by
    intro p hp
    simp only [mem_iUnion] at hp
    obtain ⟨ab, hab, hp⟩ := hp
    exact (Finset.mem_filter.mp hab).2 (prism_subset_tube hv2ne (sgrid_two _ _ _ _) hhρ hp)
  have hdisj : Set.PairwiseDisjoint (↑S) (fun ab : Fin (2 * M + 1) × Fin (2 * M + 1) =>
      prism x v (sgrid h M ab.1 ab.2) h) := by
    intro ab _ ab' _ hne
    exact prism_disjoint hh hne
  have hvol := measure_biUnion_finset hdisj (fun ab _ => measurableSet_prism x v _ h)
    (μ := volume)
  calc ENNReal.ofReal (S.card * (h ^ 2 / 2))
      = ∑ _ab ∈ S, ENNReal.ofReal (h ^ 2 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ∑ ab ∈ S, volume (prism x v (sgrid h M ab.1 ab.2) h) := by
        refine Finset.sum_le_sum fun ab _ => le_trans (ENNReal.ofReal_le_ofReal ?_)
          (volume_prism_ge hh)
        have : 0 ≤ h ^ 2 := sq_nonneg h
        nlinarith
    _ = volume (⋃ ab ∈ S, prism x v (sgrid h M ab.1 ab.2) h) := hvol.symm
    _ ≤ volume P := measure_mono hsub

end WangZahlLot.Obl.wz_intermediate_twist_normalization
