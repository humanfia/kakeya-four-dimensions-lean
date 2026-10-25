-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.Exponent.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TopScale
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.SharpCluster
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.UniformArithmetic
import Submission.WZ.Obl.wz_balanced_cluster_cover
import Submission.WZ.Obl.wz_measurable_angular_selection
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Arithmetic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters
open scoped ENNReal

/-- A relative convex Frostman bound yields a fixed volume exponent below one. -/
theorem uniform_volume_lower : ∃ a η d : ℝ, 0 < a ∧ 0 < η ∧ 0 < d ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → Separated η δ n x v →
        ENNReal.ofReal (a * δ ^ (3 / 4 : ℝ)) ≤ volume (⋃ i, Y i) := by
  classical
  obtain ⟨C, hC, hbalanced⟩ :=
    WangZahlLot.wz_balanced_cluster_cover WangZahlLot.wz_measurable_angular_selection
  let q : ℝ := 1 / (100 * (C + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqeq : q * (100 * (C + 1)) = 1 := by dsimp [q]; field_simp
  have hq1 : q ≤ 1 := by nlinarith
  have heF : (1 / 2 : ℝ) + (4 * C + 13 / 2) * q ≤ 3 / 4 := by nlinarith
  have heC : (2 * C + 3) * q ≤ (3 / 4 : ℝ) := by nlinarith
  obtain ⟨d, hd, hdmax, hbalanced⟩ := hbalanced q hq hq1
  obtain ⟨c, hc, s, hs, hsmax, hcluster⟩ := sharp_cluster C q q hC hq hq1 hq
  let G : ℝ := 8 * (6 + C) * C ^ 2
  have hG : 0 < G := by dsimp [G]; positivity
  let a : ℝ := min (c / (8 * C) * (56 : ℝ) ^ (-(1 / 2 : ℝ))) (s ^ 2 / (56 * G))
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, q, d, ha, hq, hd, ?_⟩
  intro δ hδ hδd hδmax n x v Y hH hS
  have hδ1 : δ ≤ 1 := by linarith
  have hF := hS.global_frostman hδ hδ1 hH.1 hH.2.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast hH.1
  let m : ℝ := 56 * δ ^ (-q) * (n : ℝ) * δ ^ 2
  have hm : 1 ≤ m := counting_constant_ge_one hδ hδ1 hH.1 hH.2.1 hF
  have hm0 : 0 ≤ m := by linarith
  have hcount : ConvexCount δ m x v := by
    intro W hW
    have h := mul_le_mul' (hF W hW) (le_rfl : ENNReal.ofReal (δ ^ 2) ≤ _)
    rw [← ENNReal.ofReal_mul (by positivity)] at h
    apply h.trans
    have heq : (ENNReal.ofReal (δ ^ (-q) * (n : ℝ)) * volume W) *
        ENNReal.ofReal (δ ^ 2) = ENNReal.ofReal (δ ^ (-q) * (n : ℝ) * δ ^ 2) * volume W := by
      rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
    rw [heq]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    dsimp [m]
    nlinarith [mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ.le (-q)) (Nat.cast_nonneg n)) (sq_nonneg δ)]
  have hslab : SlabCount δ (δ ^ (-q)) x v := by
    intro u t r hu hr
    exact hF _ (slab_convex u t r)
  have hUfin := hH.volume_union_ne_top
  have hlam : 0 < δ ^ q := Real.rpow_pos_of_pos hδ _
  have hlam1 : δ ^ q ≤ 1 := Real.rpow_le_one hδ.le hδ1 hq.le
  obtain ⟨θ, hδθ, hθ1, J, k, f, z, w, Z, hJ, hk, hf, hw, hZm, hZY,
    hdir, hcyl, hdisj, hrobust, hdens, hmass, hupper⟩ :=
    hbalanced δ (δ ^ q) hδ hδd hlam hlam1 n x v Y hH.1 hH.2.1 hH.2.2.1
      hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2
  have hθ : 0 < θ := hδ.trans_le hδθ
  let E : Fin J → Set Space := fun j => ⋃ i, Z j i
  have hEU : ∀ j, E j ⊆ ⋃ i, Y i := by
    intro j p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨f j i, hZY j i hi⟩
  have hEfin : ∀ j, volume (E j) ≠ ∞ := fun j =>
    ne_top_of_le_ne_top hUfin (measure_mono (hEU j))
  have hsum : ∑ j, Vol (E j) ≤ Vol (⋃ i, Y i) :=
    disjoint_sum_le hUfin (fun j => MeasurableSet.iUnion (hZm j)) hdisj hEU
  have hk0 : ∀ j, (0 : ℝ) ≤ k j := fun _ => Nat.cast_nonneg _
  have hL : 0 < δ ^ (C * q) * δ ^ q := by positivity
  have hL1 : δ ^ (C * q) * δ ^ q ≤ 1 := by
    apply (mul_le_mul (Real.rpow_le_one hδ.le hδ1 (by positivity)) hlam1 hlam.le
      (by norm_num : (0 : ℝ) ≤ 1)).trans
    norm_num
  apply (ENNReal.ofReal_le_iff_le_toReal hUfin).mpr
  by_cases hrelative : δ ≤ s * θ
  · have hkbound : ∀ j, (k j : ℝ) ≤ ((8 * C) * δ ^ (-q)) * θ * (n : ℝ) :=
      fun j => cluster_slab_count (by positivity) (by linarith) hθ hslab hH.2.2.1
        (hf j) (hw j) (hcyl j)
    let P : ℝ := c * δ ^ ((3 / 2 : ℝ) + q) * (δ ^ (C * q) * δ ^ q) ^ 3 *
      m ^ (-(1 / 2 : ℝ))
    have hlocal : ∀ j, P * Real.sqrt θ * Real.sqrt (k j : ℝ) ≤ Vol (E j) := by
      intro j
      have hh := hcluster δ θ (δ ^ (C * q) * δ ^ q) m hδ hδmax hδθ hθ1 hrelative
        hL hL1 hm (k j) (fun i => x (f j i)) (fun i => v (f j i)) (Z j) (z j) (w j)
        (hk j) (fun i => hH.2.1 (f j i)) (hw j) (hdir j) (hcyl j) (hZm j)
        (fun i => (hZY j i).trans (hH.2.2.2.2.2.1 (f j i))) (hdens j)
        (convex_count_subfamily hcount (hf j)) (hrobust j)
      apply le_trans _ ((ENNReal.ofReal_le_iff_le_toReal (hEfin j)).mp hh)
      have ht : Real.sqrt θ ≤ θ ^ ((1 / 2 : ℝ) - q) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by linarith)
      dsimp [P]
      rw [Real.sqrt_eq_rpow (k j : ℝ)]
      calc
        _ = c * δ ^ ((3 / 2 : ℝ) + q) * Real.sqrt θ * (δ ^ (C * q) * δ ^ q) ^ 3 *
            m ^ (-(1 / 2 : ℝ)) * (k j : ℝ) ^ (1 / 2 : ℝ) := by ring
        _ ≤ _ := by gcongr
    have hscale : 1 ≤ (8 * C) * δ ^ (-q) := by
      have hp := neg_rpow_ge_one hδ hδ1 hq.le
      nlinarith
    have hbound := fine_sum (fun j => (k j : ℝ)) (fun j => Vol (E j))
      (show 0 ≤ P by dsimp [P]; positivity) hscale hθ hn hk0 hkbound hlocal hmass hsum
    dsimp [P, m] at hbound
    rw [sharp_fine_power hδ hn C q c] at hbound
    apply le_trans _ hbound
    exact mul_le_mul (min_le_left _ _)
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 heF)
      (by positivity) (by positivity)
  · have hkcount : ∀ j, (k j : ℝ) * δ ^ 2 ≤ m * G * θ ^ 2 :=
      fun j => cylinder_count hm0 (by linarith) hθ.le hθ1
        (convex_count_subfamily hcount (hf j)) (hw j) (hcyl j)
    have hkbound : ∀ j, (k j : ℝ) * s ^ 2 ≤ m * G := by
      intro j
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hδ)).mp
      have ht : s ^ 2 * θ ^ 2 ≤ δ ^ 2 := by
        nlinarith [sq_le_sq₀ (by positivity : 0 ≤ s * θ) hδ.le |>.mpr (not_le.mp hrelative).le]
      calc
        δ ^ 2 * ((k j : ℝ) * s ^ 2) = (k j : ℝ) * δ ^ 2 * s ^ 2 := by ring
        _ ≤ (m * G * θ ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right (hkcount j) (sq_nonneg s)
        _ ≤ (m * G) * δ ^ 2 := by nlinarith [mul_nonneg (mul_nonneg hm0 hG.le) (sub_nonneg.mpr ht)]
        _ = δ ^ 2 * (m * G) := by ring
    have hlocal : ∀ j, (δ ^ (C * q) * δ ^ q) * δ ^ 2 ≤ Vol (E j) := by
      intro j
      apply density_union_lower (hk j) (hEfin j)
      convert hdens j using 1
      congr 1
      ring
    have hbound := coarse_sum (fun j => (k j : ℝ)) (fun j => Vol (E j))
      hL.le (mul_pos (by linarith : 0 < m) hG) hs hδ hk0 hkbound hlocal hmass hsum
    have hbound' := coarse_cancel hδ hn hG hbound
    rw [sharp_coarse_power hδ] at hbound'
    apply le_trans _ hbound'
    exact mul_le_mul (min_le_right _ _)
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 heC) (by positivity) (by positivity)

/-- Uniform lower bounds exclude every deficit exponent greater than three quarters. -/
theorem not_examples_of_three_quarters_lt {t : ℝ} (ht : (3 / 4 : ℝ) < t) :
    ¬ Examples t := by
  intro hex
  obtain ⟨a, η, d, ha, hη, hd, hlow⟩ := uniform_volume_lower
  let d1 : ℝ := (a / 2) ^ (1 / (t - 3 / 4))
  have hd1 : 0 < d1 := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨δ, hδ, hδd, hδmax, n, x, v, Y, hH, hS, hV⟩ :=
    hex η (min d d1) hη (lt_min hd hd1)
  have hδd1 : δ ≤ d1 := hδd.trans (min_le_right _ _)
  have hp : δ ^ (t - 3 / 4) ≤ a / 2 := by
    calc
      δ ^ (t - 3 / 4) ≤ d1 ^ (t - 3 / 4) :=
        Real.rpow_le_rpow hδ.le hδd1 (by linarith)
      _ = a / 2 := by
        dsimp [d1]
        rw [← Real.rpow_mul (by positivity : 0 ≤ a / 2)]
        rw [one_div_mul_cancel (by linarith : t - 3 / 4 ≠ 0), Real.rpow_one]
  have hlt : δ ^ t < a * δ ^ (3 / 4 : ℝ) := by
    calc
      δ ^ t = δ ^ (t - 3 / 4) * δ ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ (a / 2) * δ ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ < a * δ ^ (3 / 4 : ℝ) :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hδ _)
  have hh := (hlow δ hδ (hδd.trans (min_le_left _ _)) hδmax n x v Y hH hS).trans hV
  exact hlt.not_ge ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh)

theorem extremal_exponent_le_three_quarters {σ : ℝ}
    (hbelow : ∀ t : ℝ, t < σ → Examples t) : σ ≤ (3 / 4 : ℝ) := by
  by_contra h
  have hσ : (3 / 4 : ℝ) < σ := lt_of_not_ge h
  exact not_examples_of_three_quarters_lt (t := (σ + 3 / 4) / 2) (by linarith)
    (hbelow _ (by linarith))

theorem extremal_exponent_lt_one {σ : ℝ}
    (hbelow : ∀ t : ℝ, t < σ → Examples t) : σ < 1 :=
  (extremal_exponent_le_three_quarters hbelow).trans_lt (by norm_num)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
