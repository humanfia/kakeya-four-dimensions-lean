-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ParameterCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Geometry
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

def graphPoint (x v : Space) (z : ℝ) : Space :=
  WithLp.toLp 2 ![intercept x v 0 + slope v 0 * z,
    intercept x v 1 + slope v 1 * z, z]

def graphDirection (v : Space) : Space :=
  WithLp.toLp 2 ![slope v 0, slope v 1, 1]

lemma graphDirection_norm_pos (v : Space) : 0 < ‖graphDirection v‖ := by
  have h := abs_coordinate_le_norm (graphDirection v) 2
  change |(1 : ℝ)| ≤ ‖graphDirection v‖ at h
  norm_num at h
  linarith

lemma graphDirection_norm_le {v : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) : ‖graphDirection v‖ ≤ 3 := by
  have h0 := abs_slope_le_two hv htrans 0
  have h1 := abs_slope_le_two hv htrans 1
  have h02 := mul_self_le_mul_self (abs_nonneg _) h0
  have h12 := mul_self_le_mul_self (abs_nonneg _) h1
  have hs := EuclideanSpace.real_norm_sq_eq (graphDirection v)
  simp only [Fin.sum_univ_three] at hs
  change ‖graphDirection v‖ ^ 2 = slope v 0 ^ 2 + slope v 1 ^ 2 + 1 ^ 2 at hs
  nlinarith [sq_abs (slope v 0), sq_abs (slope v 1), norm_nonneg (graphDirection v)]

def graphUnitDirection (v : Space) : Space := ‖graphDirection v‖⁻¹ • graphDirection v

lemma graphUnitDirection_norm (v : Space) : ‖graphUnitDirection v‖ = 1 := by
  rw [graphUnitDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (graphDirection_norm_pos v)),
    inv_mul_cancel₀ (graphDirection_norm_pos v).ne']

lemma graphPoint_mem_long_segment {x v : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    graphPoint x v z ∈ segment ℝ (graphPoint x v (-1))
      (graphPoint x v (-1) + (6 : ℝ) • graphUnitDirection v) := by
  have hz' : 0 ≤ z + 1 := by linarith [hz.1]
  rw [segment_eq_image']
  refine ⟨(z + 1) * ‖graphDirection v‖ / 6, ?_, ?_⟩
  · constructor
    · positivity
    · have hn := graphDirection_norm_le hv htrans
      have hb : z + 1 ≤ 2 := by linarith [hz.2]
      have := mul_le_mul hb hn (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      linarith
  · simp only [add_sub_cancel_left, graphUnitDirection, smul_smul]
    have he : (z + 1) * ‖graphDirection v‖ / 6 * (6 * ‖graphDirection v‖⁻¹) = z + 1 := by
      field_simp [(graphDirection_norm_pos v).ne']
    rw [he]
    ext i
    fin_cases i <;> simp [graphPoint, graphDirection] <;> ring

lemma tube_coordinate_near_graph {δ r : ℝ} {x v x₀ v₀ p : Space}
    (hδr : δ ≤ r) (hv : ‖v‖ = 1) (htrans : (1 / 2 : ℝ) ≤ |v 2|)
    (hp : p ∈ Tube δ x v) (hpz : |p 2| ≤ 1)
    (ha : ∀ i : Fin 2, |intercept x v i.castSucc - intercept x₀ v₀ i.castSucc| ≤ r)
    (hc : ∀ i : Fin 2, |slope v i.castSucc - slope v₀ i.castSucc| ≤ r)
    (i : Fin 2) :
    |p i.castSucc - (intercept x₀ v₀ i.castSucc + slope v₀ i.castSucc * p 2)| < 5 * r := by
  have hh := tube_coordinate_bound hv htrans hp i.castSucc
  have ha' := ha i
  have hc' := hc i
  have hr : 0 ≤ r := (abs_nonneg _).trans ha'
  have hdiff : |(intercept x v i.castSucc + slope v i.castSucc * p 2) -
      (intercept x₀ v₀ i.castSucc + slope v₀ i.castSucc * p 2)| ≤ 2 * r := by
    calc
      _ = |(intercept x v i.castSucc - intercept x₀ v₀ i.castSucc) +
        (slope v i.castSucc - slope v₀ i.castSucc) * p 2| := by congr 1; ring
      _ ≤ |intercept x v i.castSucc - intercept x₀ v₀ i.castSucc| +
        |slope v i.castSucc - slope v₀ i.castSucc| * |p 2| := by
          simpa only [abs_mul] using abs_add_le
            (intercept x v i.castSucc - intercept x₀ v₀ i.castSucc)
            ((slope v i.castSucc - slope v₀ i.castSucc) * p 2)
      _ ≤ r + r * 1 := by gcongr
      _ = 2 * r := by ring
  have htri := abs_sub_le (p i.castSucc)
    (intercept x v i.castSucc + slope v i.castSucc * p 2)
    (intercept x₀ v₀ i.castSucc + slope v₀ i.castSucc * p 2)
  linarith

lemma tube_subset_parameter_cylinder {δ r : ℝ} (hr : 0 < r) (hδr : δ ≤ r)
    {x v x₀ v₀ : Space} (hv : ‖v‖ = 1) (htrans : (1 / 2 : ℝ) ≤ |v 2|)
    (hv₀ : ‖v₀‖ = 1) (htrans₀ : (1 / 2 : ℝ) ≤ |v₀ 2|)
    (hball : Tube δ x v ⊆ ball 0 1)
    (ha : ∀ i : Fin 2, |intercept x v i.castSucc - intercept x₀ v₀ i.castSucc| ≤ r)
    (hc : ∀ i : Fin 2, |slope v i.castSucc - slope v₀ i.castSucc| ≤ r) :
    Tube δ x v ⊆ thickening (10 * r) (segment ℝ (graphPoint x₀ v₀ (-1))
      (graphPoint x₀ v₀ (-1) + (6 : ℝ) • graphUnitDirection v₀)) := by
  intro p hp
  have hpn : ‖p‖ < 1 := by simpa using hball hp
  have hpz : |p 2| ≤ 1 := (abs_coordinate_le_norm p 2).trans hpn.le
  refine mem_thickening_iff.mpr ⟨graphPoint x₀ v₀ (p 2),
    graphPoint_mem_long_segment hv₀ htrans₀ (abs_le.mp hpz), ?_⟩
  have h0 := tube_coordinate_near_graph hδr hv htrans hp hpz ha hc 0
  have h1 := tube_coordinate_near_graph hδr hv htrans hp hpz ha hc 1
  change |p 0 - (intercept x₀ v₀ 0 + slope v₀ 0 * p 2)| < 5 * r at h0
  change |p 1 - (intercept x₀ v₀ 1 + slope v₀ 1 * p 2)| < 5 * r at h1
  have h02 := mul_self_lt_mul_self (abs_nonneg _) h0
  have h12 := mul_self_lt_mul_self (abs_nonneg _) h1
  have hs := EuclideanSpace.real_norm_sq_eq (p - graphPoint x₀ v₀ (p 2))
  simp [Fin.sum_univ_three, graphPoint] at hs
  change ‖p - graphPoint x₀ v₀ (p 2)‖ ^ 2 =
    (p 0 - (intercept x₀ v₀ 0 + slope v₀ 0 * p 2)) ^ 2 +
    (p 1 - (intercept x₀ v₀ 1 + slope v₀ 1 * p 2)) ^ 2 at hs
  rw [dist_eq_norm]
  nlinarith [sq_abs (p 0 - (intercept x₀ v₀ 0 + slope v₀ 0 * p 2)),
    sq_abs (p 1 - (intercept x₀ v₀ 1 + slope v₀ 1 * p 2)), sq_pos_of_pos hr,
    norm_nonneg (p - graphPoint x₀ v₀ (p 2))]

/-- Convex Frostman counts give a two-dimensional count for the four line parameters. -/
theorem lineParameters_frostman_count {η δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hF : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W)
    (q₀ : EuclideanSpace ℝ (Fin 4)) {r : ℝ} (hδr : δ ≤ r) (hr1 : r ≤ 1) :
    (Set.ncard {i | lineParameters (x i) (v i) ∈ ball q₀ r} : ℝ) ≤
      83200 * δ ^ (-η) * (n : ℝ) * r ^ 2 := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  let I : Set (Fin n) := {i | lineParameters (x i) (v i) ∈ ball q₀ r}
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · change (I.ncard : ℝ) ≤ _
    rw [hI, Set.ncard_empty, Nat.cast_zero]
    positivity
  let W : Set Space := thickening (20 * r)
    (segment ℝ (graphPoint (x i₀) (v i₀) (-1))
      (graphPoint (x i₀) (v i₀) (-1) + (6 : ℝ) • graphUnitDirection (v i₀)))
  have hW : Convex ℝ W := (convex_segment _ _).thickening _
  have hvol : volume W ≤ ENNReal.ofReal (83200 * r ^ 2) := by
    have h := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_scaled_volume_le
      (graphUnitDirection_norm (v i₀)) (graphPoint (x i₀) (v i₀) (-1))
      (C := 20) (θ := r) (by norm_num) hr.le hr1
    simpa only [show (8 : ℝ) * (6 + 20) * 20 ^ 2 = 83200 by norm_num] using h
  have hsub : ∀ i ∈ I, Tube δ (x i) (v i) ⊆ W := by
    intro i hi
    have hd : dist (lineParameters (x i) (v i)) (lineParameters (x i₀) (v i₀)) < 2 * r := by
      have hdi : dist (lineParameters (x i) (v i)) q₀ < r := hi
      have hdj : dist q₀ (lineParameters (x i₀) (v i₀)) < r := by
        rw [dist_comm]
        exact hi₀
      exact (dist_triangle _ q₀ _).trans_lt (by linarith)
    have hcoord (j : Fin 4) :
        |lineParameters (x i) (v i) j - lineParameters (x i₀) (v i₀) j| ≤ 2 * r := by
      simpa only [Real.dist_eq] using
        (PiLp.dist_apply_le (lineParameters (x i) (v i))
          (lineParameters (x i₀) (v i₀)) j).trans hd.le
    have ha : ∀ j : Fin 2, |intercept (x i) (v i) j.castSucc -
        intercept (x i₀) (v i₀) j.castSucc| ≤ 2 * r := by
      intro j
      fin_cases j
      · exact hcoord 0
      · exact hcoord 1
    have hc : ∀ j : Fin 2, |slope (v i) j.castSucc -
        slope (v i₀) j.castSucc| ≤ 2 * r := by
      intro j
      fin_cases j
      · exact hcoord 2
      · exact hcoord 3
    have h := tube_subset_parameter_cylinder (by positivity : 0 < 2 * r)
      (by linarith : δ ≤ 2 * r) (hv i) (htrans i) (hv i₀) (htrans i₀) (hball i) ha hc
    simpa only [show 10 * (2 * r) = 20 * r by ring] using h
  have hcard : I.ncard ≤ {i | Tube δ (x i) (v i) ⊆ W}.ncard :=
    Set.ncard_mono hsub
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc
    _ ≤ ENNReal.ofReal ({i | Tube δ (x i) (v i) ⊆ W}.ncard : ℝ) :=
      ENNReal.ofReal_le_ofReal (by exact_mod_cast hcard)
    _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * volume W := hF W hW
    _ ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * ENNReal.ofReal (83200 * r ^ 2) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
