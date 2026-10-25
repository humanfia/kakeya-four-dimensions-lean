/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file NormalCellLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.NormalStrips
import Submission.Obl.k4_scalar_graph_residual_discovery.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- One physical cell meets only a bounded number of normal strips. -/
theorem normal_bin_list_in_cell (row : Fin 2 → ℝ) {p A : ℝ} (hp : 0 < p)
    (hA : 1 + |row 0| + |row 1| ≤ A) (q : Fin 3 → ℤ) :
    ∃ L : Finset ℤ, (L.card : ℝ) ≤ 2 * A + 2 ∧
      ∀ z : Fin 3 → ℝ, cell p z = q → ⌊normalCoordinate row z / p⌋ ∈ L := by
  classical
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ 1 + |row 0| + |row 1|).trans hA
  let S := normalCoordinate row '' {z : Fin 3 → ℝ | cell p z = q}
  have hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ A * p := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    have hgap : ‖z - z'‖ ≤ p := (norm_sub_lt_of_cell_eq hp (hz.trans hz'.symm)).le
    calc
      _ ≤ (1 + |row 0| + |row 1|) * ‖z - z'‖ := normalCoordinate_sub_le row z z'
      _ ≤ A * p := mul_le_mul hA hgap (norm_nonneg _) hA0
  obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    S (mul_nonneg hA0 hp.le) hp 0 hdiam
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    convert hcard using 1
    field_simp
  · intro z hz
    apply hfin.mem_toFinset.mpr
    exact ⟨normalCoordinate row z, ⟨z, hz, rfl⟩, by simp only [sub_zero]⟩

theorem last_coordinate_variation_of_base_cell_normal_band
    (row : Fin 2 → ℝ) {p A a W : ℝ} (hp : 0 < p)
    (hA : W + |row 0| + |row 1| ≤ A) {z z' : Fin 3 → ℝ}
    (hbase : cell p (fun e : Fin 2 => z e.castSucc) =
      cell p (fun e : Fin 2 => z' e.castSucc))
    (hz : normalCoordinate row z ∈ Icc a (a + W * p))
    (hz' : normalCoordinate row z' ∈ Icc a (a + W * p)) :
    |z 2 - z' 2| ≤ A * p := by
  have hgap : ‖(fun e : Fin 2 => z e.castSucc) - (fun e : Fin 2 => z' e.castSucc)‖ ≤ p :=
    (norm_sub_lt_of_cell_eq hp hbase).le
  have h0 : |z 0 - z' 0| ≤ p :=
    (norm_le_pi_norm ((fun e : Fin 2 => z e.castSucc) - (fun e : Fin 2 => z' e.castSucc)) 0).trans hgap
  have h1 : |z 1 - z' 1| ≤ p :=
    (norm_le_pi_norm ((fun e : Fin 2 => z e.castSucc) - (fun e : Fin 2 => z' e.castSucc)) 1).trans hgap
  have hn : |normalCoordinate row z - normalCoordinate row z'| ≤ W * p := by
    apply abs_le.mpr
    constructor <;> linarith [hz.1, hz.2, hz'.1, hz'.2]
  have hid : z 2 - z' 2 = (normalCoordinate row z - normalCoordinate row z') +
      row 0 * (z 0 - z' 0) + row 1 * (z 1 - z' 1) := by
    dsimp only [normalCoordinate]
    ring
  rw [hid]
  calc
    _ ≤ |normalCoordinate row z - normalCoordinate row z'| +
        |row 0 * (z 0 - z' 0)| + |row 1 * (z 1 - z' 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ W * p + |row 0| * p + |row 1| * p := by
      simp only [abs_mul]
      exact add_le_add (add_le_add hn (mul_le_mul_of_nonneg_left h0 (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = (W + |row 0| + |row 1|) * p := by ring
    _ ≤ A * p := mul_le_mul_of_nonneg_right hA hp.le

/-- A normal band of one coarse-cell width inside a rho-cell is covered
by quadratically many physical cells. The narrow normal dimension is retained. -/
theorem normal_band_cell_cover (row : Fin 2 → ℝ) {p ρ A W : ℝ}
    (hp : 0 < p) (hρ : 0 < ρ) (hW : 0 ≤ W) (hA : W + |row 0| + |row 1| ≤ A)
    (q : Fin 3 → ℤ) (a : ℝ) :
    ∃ L : Finset (Fin 3 → ℤ), (L.card : ℝ) ≤ (ρ / p + 2) ^ 2 * (2 * A + 2) ∧
      ∀ z : Fin 3 → ℝ, cell ρ z = q → normalCoordinate row z ∈ Icc a (a + W * p) →
        cell p z ∈ L := by
  classical
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ W + |row 0| + |row 1|).trans hA
  let S (v : Fin 2 → ℤ) : Set ℝ := (fun z : Fin 3 → ℝ => z 2) ''
    {z | cell p (fun e : Fin 2 => z e.castSucc) = v ∧
      normalCoordinate row z ∈ Icc a (a + W * p)}
  have hlist (v : Fin 2 → ℤ) : ∃ F : Finset ℤ, (F.card : ℝ) ≤ 2 * A + 2 ∧
      ∀ z : Fin 3 → ℝ, cell p (fun e : Fin 2 => z e.castSucc) = v →
        normalCoordinate row z ∈ Icc a (a + W * p) → ⌊z 2 / p⌋ ∈ F := by
    have hdiam : ∀ x ∈ S v, ∀ y ∈ S v, dist x y ≤ A * p := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
      exact last_coordinate_variation_of_base_cell_normal_band row hp hA
        (hz.1.trans hz'.1.symm) hz.2 hz'.2
    obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      (S v) (mul_nonneg hA0 hp.le) hp 0 hdiam
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card _ hfin]
      convert hcard using 1
      field_simp
    · intro z hq hn
      apply hfin.mem_toFinset.mpr
      exact ⟨z 2, ⟨z, ⟨hq, hn⟩, rfl⟩, by simp only [sub_zero]⟩
  choose F hFcard hFmem using hlist
  let lower : Fin 2 → ℝ := fun e => (q e.castSucc : ℝ) * ρ
  let Q := cubeIndices p ρ lower
  have hQcard : (Q.card : ℝ) ≤ (ρ / p + 2) ^ 2 := by
    have hc := ENNReal.toReal_mono ENNReal.ofReal_ne_top (card_cubeIndices hp hρ.le lower)
    simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity : 0 ≤ (ρ / p + 2) ^ 2)] using hc
  have hQmem (z : Fin 3 → ℝ) (hz : cell ρ z = q) :
      cell p (fun e : Fin 2 => z e.castSucc) ∈ Q := by
    apply cell_mem_cubeIndices hp lower _
    intro e
    have he := Int.floor_eq_iff.mp (congrFun hz e.castSucc)
    constructor
    · exact (le_div_iff₀ hρ).mp he.1
    · dsimp only [lower]
      have h := (div_lt_iff₀ hρ).mp he.2
      linarith
  let L := Q.biUnion (fun v => (F v).image (fun j => (![v 0, v 1, j] : Fin 3 → ℤ)))
  refine ⟨L, ?_, ?_⟩
  · calc
      (L.card : ℝ) ≤ ∑ v ∈ Q, (((F v).image (fun j => (![v 0, v 1, j] : Fin 3 → ℤ))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Q)
          (t := fun v => (F v).image (fun j => (![v 0, v 1, j] : Fin 3 → ℤ)))
      _ ≤ ∑ v ∈ Q, ((F v).card : ℝ) := Finset.sum_le_sum (fun _ _ => by exact_mod_cast Finset.card_image_le)
      _ ≤ ∑ _v ∈ Q, (2 * A + 2) := Finset.sum_le_sum (fun v _ => hFcard v)
      _ = (Q.card : ℝ) * (2 * A + 2) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hQcard (by positivity)
  · intro z hz hn
    apply Finset.mem_biUnion.mpr
    refine ⟨cell p (fun e : Fin 2 => z e.castSucc), hQmem z hz,
      Finset.mem_image.mpr ⟨⌊z 2 / p⌋, hFmem _ z rfl hn, ?_⟩⟩
    ext e
    fin_cases e <;> rfl

theorem normal_band_cell_cover_quadratic (row : Fin 2 → ℝ) {p ρ A W : ℝ}
    (hp : 0 < p) (hρ : 0 < ρ) (hpρ : p ≤ ρ)
    (hW : 0 ≤ W) (hA : W + |row 0| + |row 1| ≤ A)
    (q : Fin 3 → ℤ) (a : ℝ) :
    ∃ L : Finset (Fin 3 → ℤ), (L.card : ℝ) ≤ 18 * (A + 1) * (ρ / p) ^ 2 ∧
      ∀ z : Fin 3 → ℝ, cell ρ z = q → normalCoordinate row z ∈ Icc a (a + W * p) →
        cell p z ∈ L := by
  obtain ⟨L, hL, hmem⟩ := normal_band_cell_cover row hp hρ hW hA q a
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ W + |row 0| + |row 1|).trans hA
  have hratio : 1 ≤ ρ / p := (le_div_iff₀ hp).mpr (by simpa using hpρ)
  have hquad : (ρ / p + 2) ^ 2 ≤ 9 * (ρ / p) ^ 2 := by nlinarith
  refine ⟨L, hL.trans ?_, hmem⟩
  calc
    _ ≤ (9 * (ρ / p) ^ 2) * (2 * A + 2) :=
      mul_le_mul_of_nonneg_right hquad (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_scalar_graph_residual_discovery
