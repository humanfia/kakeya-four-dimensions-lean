-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.GrainCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Basic
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.Interfaces

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Two points in the same tube differ from a multiple of its direction by less
than twice the tube radius. -/
theorem tube_two_point_error {δ : ℝ} {x v p q : Space}
    (hp : p ∈ Tube δ x v) (hq : q ∈ Tube δ x v) :
    ∃ s : ℝ, |s| ≤ 1 ∧ ‖(p - q) - s • v‖ < 2 * δ := by
  obtain ⟨p', hp', hpp'⟩ := mem_thickening_iff.mp hp
  obtain ⟨q', hq', hqq'⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hp' hq'
  obtain ⟨t, ht, rfl⟩ := hp'
  obtain ⟨u, hu, rfl⟩ := hq'
  simp only [add_sub_cancel_left, dist_eq_norm] at hpp' hqq'
  refine ⟨t - u, abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩, ?_⟩
  have he : (p - q) - (t - u) • v = (p - (x + t • v)) - (q - (x + u • v)) := by module
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- A coordinate of a rotated vector is bounded by its Euclidean norm. -/
theorem abs_rotated_coord_le (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) (i : Fin 3) :
    |e p i| ≤ ‖p‖ := by
  simpa only [Real.norm_eq_abs, e.norm_map] using PiLp.norm_apply_le (e p) i

/-- Crossing a prism's two long ends forces a small transverse direction
component. The estimate is uniform in the prism's location and orientation. -/
theorem tube_crossing_coordinate_bound {δ a c : ℝ} {x v p q z : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hδc : 4 * δ ≤ c) (hv : ‖v‖ = 1)
    (hp : p ∈ Tube δ x v) (hq : q ∈ Tube δ x v)
    (hpa : |e (p - z) i| ≤ a / 2) (hqa : |e (q - z) i| ≤ a / 2)
    (hpc : e (p - z) 2 = c / 2) (hqc : e (q - z) 2 = -c / 2) :
    |e v i| ≤ 6 * a / c := by
  have hc : 0 < c := by linarith
  obtain ⟨s, -, hs⟩ := tube_two_point_error hp hq
  have hcoord (j : Fin 3) : |e (p - q) j - s * e v j| < 2 * δ := by
    have hh := (abs_rotated_coord_le e ((p - q) - s • v) j).trans_lt hs
    simpa only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hh
  have hpq (j : Fin 3) : e (p - q) j = e (p - z) j - e (q - z) j := by
    rw [show p - q = (p - z) - (q - z) by abel, map_sub]
    rfl
  have hv2 : |e v 2| ≤ 1 := by simpa only [hv] using abs_rotated_coord_le e v 2
  have hlong : c - 2 * δ < s * e v 2 := by
    have hh := (abs_lt.mp (hcoord 2)).2
    rw [hpq, hpc, hqc] at hh
    linarith
  have hslarge : c / 2 ≤ |s| := by
    have hh : s * e v 2 ≤ |s| := calc
      _ ≤ |s * e v 2| := le_abs_self _
      _ = |s| * |e v 2| := abs_mul _ _
      _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left hv2 (abs_nonneg s)
      _ = |s| := mul_one _
    linarith
  have hpqa : |e (p - q) i| ≤ a := by
    rw [hpq]
    exact (abs_sub _ _).trans (by linarith)
  have hsdir : |s| * |e v i| ≤ 3 * a := by
    rw [← abs_mul]
    have hh := abs_sub (e (p - q) i) (e (p - q) i - s * e v i)
    have he : e (p - q) i - (e (p - q) i - s * e v i) = s * e v i := by ring
    rw [he] at hh
    linarith [hcoord i]
  apply (le_div_iff₀ hc).mpr
  have hh := mul_le_mul_of_nonneg_right hslarge (abs_nonneg (e v i))
  nlinarith


/-- A bound on a transverse direction component propagates from one point to
all points of the tube, at a cost of twice its radius. -/
theorem tube_coordinate_bound {δ A d : ℝ} {x v z q : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3)
    (hq : q ∈ Tube δ x v) (hbase : |e (q - z) i| ≤ A) (hdir : |e v i| ≤ d) :
    ∀ p ∈ Tube δ x v, |e (p - z) i| ≤ A + d + 2 * δ := by
  intro p hp
  obtain ⟨s, hs, herr⟩ := tube_two_point_error hp hq
  have herror : |e (p - q) i - s * e v i| < 2 * δ := by
    have hh := (abs_rotated_coord_le e ((p - q) - s • v) i).trans_lt herr
    simpa only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hh
  have hproduct : |s * e v i| ≤ d := by
    rw [abs_mul]
    calc
      _ ≤ 1 * |e v i| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ d := by simpa only [one_mul] using hdir
  have hdiff : |e (p - q) i| ≤ d + 2 * δ := by
    have hh := abs_add_le (e (p - q) i - s * e v i) (s * e v i)
    simp only [sub_add_cancel] at hh
    linarith
  have he : e (p - z) i = e (p - q) i + e (q - z) i := by
    rw [show p - z = (p - q) + (q - z) by abel, map_add]
    rfl
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- Expressing a rotated affine coordinate as a slab with a unit normal. -/
theorem rotated_coordinate_inner (e : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3) (p z : Space) :
    inner ℝ (e.symm (EuclideanSpace.single i 1)) p -
      inner ℝ (e.symm (EuclideanSpace.single i 1)) z = e (p - z) i := by
  rw [← inner_sub_right, ← e.inner_map_map]
  simp [EuclideanSpace.inner_single_left]

namespace Interfaces

/-- The long-end crossing condition in a grains configuration yields the
expected transverse angular bounds for every crossing fine tube. -/
theorem crossing_prism_direction {δ a b c : ℝ} {x v z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hδc : 4 * δ ≤ c) (hv : ‖v‖ = 1)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) :
    |e v 0| ≤ 6 * a / c ∧ |e v 1| ≤ 6 * b / c := by
  obtain ⟨p, hp, hpc⟩ := hcross (c / 2) (by simp)
  obtain ⟨q, hq, hqc⟩ := hcross (-c / 2) (by simp)
  have hpP : |e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧
      |e (p - z) 2| ≤ c / 2 := hp.2
  have hqP : |e (q - z) 0| ≤ a / 2 ∧ |e (q - z) 1| ≤ b / 2 ∧
      |e (q - z) 2| ≤ c / 2 := hq.2
  exact ⟨tube_crossing_coordinate_bound e 0 hδ hδa hδc hv hp.1 hq.1
      hpP.1 hqP.1 hpc hqc,
    tube_crossing_coordinate_bound e 1 hδ (hδa.trans hab) hδc hv hp.1 hq.1
      hpP.2.1 hqP.2.1 hpc hqc⟩


/-- A fine tube crossing a grain is contained in the thin slab obtained by
extending the grain's short side over unit length. -/
theorem crossing_prism_slab {δ a b c : ℝ} {x v z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hδc : 4 * δ ≤ c) (hc1 : c ≤ 1) (hv : ‖v‖ = 1)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) :
    T δ x v ⊆ {p | |e (p - z) 0| ≤ 9 * a / c} := by
  have hc : 0 < c := by linarith
  have ha : 0 ≤ a := hδ.le.trans hδa
  have ha' : a ≤ a / c := (le_div_iff₀ hc).mpr (by nlinarith)
  obtain ⟨q, hq, -⟩ := hcross (c / 2) (by simp)
  have hbase : |e (q - z) 0| ≤ a / 2 := hq.2.1
  have hdir := (crossing_prism_direction e hδ hδa hab hδc hv hcross).1
  intro p hp
  have hh := tube_coordinate_bound e 0 hq.1 hbase hdir p hp
  change |e (p - z) 0| ≤ 9 * a / c
  have hac : 0 ≤ a / c := div_nonneg ha hc.le
  have he : 9 * a / c = 9 * (a / c) := by ring
  rw [he]
  have he' : 6 * a / c = 6 * (a / c) := by ring
  rw [he'] at hh
  linarith

/-- The same geometric slab in the unit-normal form used by the below-slab conditions. -/
theorem crossing_prism_unit_slab {δ a b c : ℝ} {x v z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hδc : 4 * δ ≤ c) (hc1 : c ≤ 1) (hv : ‖v‖ = 1)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) :
    ∃ (u : V) (t : ℝ), ‖u‖ = 1 ∧
      T δ x v ⊆ {p | |inner ℝ u p - t| ≤ 9 * a / c} := by
  refine ⟨e.symm (EuclideanSpace.single 0 1),
    inner ℝ (e.symm (EuclideanSpace.single 0 1)) z, by simp, ?_⟩
  intro p hp
  change |inner ℝ (e.symm (EuclideanSpace.single 0 1)) p -
    inner ℝ (e.symm (EuclideanSpace.single 0 1)) z| ≤ 9 * a / c
  rw [rotated_coordinate_inner]
  exact crossing_prism_slab e hδ hδa hab hδc hc1 hv hcross hp

end Interfaces
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
