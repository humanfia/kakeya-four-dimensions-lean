-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.GrainConstruction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.GrainCrossing

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open LeanEval.Analysis.WangZahlKakeya Set Metric

private theorem axis_coord (e : Space ≃ₗᵢ[ℝ] Space) (x v z : Space)
    (s t : ℝ) (i : Fin 3) :
    e (x + s • v - z) i = e (x + t • v - z) i + (s - t) * e v i := by
  rw [show x + s • v - z = (x + t • v - z) + (s - t) • v by module,
    map_add, map_smul]
  rfl

/-- Within the long coordinate range of a box, a nearly axial tube stays
strictly inside a short coordinate range when its axis passes through the core. -/
theorem tube_short_coordinate_interior {δ a c t₀ : ℝ} {x v z p : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) (i : Fin 3)
    (hδ : 0 < δ) (hδa : 16 * δ ≤ a) (hδc : 16 * δ ≤ c)
    (hlong : 1 / 2 ≤ |e v 2|)
    (hbase : |e (x + t₀ • v - z) i| ≤ a / 8)
    (hbase2 : |e (x + t₀ • v - z) 2| ≤ c / 8)
    (hdir : c * |e v i| ≤ a / 16)
    (hp : p ∈ Tube δ x v) (hpc : |e (p - z) 2| ≤ c / 2) :
    |e (p - z) i| < a / 2 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hpq
  have herr (j : Fin 3) :
      |e (p - z) j - e (x + s • v - z) j| < δ := by
    have hh := (abs_rotated_coord_le e (p - (x + s • v)) j).trans_lt hpq
    rw [show p - (x + s • v) = (p - z) - (x + s • v - z) by abel,
      map_sub] at hh
    exact hh
  have hs2 : |e (x + s • v - z) 2| < c / 2 + δ := by
    have hh := abs_sub (e (p - z) 2)
      (e (p - z) 2 - e (x + s • v - z) 2)
    simp only [sub_sub_cancel] at hh
    linarith [herr 2]
  have hshift : |s - t₀| < 2 * c := by
    have hh := abs_sub (e (x + s • v - z) 2) (e (x + t₀ • v - z) 2)
    have he : e (x + s • v - z) 2 - e (x + t₀ • v - z) 2 =
        (s - t₀) * e v 2 := by rw [axis_coord e x v z s t₀ 2]; ring
    rw [he, abs_mul] at hh
    have hh' := mul_le_mul_of_nonneg_left hlong (abs_nonneg (s - t₀))
    linarith
  have hcoord : |e (x + s • v - z) i| ≤ a / 8 + a / 8 := by
    rw [axis_coord e x v z s t₀ i]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_right hshift.le (abs_nonneg (e v i))
    linarith
  have hh := abs_sub (e (x + s • v - z) i)
    (e (x + s • v - z) i - e (p - z) i)
  simp only [sub_sub_cancel] at hh
  rw [abs_sub_comm] at hh
  linarith [herr i]

namespace Interfaces

private theorem prism_isClosed (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    IsClosed (P a b c z e) := by
  have hc (i : Fin 3) : Continuous (fun p : V => |e (p - z) i|) := by
    fun_prop
  exact (isClosed_le (hc 0) continuous_const).inter
    ((isClosed_le (hc 1) continuous_const).inter (isClosed_le (hc 2) continuous_const))

private theorem prism_interior_of_strict {a b c : ℝ} {z p : V}
    (e : V ≃ₗᵢ[ℝ] V) (h0 : |e (p - z) 0| < a / 2)
    (h1 : |e (p - z) 1| < b / 2) (h2 : |e (p - z) 2| < c / 2) :
    p ∈ interior (P a b c z e) := by
  let U : Set V := {q | |e (q - z) 0| < a / 2 ∧ |e (q - z) 1| < b / 2 ∧
    |e (q - z) 2| < c / 2}
  have hc (i : Fin 3) : Continuous (fun q : V => |e (q - z) i|) := by
    fun_prop
  have hU : IsOpen U := (isOpen_lt (hc 0) continuous_const).inter
    ((isOpen_lt (hc 1) continuous_const).inter (isOpen_lt (hc 2) continuous_const))
  have hsub : U ⊆ P a b c z e := fun q hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
  exact (interior_maximal hsub hU) ⟨h0, h1, h2⟩

/-- A tube passing through a prism's core in a sufficiently axial direction
can meet the prism boundary only at its two long faces. -/
theorem prism_only_long_face_exits {δ a b c t₀ : ℝ} {x v z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ)
    (hδa : 16 * δ ≤ a) (hδb : 16 * δ ≤ b) (hδc : 16 * δ ≤ c)
    (hlong : 1 / 2 ≤ |e v 2|)
    (hbase : |e (x + t₀ • v - z) 0| ≤ a / 8 ∧
      |e (x + t₀ • v - z) 1| ≤ b / 8 ∧ |e (x + t₀ • v - z) 2| ≤ c / 8)
    (hdir0 : c * |e v 0| ≤ a / 16) (hdir1 : c * |e v 1| ≤ b / 16) :
    ∀ p ∈ T δ x v ∩ frontier (P a b c z e), |e (p - z) 2| = c / 2 := by
  intro p hp
  have hpP : p ∈ P a b c z e :=
    (prism_isClosed a b c z e).closure_eq ▸ frontier_subset_closure hp.2
  apply le_antisymm hpP.2.2
  by_contra hlt
  have hp0 := tube_short_coordinate_interior e 0 hδ hδa hδc hlong hbase.1
    hbase.2.2 hdir0 hp.1 hpP.2.2
  have hp1 := tube_short_coordinate_interior e 1 hδ hδb hδc hlong hbase.2.1
    hbase.2.2 hdir1 hp.1 hpP.2.2
  exact hp.2.2 (prism_interior_of_strict e hp0 hp1 (lt_of_not_ge hlt))

/-- The same core and direction assumptions give an axis point on each long
face, provided the core occurs away from the two ends of the unit segment. -/
theorem prism_both_long_faces {δ a b c t₀ : ℝ} {x v z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hδ : 0 < δ)
    (hδa : 16 * δ ≤ a) (hδb : 16 * δ ≤ b) (hδc : 16 * δ ≤ c)
    (ht₀ : 2 * c ≤ t₀) (ht₁ : t₀ ≤ 1 - 2 * c)
    (hlong : 1 / 2 ≤ |e v 2|)
    (hbase : |e (x + t₀ • v - z) 0| ≤ a / 8 ∧
      |e (x + t₀ • v - z) 1| ≤ b / 8 ∧ |e (x + t₀ • v - z) 2| ≤ c / 8)
    (hdir0 : c * |e v 0| ≤ a / 16) (hdir1 : c * |e v 1| ≤ b / 16) :
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t := by
  intro t ht
  have hc : 0 < c := by linarith
  have habst : |t| = c / 2 := by
    rcases ht with rfl | ht
    · rw [neg_div, abs_neg, abs_of_pos (by positivity)]
    · rw [Set.mem_singleton_iff] at ht
      rw [ht, abs_of_pos (by positivity)]
  have hv2 : e v 2 ≠ 0 := by intro h; rw [h, abs_zero] at hlong; linarith
  let s := t₀ + (t - e (x + t₀ • v - z) 2) / e v 2
  have hshift : |s - t₀| ≤ 2 * c := by
    dsimp [s]
    rw [add_sub_cancel_left, abs_div]
    apply (div_le_iff₀ (abs_pos.mpr hv2)).mpr
    have hh := abs_sub t (e (x + t₀ • v - z) 2)
    rw [habst] at hh
    nlinarith [hbase.2.2]
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    have hh := abs_le.mp hshift
    constructor <;> linarith
  have hpaxis : x + s • v ∈ segment ℝ x (x + v) := by
    rw [segment_eq_image']
    exact ⟨s, hs, by simp⟩
  have hpT : x + s • v ∈ T δ x v := self_subset_thickening hδ _ hpaxis
  have hp2 : e (x + s • v - z) 2 = t := by
    rw [axis_coord e x v z s t₀ 2]
    dsimp [s]
    field_simp
    ring
  have hpabs : |e (x + s • v - z) 2| ≤ c / 2 := by rw [hp2, habst]
  have hp0 := tube_short_coordinate_interior e 0 hδ hδa hδc hlong hbase.1
    hbase.2.2 hdir0 hpT hpabs
  have hp1 := tube_short_coordinate_interior e 1 hδ hδb hδc hlong hbase.2.1
    hbase.2.2 hdir1 hpT hpabs
  exact ⟨x + s • v, ⟨hpT, hp0.le, hp1.le, hpabs⟩, hp2⟩

end Interfaces
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
