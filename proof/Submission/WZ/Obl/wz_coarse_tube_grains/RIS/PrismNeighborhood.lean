-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PrismNeighborhood.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismCount

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

private theorem prism_affine_coord (e : V ≃ₗᵢ[ℝ] V) (z p q : V)
    (t : ℝ) (i : Fin 3) :
    e ((1 - t) • p + t • q - z) i = (1 - t) * e (p - z) i + t * e (q - z) i := by
  rw [show (1 - t) • p + t • q - z = (1 - t) • (p - z) + t • (q - z) by module,
    map_add, map_smul, map_smul]
  rfl

/-- A convex set crossing both long faces of a prism comes within twice the
larger short side of every point of that prism. -/
theorem prism_subset_thickening_of_crossing {a b c : ℝ} {z : V} {W : Set V}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hc : 0 < c)
    (e : V ≃ₗᵢ[ℝ] V) (hW : Convex ℝ W)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ W ∩ P a b c z e, e (p - z) 2 = t) :
    P a b c z e ⊆ thickening (2 * b) W := by
  obtain ⟨pm, hpm, hpmc⟩ := hcross (-c / 2) (by simp)
  obtain ⟨pp, hpp, hppc⟩ := hcross (c / 2) (by simp)
  intro p hp
  let t := (e (p - z) 2 + c / 2) / c
  have hp2 : |e (p - z) 2| ≤ c / 2 := hp.2.2
  have ht0 : 0 ≤ t := div_nonneg (by linarith [(abs_le.mp hp2).1]) hc.le
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hc).mpr
    linarith [(abs_le.mp hp2).2]
  let q := (1 - t) • pm + t • pp
  have hqW : q ∈ W := hW hpm.1 hpp.1 (by linarith) ht0 (by ring)
  have hqP : q ∈ P a b c z e :=
    (Factor.box_convex a b c z e) hpm.2 hpp.2 (by linarith) ht0 (by ring)
  have hqc : e (q - z) 2 = e (p - z) 2 := by
    rw [prism_affine_coord e z pm pp t 2, hpmc, hppc]
    dsimp only [t]
    field_simp
    ring
  have hcoord (i : Fin 3) : e (p - q) i = e (p - z) i - e (q - z) i := by
    rw [show p - q = (p - z) - (q - z) by abel, map_sub]
    rfl
  have h0 : |e (p - q) 0| ≤ a := by
    rw [hcoord]
    have hp0 : |e (p - z) 0| ≤ a / 2 := hp.1
    have hq0 : |e (q - z) 0| ≤ a / 2 := hqP.1
    linarith [abs_sub (e (p - z) 0) (e (q - z) 0)]
  have h1 : |e (p - q) 1| ≤ b := by
    rw [hcoord]
    have hp1 : |e (p - z) 1| ≤ b / 2 := hp.2.1
    have hq1 : |e (q - z) 1| ≤ b / 2 := hqP.2.1
    linarith [abs_sub (e (p - z) 1) (e (q - z) 1)]
  have h2 : e (p - q) 2 = 0 := by rw [hcoord, hqc, sub_self]
  have hnorm : ‖e (p - q)‖ < 2 * b := by
    have h0sq := (sq_le_sq₀ (abs_nonneg _) ha).mpr h0
    have h1sq := (sq_le_sq₀ (abs_nonneg _) hb.le).mpr h1
    have habsq := pow_le_pow_left₀ ha hab 2
    have hsum := EuclideanSpace.real_norm_sq_eq (e (p - q))
    rw [Fin.sum_univ_three, h2] at hsum
    simp only [sq_abs] at h0sq h1sq
    nlinarith [norm_nonneg (e (p - q)), sq_pos_of_pos hb]
  apply mem_thickening_iff.mpr
  refine ⟨q, hqW, ?_⟩
  simpa only [dist_eq_norm, e.norm_map] using hnorm

/-- The entire prism lies in a radius enlargement of a coarse unit tube once
one of its covered fine tubes crosses both long faces. -/
theorem crossing_prism_subset_expanded_coarse {δ ρ a b c : ℝ} {x v y w z : V}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hc : 0 < c) (hbρ : 2 * b ≤ ρ)
    (e : V ≃ₗᵢ[ℝ] V) (hcover : T δ x v ⊆ T ρ y w)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) :
    P a b c z e ⊆ T (2 * ρ) y w := by
  have hcross' : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T ρ y w ∩ P a b c z e, e (p - z) 2 = t := by
    intro t ht
    obtain ⟨p, hp, he⟩ := hcross t ht
    exact ⟨p, ⟨hcover hp.1, hp.2⟩, he⟩
  have hnear := prism_subset_thickening_of_crossing ha hab hb hc e
    ((convex_segment y (y + w)).thickening ρ) hcross'
  exact hnear.trans ((thickening_thickening_subset (2 * b) ρ (segment ℝ y (y + w))).trans
    (thickening_mono (by linarith : 2 * b + ρ ≤ 2 * ρ) _))

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
