-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainCardinality
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

/-- The parts of the frozen grains configuration used in the medium estimate. -/
structure GrainData (δ h ρ : ℝ) (n N : ℕ) (S : Finset (Fin n))
    (Z : Fin n → Set V) (y w : Fin N → V) (f : Fin n → Fin N) where
  a : ℝ
  c : ℝ
  L : ℕ
  z : Fin L → V
  e : Fin L → V ≃ₗᵢ[ℝ] V
  H : Fin L → Set V
  γ : Fin L → Fin N
  short : δ ≤ a
  middle : a ≤ ρ * c
  long : ρ * c ≤ c
  length : c ≤ 1
  measurable : ∀ j, MeasurableSet (H j)
  shading : ∀ j, H j ⊆ P a (ρ * c) c (z j) (e j)
  parent : ∀ j, P a (ρ * c) c (z j) (e j) ⊆ T ρ (y (γ j)) (w (γ j))
  alignment : ∀ j, (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2
  disjoint : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j)
  fibers : ∀ k, assignedFiber γ H k = {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i}
  density : O (δ ^ h * L * a * (ρ * c) * c) ≤ ∑ j, volume (H j)
  fine : UF n S Z N f
  localCount : ∀ j W, Convex ℝ W →
    O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
      P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
      P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O (δ ^ (-h)) * μ W

theorem grainData_of_G {ω δ h ρ : ℝ} {n N : ℕ} {S : Finset (Fin n)}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    (hG : G ω δ h n x v Y S Z ρ N y w f) : Nonempty (GrainData δ h ρ n N S Z y w f) := by
  obtain ⟨a, c, L, z, e, H, γ, m, hδa, hac, hρcc, hc1, hgeo, hdisj, hfib, hden,
    hfine, -, -, hlocal⟩ := hG.2.2.2
  exact ⟨⟨a, c, L, z, e, H, γ, hδa, hac, hρcc, hc1,
    fun j => (hgeo j).1, fun j => (hgeo j).2.1, fun j => (hgeo j).2.2.1,
    fun j => (hgeo j).2.2.2, hdisj, hfib, hden, ⟨m, hfine⟩, hlocal⟩⟩

namespace GrainData

variable {δ h ρ : ℝ} {n N : ℕ} {S : Finset (Fin n)}
  {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}

lemma fiber_eq (Gd : GrainData δ h ρ n N S Z y w f)
    (hZsupport : ∀ i, i ∉ S → Z i = ∅) (k : Fin N) :
    assignedFiber Gd.γ Gd.H k = assignedFiber f Z k := by
  rw [Gd.fibers, assignedFiber_eq_supported f hZsupport]

lemma shading_in_union (Gd : GrainData δ h ρ n N S Z y w f)
    {Y : Fin n → Set V} (hZY : ∀ i, Z i ⊆ Y i) (j : Fin Gd.L) : Gd.H j ⊆ ⋃ i, Y i := by
  intro p hp
  have hf : p ∈ assignedFiber Gd.γ Gd.H (Gd.γ j) := ⟨j, rfl, hp⟩
  rw [Gd.fibers] at hf
  obtain ⟨i, _, _, hi⟩ := hf
  exact mem_iUnion.mpr ⟨i, hZY i hi⟩

lemma mass_finite (Gd : GrainData δ h ρ n N S Z y w f)
    {Y : Fin n → Set V} (hZY : ∀ i, Z i ⊆ Y i) (hYball : ∀ i, Y i ⊆ ball 0 1) :
    (∑ j, volume (Gd.H j)) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j _
  apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := (0 : V)) (r := 1)).ne
  apply measure_mono
  exact (Gd.shading_in_union hZY j).trans (iUnion_subset hYball)

lemma cardinality (Gd : GrainData δ h ρ n N S Z y w f)
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f) :
    (Gd.L : ℝ) ≤ 4096 * δ ^ (-(2 * h + 5)) :=
  frozen_grain_cardinality hδ hδρ hρ1 hA hC Gd.z Gd.e Gd.H Gd.γ
    Gd.short Gd.middle Gd.long Gd.measurable Gd.shading Gd.parent Gd.disjoint Gd.density

lemma fine_positive (Gd : GrainData δ h ρ n N S Z y w f)
    (hZsupport : ∀ i, i ∉ S → Z i = ∅) (hmass : 0 < ∑ i, volume (Z i)) :
    ∃ m : ℝ, 0 < m ∧ ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
  obtain ⟨m, hm, hlevel⟩ := fine_level_of_UF hZsupport Gd.fine
  have hex : ∃ i, (Z i).Nonempty := by
    by_contra hh
    push_neg at hh
    have he : ∑ i, volume (Z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hh i, measure_empty]
    rw [he] at hmass
    exact lt_irrefl _ hmass
  obtain ⟨i, p, hp⟩ := hex
  have hupper := (hlevel (f i) p ⟨i, rfl, hp⟩).2
  have hcount : 0 < fiberBodyCount f Z (f i) p := by
    rw [fiberBodyCount_eq_ncard]
    apply Nat.cast_pos.mpr
    exact Set.ncard_pos (Set.toFinite _) |>.mpr ⟨i, rfl, hp⟩
  exact ⟨m, by linarith, hlevel⟩

lemma mass_positive (Gd : GrainData δ h ρ n N S Z y w f)
    (hZsupport : ∀ i, i ∉ S → Z i = ∅) (hmass : 0 < ∑ i, volume (Z i)) :
    0 < ∑ j, volume (Gd.H j) := by
  have hex : ∃ j, 0 < volume (Gd.H j) := by
    by_contra hh
    push_neg at hh
    have hZzero (i) : volume (Z i) = 0 := by
      apply le_antisymm _ bot_le
      calc
        _ ≤ volume (assignedFiber f Z (f i)) := measure_mono fun p hp => ⟨i, rfl, hp⟩
        _ = volume (assignedFiber Gd.γ Gd.H (f i)) := by rw [Gd.fiber_eq hZsupport]
        _ ≤ ∑ j, volume (Gd.H j) := by
          exact (measure_mono (by rintro p ⟨j, _, hj⟩; exact mem_iUnion.mpr ⟨j, hj⟩)).trans
            (by simpa only [tsum_fintype] using measure_iUnion_le (μ := volume) Gd.H)
        _ = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (hh j) bot_le
    simp only [hZzero, Finset.sum_const_zero] at hmass
    exact lt_irrefl _ hmass
  obtain ⟨j, hj⟩ := hex
  exact hj.trans_le (Finset.single_le_sum (f := fun j => volume (Gd.H j))
    (fun _ _ => bot_le) (Finset.mem_univ j))

end GrainData

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
