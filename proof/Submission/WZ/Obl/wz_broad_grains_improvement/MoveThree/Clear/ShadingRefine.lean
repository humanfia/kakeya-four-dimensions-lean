-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.ShadingRefine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/ShadingRefine.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.CommonCut

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/ShadingRefine.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount fiberBodyCount_eq_ncard)

/-- Keep precisely the part of each old grain met by a retained fine shading
from its own assigned fibre. -/
def refinedGrain {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Hs : Fin L → Set V) (W : Fin n → Set V) (j : Fin L) : Set V :=
  Hs j ∩ assignedFiber f W (γ j)

theorem refinedGrain_fibres {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    {Z W : Fin n → Set V} {Hs : Fin L → Set V}
    (hWZ : ∀ i, W i ⊆ Z i)
    (hfib : ∀ k, assignedFiber γ Hs k = assignedFiber f Z k) :
    ∀ k, assignedFiber γ (refinedGrain f γ Hs W) k = assignedFiber f W k := by
  intro k
  change assignedFiber γ (fun j => Hs j ∩ assignedFiber f W (γ j)) k = _
  rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_common_cut, hfib k]
  exact inter_eq_right.mpr
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_mono f hWZ k)

/-- Arbitrary fine subshadings retaining a fraction `t` of the mass retain at
least `t/2` of the old grain mass, after their grain unions are updated. -/
theorem refinedGrain_mass {n N L : ℕ} (f : Fin n → Fin N) (γ : Fin L → Fin N)
    {Z W : Fin n → Set V} {Hs : Fin L → Set V} {m t : ℝ}
    (hm : 0 < m) (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hWm : ∀ i, MeasurableSet (W i))
    (hHm : ∀ j, MeasurableSet (Hs j)) (hWZ : ∀ i, W i ⊆ Z i)
    (hdisj : ∀ j j', j ≠ j' → γ j = γ j' → Disjoint (Hs j) (Hs j'))
    (hfib : ∀ k, assignedFiber γ Hs k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m)
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (W i)) :
    O (t / 2) * ∑ j, μ (Hs j) ≤ ∑ j, μ (refinedGrain f γ Hs W j) := by
  have hnewm (j) : MeasurableSet (refinedGrain f γ Hs W j) := (hHm j).inter
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.measurable_assignedFiber f hWm (γ j))
  have hnewd : ∀ j j', j ≠ j' → γ j = γ j' →
      Disjoint (refinedGrain f γ Hs W j) (refinedGrain f γ Hs W j') :=
    fun j j' hne he => (hdisj j j' hne he).mono inter_subset_left inter_subset_left
  have hnewlevel (k p) (hp : p ∈ assignedFiber f W k) :
      0 ≤ fiberBodyCount f W k p ∧ fiberBodyCount f W k p ≤ 2 * m := by
    have hpoint : p ∈ assignedFiber f Z k :=
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_mono f hWZ k hp
    refine ⟨?_, le_trans ?_ (hlevel k p hpoint).2⟩
    · rw [fiberBodyCount_eq_ncard]
      exact Nat.cast_nonneg _
    · rw [fiberBodyCount_eq_ncard, fiberBodyCount_eq_ncard]
      apply Nat.cast_le.mpr
      exact Set.ncard_mono (fun i hi => ⟨hi.1, hWZ i hi.2⟩)
  have hold := (WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_fine_mass_bounds
    f γ Z Hs hm.le (by positivity) hZm hHm hdisj hfib hlevel).1
  have hnew := (WangZahlLot.Obl.wz_clustered_cover_volume_gain.grain_fine_mass_bounds
    f γ W (refinedGrain f γ Hs W) le_rfl (by positivity) hWm hnewm hnewd
      (refinedGrain_fibres f γ hWZ hfib) hnewlevel).2
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr (show 0 < 2 * m by positivity)).ne' ENNReal.ofReal_ne_top).mp
  calc O (2 * m) * (O (t / 2) * ∑ j, μ (Hs j)) =
      O t * (O m * ∑ j, μ (Hs j)) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul ht]
        congr 2
        ring
    _ ≤ O t * ∑ i, μ (Z i) := mul_le_mul' le_rfl hold
    _ ≤ ∑ i, μ (W i) := hretain
    _ ≤ _ := hnew

/-- Fine subshadings preserve exact grain saturation and crossing after their
grain unions are updated. Only the new mass and multiplicity bounds are needed. -/
theorem HB_shading_refine {δ h h' ρ a c b g m m' : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z W : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N} {z : Fin L → V}
    {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (hWm : ∀ i, MeasurableSet (W i)) (hWZ : ∀ i, W i ⊆ Z i)
    (hsupport : ∀ i, i ∉ S → Z i = ∅)
    (hHB : HB δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (refinedGrain f γ Hs W j))
    (hlevel : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} ∈ Icc m' (2 * m')) :
    HB δ h' n x v S W ρ N y w f a c b g L z e (refinedGrain f γ Hs W) γ m' := by
  obtain ⟨hδa, haρc, hρcc, hc1, hgeom, hdisj, hfib, hden, holdlevel, hcross, hbc, hlocal⟩ := hHB
  have hWoff : ∀ i, i ∉ S → W i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hWZ i).trans (by rw [hsupport i hi]))
  have hfib' (k) : assignedFiber γ Hs k = assignedFiber f Z k := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport k]
    exact hfib k
  refine ⟨hδa, haρc, hρcc, hc1, ?_, ?_, ?_, hmass, hlevel, ?_, hbc, hlocal⟩
  · intro j
    exact ⟨(hgeom j).1.inter
      (WangZahlLot.Obl.wz_clustered_cover_volume_gain.measurable_assignedFiber f hWm (γ j)),
      inter_subset_left.trans (hgeom j).2.1, (hgeom j).2.2⟩
  · intro j j' hne he
    exact (hdisj j j' hne he).mono inter_subset_left inter_subset_left
  · intro k
    change assignedFiber γ (refinedGrain f γ Hs W) k = _
    rw [refinedGrain_fibres f γ hWZ hfib',
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hWoff k]
  · intro i hi j hij hne
    obtain ⟨p, hpW, hpH⟩ := hne
    obtain ⟨hsat, hfront, hends⟩ := hcross i hi j hij ⟨p, hWZ i hpW, hpH.1⟩
    refine ⟨?_, hfront, hends⟩
    rintro q ⟨hqW, hqU⟩
    exact ⟨hsat ⟨hWZ i hqW, hqU⟩, i, hij, hqW⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
