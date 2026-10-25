-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.LowOverlap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.FairCut
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Monotone

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, LowOverlap.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V μ O q I T X P)

/-- Simultaneously retain the same fraction of each incidence piece and
each prism's union shading. -/
theorem fair_prism_cuts {n L N m : ℕ} (hm : 0 < m)
    (W : Fin n → Fin L → Set V) (γ : Fin L → Fin N)
    (hWm : ∀ i j, MeasurableSet (W i j)) (hWI : ∀ i j, W i j ⊆ I)
    (hcount : ∀ p k, {j | γ j = k ∧ p ∈ ⋃ i, W i j}.ncard ≤ m) :
    ∃ C : Fin L → Set V, (∀ j, MeasurableSet (C j)) ∧
      (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (C j) (C j')) ∧
      (∀ i j, volume (W i j ∩ C j) = (m : ENNReal)⁻¹ * volume (W i j)) ∧
      ∀ j, volume (⋃ i, W i j ∩ C j) = (m : ENNReal)⁻¹ * volume (⋃ i, W i j) := by
  classical
  let B : Option (Fin n) × Fin L → Set V := fun z =>
    match z.1 with
    | none => ⋃ i, W i z.2
    | some i => W i z.2
  have hBm (z : Option (Fin n) × Fin L) : MeasurableSet (B z) := by
    obtain ⟨i, j⟩ := z
    cases i with
    | none => exact MeasurableSet.iUnion (fun i => hWm i j)
    | some i => exact hWm i j
  have hBI (z : Option (Fin n) × Fin L) : B z ⊆ I := by
    obtain ⟨i, j⟩ := z
    cases i with
    | none => exact iUnion_subset (fun i => hWI i j)
    | some i => exact hWI i j
  have hBcount (p : V) (k : Fin N) :
      {j | γ j = k ∧ ∃ z : Option (Fin n) × Fin L, z.2 = j ∧ p ∈ B z}.ncard ≤ m := by
    convert hcount p k using 1
    congr 1
    ext j
    constructor
    · rintro ⟨hj, ⟨i, j'⟩, hji, hp⟩
      change j' = j at hji
      subst j'
      refine ⟨hj, ?_⟩
      cases i with
      | none => exact hp
      | some i => exact mem_iUnion.mpr ⟨i, hp⟩
    · rintro ⟨hj, hp⟩
      exact ⟨hj, (none, j), rfl, hp⟩
  obtain ⟨C, hCm, hdisj, hvol⟩ := fair_fiber_cut hm B hBm hBI Prod.snd γ hBcount
  refine ⟨C, hCm, hdisj, fun i j => hvol (some i, j), ?_⟩
  intro j
  simpa only [B, iUnion_inter] using hvol (none, j)

/-- With a pointwise overlap bound, the last prism stage follows solely by
fair cuts. Neither the prism geometry nor the coarse cover changes. -/
theorem stage_two_of_bounded_overlap {ω ζ δ h h' ρ c : ℝ} {n m : ℕ}
    (D : PrismData n) (x v : Fin n → V) (Y : Fin n → Set V)
    (hm : 0 < m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h')
    (hbudget : O (δ ^ h') ≤ (m : ENNReal)⁻¹ * O (δ ^ h))
    (hYI : ∀ i, Y i ⊆ I) (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (hcount : ∀ p k, {j | D.γ j = k ∧ p ∈ ⋃ i, D.W i j}.ncard ≤ m) :
    G ω ζ δ h' ρ c n x v Y 2 := by
  classical
  rcases H with ⟨ha, hab, hbc, hc, hW, hmass, hdense, hcross, hbroad, hX, hw, hcover, _⟩
  obtain ⟨C, hCm, hdisj, hvol, hvolUnion⟩ := fair_prism_cuts hm D.W D.γ
    (fun i j => (hW i j).1) (fun i j => ((hW i j).2.1.trans inter_subset_left).trans (hYI i)) hcount
  let W' := fun i j => D.W i j ∩ C j
  have hW'm (i : Fin n) (j : Fin D.L) : MeasurableSet (W' i j) := (hW i j).1.inter (hCm j)
  have hW'sub (i : Fin n) (j : Fin D.L) : W' i j ⊆ D.W i j := inter_subset_left
  have hmass' : O (δ ^ h') * ∑ i, volume (Y i) ≤ ∑ i, ∑ j, volume (W' i j) := by
    calc
      _ ≤ ((m : ENNReal)⁻¹ * O (δ ^ h)) * ∑ i, volume (Y i) := mul_le_mul' hbudget le_rfl
      _ ≤ (m : ENNReal)⁻¹ * ∑ i, ∑ j, volume (D.W i j) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl hmass
      _ = _ := by simp only [W', hvol, Finset.mul_sum]
  have hdense' (j : Fin D.L) : O (δ ^ h') * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      volume (⋃ i, W' i j) := by
    calc
      _ ≤ ((m : ENNReal)⁻¹ * O (δ ^ h)) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) :=
        mul_le_mul' hbudget le_rfl
      _ ≤ (m : ENNReal)⁻¹ * volume (⋃ i, D.W i j) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl (hdense j)
      _ = _ := (hvolUnion j).symm
  have hbroad' : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | p ∈ W' i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h') * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W' i j} := by
    intro j p u r hu hdr hrρ
    by_cases hp : p ∈ C j
    · have hc0 : 0 < c := hδ.trans_le (ha.trans (hab.trans hbc))
      have hρ0 : 0 < ρ := (mul_pos_iff.mp (hδ.trans_le (ha.trans hab))).resolve_right
        (by intro h; linarith [h.2]) |>.1
      have hn := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh)
      have hb := (hbroad j p u r hu hdr hrρ).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ0.le) _))
          (Nat.cast_nonneg _))
      simpa only [W', mem_inter_iff, hp, and_true] using hb
    · simp [W', hp, q]
  refine ⟨D.a, D.s, D.L, D.N, D.z, D.e, W', D.y, D.w, D.γ, ha, hab, hbc, hc,
    ?_, hmass', hdense', ?_, hbroad', hX, hw, fun _ => hcover (by norm_num), ?_⟩
  · intro i j
    exact ⟨hW'm i j, (hW'sub i j).trans (hW i j).2.1,
      fun j' hne => ((hW i j).2.2 j' hne).mono (hW'sub i j) (hW'sub i j')⟩
  · intro i j hne
    exact hcross i j (hne.mono (hW'sub i j))
  · intro _ j j' hne hγ
    exact (hdisj j j' hne hγ).mono (iUnion_subset fun _ => inter_subset_right)
      (iUnion_subset fun _ => inter_subset_right)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
