-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.CommonCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/CommonCut.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.GoodGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CommonCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/CommonCut.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set

/-- The sum over the retained support is the full fine shading mass. -/
theorem sum_supported {n : ℕ} {S : Finset (Fin n)} {Z : Fin n → Set V}
    (hZ : ∀ i, i ∉ S → Z i = ∅) : (∑ i ∈ S, μ (Z i)) = ∑ i, μ (Z i) := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  simp [hZ i hi, μ]

/-- A measurable cut in each coarse fibre preserves the geometric cover clauses. -/
theorem cover_common_cut {δ h h' ρ : ℝ} {n N : ℕ} {x v : Fin n → V}
    {Y Z : Fin n → Set V} {S : Finset (Fin n)} {y w : Fin N → V}
    {f : Fin n → Fin N} {flag : Prop} (D : Fin N → Set V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh' : h ≤ h')
    (hC : C δ h n x v Y S Z ρ N y w f flag)
    (hD : ∀ k, MeasurableSet (D k))
    (hmass : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i ∩ D (f i))) :
    C δ h' n x v Y S (fun i => Z i ∩ D (f i)) ρ N y w f flag := by
  have hc := cover_mono hδ hδ1 hhh' hC
  refine ⟨?_, hmass, hc.2.2⟩
  intro i
  refine ⟨(hC.1 i).1.inter (hD (f i)), inter_subset_left.trans (hC.1 i).2.1, ?_⟩
  intro hi
  change Z i ∩ D (f i) = ∅
  rw [(hC.1 i).2.2 hi, empty_inter]

/-- Cutting all fine shadings in a fibre by the same set preserves its angular proportions. -/
theorem broad_common_cut {ω ζ δ h ρ : ℝ} {n N : ℕ} {v : Fin n → V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {f : Fin n → Fin N}
    (D : Fin N → Set V) (hb : Broad ω ζ δ h ρ n N v S Z f) :
    Broad ω ζ δ h ρ n N v S (fun i => Z i ∩ D (f i)) f := by
  intro k p u r hu hδr hrρ
  by_cases hp : p ∈ D k
  · have hbase : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ D (f i)} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hi, hfi, hZ, _⟩; exact ⟨hi, hfi, hZ⟩
      · rintro ⟨hi, hfi, hZ⟩; exact ⟨hi, hfi, hZ, hfi.symm ▸ hp⟩
    have hcap : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ D (f i) ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hi, hfi, ⟨hZ, _⟩, ha⟩; exact ⟨hi, hfi, hZ, ha⟩
      · rintro ⟨hi, hfi, hZ, ha⟩; exact ⟨hi, hfi, ⟨hZ, hfi.symm ▸ hp⟩, ha⟩
    rw [hbase, hcap]
    exact hb k p u r hu hδr hrρ
  · have hbase : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ D (f i)} = ∅ := by
      ext i
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨_, hfi, _, hD⟩
      exact hp (hfi ▸ hD)
    have hcap : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ D (f i) ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} = ∅ := by
      ext i
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨_, hfi, ⟨_, hD⟩, _⟩
      exact hp (hfi ▸ hD)
    rw [hbase, hcap]
    norm_num [q]

/-- The exact saturation and crossing clauses survive a common cut in each fibre. -/
theorem HB_common_cut {δ h h' ρ a c b g m : ℝ} {n N L : ℕ}
    {x v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {y w : Fin N → V} {f : Fin n → Fin N} {z : Fin L → V}
    {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (D : Fin N → Set V) (hD : ∀ k, MeasurableSet (D k))
    (hHB : HB δ h n x v S Z ρ N y w f a c b g L z e Hs γ m)
    (hmass : O (δ ^ h' * L * a * (ρ * c) * c) ≤ ∑ j, μ (Hs j ∩ D (γ j))) :
    HB δ h' n x v S (fun i => Z i ∩ D (f i)) ρ N y w f a c b g
      L z e (fun j => Hs j ∩ D (γ j)) γ m := by
  obtain ⟨hδa, haρc, hρcc, hc1, hgeom, hdisj, hfib, hden, hlevel, hcross, hbc, hlocal⟩ := hHB
  refine ⟨hδa, haρc, hρcc, hc1, ?_, ?_, ?_, hmass, ?_, ?_, hbc, hlocal⟩
  · intro j
    exact ⟨(hgeom j).1.inter (hD (γ j)), inter_subset_left.trans (hgeom j).2.1,
      (hgeom j).2.2⟩
  · intro j j' hne he
    exact (hdisj j j' hne he).mono inter_subset_left inter_subset_left
  · intro k
    ext p
    constructor
    · rintro ⟨j, hj, hp, hpD⟩
      have hpold : p ∈ {p | ∃ j, γ j = k ∧ p ∈ Hs j} := ⟨j, hj, hp⟩
      rw [hfib k] at hpold
      obtain ⟨i, hiS, hi, hpi⟩ := hpold
      exact ⟨i, hiS, hi, hpi, (hi.trans hj.symm).symm ▸ hpD⟩
    · rintro ⟨i, hiS, hi, hp, hpD⟩
      have hpold : p ∈ {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} := ⟨i, hiS, hi, hp⟩
      rw [← hfib k] at hpold
      obtain ⟨j, hj, hpj⟩ := hpold
      exact ⟨j, hj, hpj, (hj.trans hi.symm).symm ▸ hpD⟩
  · intro k p hp
    obtain ⟨i, hiS, hi, hpi, hpD⟩ := hp
    have hpk : p ∈ D k := hi ▸ hpD
    have he : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ D (f i)} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext j
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨hj, hf, hz, _⟩; exact ⟨hj, hf, hz⟩
      · rintro ⟨hj, hf, hz⟩; exact ⟨hj, hf, hz, hf.symm ▸ hpk⟩
    rw [he]
    exact hlevel k p ⟨i, hiS, hi, hpi⟩
  · intro i hi j hij hne
    have hold : (Z i ∩ Hs j).Nonempty := by
      obtain ⟨p, hp, hq⟩ := hne
      exact ⟨p, hp.1, hq.1⟩
    obtain ⟨hsat, hfront, hends⟩ := hcross i hi j hij hold
    refine ⟨?_, hfront, hends⟩
    rintro p ⟨⟨hp, hpD⟩, hpU⟩
    exact ⟨hsat ⟨hp, hpU⟩, hij ▸ hpD⟩

/-- A common cut retaining a fraction `t` of the fine mass retains `t/2` of the
grain mass, and hence gives a complete new cover and grain state. -/
theorem common_cut_stage_data {ω ζ δ h h' ρ a c b g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh' : h ≤ h')
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hH : H δ h n x v S Z ρ N y w f a c b g)
    (D : Fin N → Set V) (hD : ∀ k, MeasurableSet (D k))
    {t : ℝ} (ht : 0 ≤ t) (hbudget : δ ^ h' ≤ (t / 2) * δ ^ h)
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ D (f i))) :
    C δ h' n x v Y S (fun i => Z i ∩ D (f i)) ρ N y w f True ∧
    Broad ω ζ δ h' ρ n N v S (fun i => Z i ∩ D (f i)) f ∧
    H δ h' n x v S (fun i => Z i ∩ D (f i)) ρ N y w f a c b g := by
  obtain ⟨L, z, e, Hs, γ, m, hHB⟩ := H_iff.mp hH
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hC.1 i).1
  have hHm : ∀ j, MeasurableSet (Hs j) := fun j => (hHB.2.2.2.2.1 j).1
  have hfib (k : Fin N) :
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber γ Hs k =
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber f Z k := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport]
    exact hHB.2.2.2.2.2.2.1 k
  obtain ⟨m₀, hm₀, hlevel⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.fine_level_of_UF
    hsupport ⟨m, hHB.2.2.2.2.2.2.2.2.1⟩
  have hZpos : 0 < ∑ i, μ (Z i) := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
    have hYpos : 0 < ∑ i, μ (Y i) :=
      (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hA.2.2.2.1
    have hCpos : 0 < O (δ ^ h) * ∑ i, μ (Y i) :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ h)).ne' hYpos.ne'
    exact hCpos.trans_le (hC.2.1.trans_eq (sum_supported hsupport))
  have hm₀pos : 0 < m₀ := by
    obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ => (0 : ENNReal)) (g := fun i => μ (Z i)) (by simpa using hZpos)
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
    have hupper := (hlevel (f i) p ⟨i, rfl, hp⟩).2
    have hc : 0 < WangZahlLot.Obl.wz_clustered_cover_volume_gain.fiberBodyCount f Z (f i) p := by
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.fiberBodyCount_eq_ncard]
      exact Nat.cast_pos.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, rfl, hp⟩)
    linarith
  have hgrain := WangZahlLot.Obl.wz_clustered_cover_volume_gain.common_cut_retains_grain_mass
    f γ Z Hs D hm₀pos ht hZm hHm hD hHB.2.2.2.2.2.1 hfib hlevel hretain
  have hnewSupport : ∀ i, i ∉ S → Z i ∩ D (f i) = ∅ := by
    intro i hi
    rw [hsupport i hi, empty_inter]
  have hmassC : O (δ ^ h') * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i ∩ D (f i)) := by
    rw [sum_supported hnewSupport]
    calc O (δ ^ h') * ∑ i, μ (Y i)
        ≤ (O t * O (δ ^ h)) * ∑ i, μ (Y i) := by
          apply mul_le_mul' _ le_rfl
          rw [← ENNReal.ofReal_mul ht]
          apply ENNReal.ofReal_le_ofReal
          exact hbudget.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      _ = O t * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_assoc _ _ _
      _ ≤ O t * ∑ i, μ (Z i) :=
        mul_le_mul' le_rfl (hC.2.1.trans_eq (sum_supported hsupport))
      _ ≤ _ := hretain
  refine ⟨cover_common_cut D hδ hδ1 hhh' hC hD hmassC,
    Broad_mono hδ hδ1 hhh' (broad_common_cut D hbr), ?_⟩
  refine H_iff.mpr ⟨L, z, e, (fun j => Hs j ∩ D (γ j)), γ, m,
    HB_common_cut D hD hHB ?_⟩
  have ha : 0 < a := hδ.trans_le hHB.1
  have hρc : 0 < ρ * c := ha.trans_le hHB.2.1
  have hc : 0 < c := hρc.trans_le hHB.2.2.1
  calc O (δ ^ h' * L * a * (ρ * c) * c)
      ≤ O (t / 2) * O (δ ^ h * L * a * (ρ * c) * c) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc δ ^ h' * L * a * (ρ * c) * c
            ≤ ((t / 2) * δ ^ h) * L * a * (ρ * c) * c := by gcongr
          _ = _ := by ring
    _ ≤ O (t / 2) * ∑ j, μ (Hs j) := mul_le_mul' le_rfl hHB.2.2.2.2.2.2.2.1
    _ ≤ _ := hgrain

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
