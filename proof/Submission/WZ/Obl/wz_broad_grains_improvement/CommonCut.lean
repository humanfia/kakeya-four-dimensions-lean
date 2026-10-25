-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CommonCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CommonCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set

/-- A measurable cut shared by all shadings assigned to a coarse tube preserves
its cover, with the displayed retained-mass budget. -/
theorem cover_common_cut {δ h h' ρ t : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    (hC : C δ h n x v Y S Z ρ N y w f b)
    (R : Fin N → Set V) (hR : ∀ k, MeasurableSet (R k))
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ R (f i)))
    (hbudget : δ ^ h' ≤ t * δ ^ h) :
    C δ h' n x v Y S (fun i => Z i ∩ R (f i)) ρ N y w f b := by
  classical
  have hsum : ∑ i ∈ S, μ (Z i) = ∑ i, μ (Z i) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [(hC.1 i).2.2 hi]
  have hsum' : ∑ i ∈ S, μ (Z i ∩ R (f i)) = ∑ i, μ (Z i ∩ R (f i)) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [(hC.1 i).2.2 hi]
  have hC' := cover_mono hδ hδ1 hh hC
  refine ⟨fun i => ⟨(hC.1 i).1.inter (hR (f i)),
    inter_subset_left.trans (hC.1 i).2.1,
    fun hi => by simp [(hC.1 i).2.2 hi]⟩, ?_, hC'.2.2⟩
  rw [hsum']
  calc
    O (δ ^ h') * ∑ i, μ (Y i) ≤ O (t * δ ^ h) * ∑ i, μ (Y i) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hbudget) le_rfl
    _ = O t * (O (δ ^ h) * ∑ i, μ (Y i)) := by
      simp only [O, ENNReal.ofReal_mul ht, mul_assoc]
    _ ≤ O t * ∑ i, μ (Z i) :=
      mul_le_mul' le_rfl (by simpa only [hsum] using hC.2.1)
    _ ≤ _ := hretain

/-- Common fibre cuts preserve exact grains, including their saturation and
crossing clauses. Uniform fine multiplicity transfers retained mass to grains. -/
theorem grains_common_cut {δ h h' ρ a c b g t : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h') (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hsupport : ∀ i, i ∉ S → Z i = ∅)
    (hH : H δ h n x v S Z ρ N y w f a c b g)
    (R : Fin N → Set V) (hR : ∀ k, MeasurableSet (R k))
    (hretain : O t * ∑ i, μ (Z i) ≤ ∑ i, μ (Z i ∩ R (f i)))
    (hbudget : 2 * δ ^ h' ≤ t * δ ^ h) :
    H δ h' n x v S (fun i => Z i ∩ R (f i)) ρ N y w f a c b g := by
  classical
  by_cases hnonempty : ∃ i, (Z i).Nonempty
  swap
  · have he : (fun i => Z i ∩ R (f i)) = Z := by
      funext i
      have hi : Z i = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hi => hnonempty ⟨i, hi⟩)
      simp [hi]
    rw [he]
    exact grains_mono hδ hδ1 hh hH
  obtain ⟨L, z, e, G, γ, m, hda, hab, hbc, hc1,
    hgeom, hdisj, hunion, hmass, hmult, hcross, hb, hcount⟩ := hH
  have hs (i : Fin n) {p : V} (hp : p ∈ Z i) : i ∈ S := by
    by_contra hn
    simp [hsupport i hn] at hp
  have hm : 0 < m := by
    obtain ⟨i, p, hp⟩ := hnonempty
    have hlev := hmult (f i) p ⟨i, hs i hp, rfl, hp⟩
    have hcard : 0 < q n {j | j ∈ S ∧ f j = f i ∧ p ∈ Z j} := by
      exact_mod_cast ((Set.ncard_pos (s := {j | j ∈ S ∧ f j = f i ∧ p ∈ Z j})).mpr
        ⟨i, hs i hp, rfl, hp⟩)
    linarith [hlev.2]
  have heq (k) : wz_clustered_cover_volume_gain.assignedFiber γ G k =
      wz_clustered_cover_volume_gain.assignedFiber f Z k := by
    rw [wz_clustered_cover_volume_gain.assignedFiber_eq_supported f hsupport]
    exact hunion k
  have hlevel (k p) (hp : p ∈ wz_clustered_cover_volume_gain.assignedFiber f Z k) :
      m ≤ wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ∧
      wz_clustered_cover_volume_gain.fiberBodyCount f Z k p ≤ 2 * m := by
    have hset : {i | f i = k ∧ p ∈ Z i} = {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i
      exact ⟨fun hi => ⟨hs i hi.2, hi⟩, fun hi => hi.2⟩
    rw [wz_clustered_cover_volume_gain.fiberBodyCount_eq_ncard, hset]
    obtain ⟨i, hik, hip⟩ := hp
    exact hmult k p ⟨i, hs i hip, hik, hip⟩
  have hgrain := wz_clustered_cover_volume_gain.common_cut_retains_grain_mass
    f γ Z G R hm ht hZm (fun j => (hgeom j).1) hR hdisj heq hlevel hretain
  have ha : 0 ≤ a := (hδ.trans_le hda).le
  have hrc : 0 ≤ ρ * c := ha.trans hab
  have hc : 0 ≤ c := hrc.trans hbc
  refine ⟨L, z, e, (fun j => G j ∩ R (γ j)), γ, m,
    hda, hab, hbc, hc1, ?_, ?_, ?_, ?_, ?_, ?_, hb, hcount⟩
  · intro j
    exact ⟨(hgeom j).1.inter (hR (γ j)),
      inter_subset_left.trans (hgeom j).2.1, (hgeom j).2.2⟩
  · intro j j' hjj hγ
    exact (hdisj j j' hjj hγ).mono inter_subset_left inter_subset_left
  · intro k
    ext p
    constructor
    · rintro ⟨j, hj, hpG, hpR⟩
      obtain ⟨i, hiS, hi, hpZ⟩ := (hunion k).subset ⟨j, hj, hpG⟩
      exact ⟨i, hiS, hi, hpZ, (hi.trans hj.symm) ▸ hpR⟩
    · rintro ⟨i, hiS, hi, hpZ, hpR⟩
      obtain ⟨j, hj, hpG⟩ := (hunion k).symm.subset ⟨i, hiS, hi, hpZ⟩
      exact ⟨j, hj, hpG, (hj.trans hi.symm) ▸ hpR⟩
  · apply le_trans (b := O (t / 2) * O (δ ^ h * L * a * (ρ * c) * c))
    · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ t / 2)]
      apply ENNReal.ofReal_le_ofReal
      have hp : δ ^ h' ≤ (t / 2) * δ ^ h := by linarith
      calc
        _ ≤ ((t / 2) * δ ^ h) * L * a * (ρ * c) * c := by gcongr
        _ = _ := by ring
    · exact (mul_le_mul' le_rfl hmass).trans hgrain
  · intro k p hp
    obtain ⟨i, hiS, hi, hpZ, hpR⟩ := hp
    have hpk : p ∈ R k := hi ▸ hpR
    have he : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ R (f i)} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i
      constructor
      · exact fun h => ⟨h.1, h.2.1, h.2.2.1⟩
      · exact fun h => ⟨h.1, h.2.1, h.2.2, h.2.1.symm ▸ hpk⟩
    rw [he]
    exact hmult k p ⟨i, hiS, hi, hpZ⟩
  · intro i hiS j hij hmeet
    obtain ⟨p, hpZ, hpG⟩ := hmeet
    have hcr := hcross i hiS j hij ⟨p, hpZ.1, hpG.1⟩
    refine ⟨?_, hcr.2⟩
    intro p hp
    exact ⟨hcr.1 ⟨hp.1.1, hp.2⟩, hij ▸ hp.1.2⟩

/-- Cutting within each fibre preserves all relative directional proportions. -/
theorem broad_fibre_common_cut {δ h h' ρ β : ℝ} {n N : ℕ}
    {v : Fin n → V} {Z : Fin n → Set V} {S : Finset (Fin n)}
    {f : Fin n → Fin N} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : h ≤ h')
    (hbr : ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h) * (r / ρ) ^ β * q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i})
    (R : Fin N → Set V) :
    ∀ (k : Fin N) (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ R (f i) ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-h') * (r / ρ) ^ β *
          q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ R (f i)} := by
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hδ.trans_le hdr
  have hρ : 0 < ρ := hr.trans_le hrρ
  by_cases hp : p ∈ R k
  · have he (P : Fin n → Prop) :
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ R (f i) ∧ P i} =
          {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ P i} := by
      ext i
      constructor
      · exact fun h => ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2⟩
      · exact fun h => ⟨h.1, h.2.1, ⟨h.2.2.1, h.2.1.symm ▸ hp⟩, h.2.2.2⟩
    have hbase := he (fun _ => True)
    simp only [and_true] at hbase
    rw [he, hbase]
    apply (hbr k p u r hu hdr hrρ).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hh))
      (Real.rpow_nonneg (div_nonneg hr.le hρ.le) _)
  · have hempty (P : Fin n → Prop) :
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ R (f i) ∧ P i} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hp (hi.2.1 ▸ hi.2.2.1.2)
    have hbase := hempty (fun _ => True)
    simp only [and_true] at hbase
    rw [hempty, hbase]
    simp [q]

end WangZahlLot.Obl.wz_broad_grains_improvement
