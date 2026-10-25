-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGFibre

/-!
# Slabs across a direction, and a tube meeting every occupied slab

Prop. 4.1, Step 1 of the sticky Kakeya paper (property (P)): in a family of unit tubes
transverse to the slabs `{h z ≤ ⟪p, w⟫ < h (z + 1)}`, some tube `q0` can be chosen so that,
after restricting all shadings to the slabs met by the shading of `q0`, a `τ^ε` fraction of
the mass survives. A tube meets one slab in volume `O(τ² h)`, and Cauchy–Schwarz over the
slabs gives the average.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- The slab of height `h` with index `z` across the direction `w`. -/
def slab (w : Space) (h : ℝ) (z : ℤ) : Set Space :=
  {p | h * z ≤ ⟪p, w⟫ ∧ ⟪p, w⟫ < h * (z + 1)}

/-- The index of the slab containing `p`. -/
noncomputable def slabIndex (w : Space) (h : ℝ) (p : Space) : ℤ := ⌊⟪p, w⟫ / h⌋

theorem mem_slab_slabIndex {w : Space} {h : ℝ} (hh : 0 < h) (p : Space) :
    p ∈ slab w h (slabIndex w h p) := by
  have h1 := Int.floor_le (⟪p, w⟫ / h)
  have h2 := Int.lt_floor_add_one (⟪p, w⟫ / h)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hh.le
    rwa [mul_div_cancel₀ _ hh.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hh
    rwa [mul_div_cancel₀ _ hh.ne'] at this

theorem slabIndex_eq_of_mem {w : Space} {h : ℝ} (hh : 0 < h) {p : Space} {z : ℤ}
    (hp : p ∈ slab w h z) : slabIndex w h p = z := by
  obtain ⟨h1, h2⟩ := hp
  rw [slabIndex, Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hh]; linarith
  · rw [div_lt_iff₀ hh]; linarith

theorem slab_disjoint {w : Space} {h : ℝ} (hh : 0 < h) {z z' : ℤ} (hzz : z ≠ z') :
    Disjoint (slab w h z) (slab w h z') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  exact hzz ((slabIndex_eq_of_mem hh hp).symm.trans (slabIndex_eq_of_mem hh hp'))

theorem measurableSet_slab (w : Space) (h : ℝ) (z : ℤ) : MeasurableSet (slab w h z) := by
  have hm : Measurable fun p : Space => ⟪p, w⟫ := by fun_prop
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

/-- A unit tube transverse to the slabs meets one slab in volume `O(r² h)`. -/
theorem volume_tube_inter_slab_le {r h : ℝ} (hr : 0 < r) (hrh : r ≤ h) {x v w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hvw : 1 / 2 ≤ |⟪v, w⟫|) (z : ℤ) :
    volume (tube r x v ∩ slab w h z) ≤ ENNReal.ofReal (1664 * h * r ^ 2) := by
  let I : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ∃ p ∈ slab w h z, ‖p - (x + t • v)‖ < r}
  have hsub : tube r x v ∩ slab w h z ⊆ thickening r ((fun t => x + t • v) '' I) := by
    rintro p ⟨hp, hps⟩
    obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
    apply mem_thickening_iff.mpr
    exact ⟨x + t • v, ⟨t, ⟨ht, p, hps, hpt⟩, rfl⟩, by rw [dist_eq_norm]; exact hpt⟩
  have hdiam : ∀ s ∈ I, ∀ t ∈ I, dist s t ≤ 6 * h := by
    rintro s ⟨-, p, ⟨hp1, hp2⟩, hps⟩ t ⟨-, p', ⟨hp1', hp2'⟩, hpt⟩
    have hw1 : ∀ u : Space, |⟪u, w⟫| ≤ ‖u‖ := fun u => by
      have := abs_real_inner_le_norm u w
      rwa [hw, mul_one] at this
    have e1 := hw1 (p - (x + s • v))
    have e2 := hw1 (p' - (x + t • v))
    have key : (s - t) * ⟪v, w⟫ = (⟪p, w⟫ - ⟪p', w⟫) - ⟪p - (x + s • v), w⟫ +
        ⟪p' - (x + t • v), w⟫ := by
      simp only [inner_sub_left, inner_add_left, inner_smul_left, RCLike.conj_to_real]
      ring
    have hb : |(s - t) * ⟪v, w⟫| ≤ h + 2 * r := by
      rw [key]
      have hpp : |⟪p, w⟫ - ⟪p', w⟫| ≤ h := by
        rw [abs_le]; constructor <;> linarith
      calc |⟪p, w⟫ - ⟪p', w⟫ - ⟪p - (x + s • v), w⟫ + ⟪p' - (x + t • v), w⟫|
          ≤ |⟪p, w⟫ - ⟪p', w⟫| + |⟪p - (x + s • v), w⟫| + |⟪p' - (x + t • v), w⟫| := by
            have := abs_add_le (⟪p, w⟫ - ⟪p', w⟫ - ⟪p - (x + s • v), w⟫)
              ⟪p' - (x + t • v), w⟫
            have := abs_sub (⟪p, w⟫ - ⟪p', w⟫) ⟪p - (x + s • v), w⟫
            linarith
        _ ≤ h + r + r := by linarith
        _ = h + 2 * r := by ring
    rw [abs_mul] at hb
    rw [Real.dist_eq]
    have h2 : |s - t| * (1 / 2) ≤ h + 2 * r :=
      (mul_le_mul_of_nonneg_left hvw (abs_nonneg _)).trans hb
    linarith
  exact (measure_mono hsub).trans
    ((WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
      (fun t ht => ht.1) hr (by linarith) hdiam).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith)))

theorem measurable_slabIndex (w : Space) (h : ℝ) : Measurable (slabIndex w h) := by
  have hm : Measurable fun p : Space => ⟪p, w⟫ / h := by fun_prop
  exact Int.measurable_floor.comp hm

/-- The slabs met by the shading of `q0`. -/
def slabsOf (w : Space) (h : ℝ) (A : Set Space) : Set Space :=
  {p | (A ∩ slab w h (slabIndex w h p)).Nonempty}

theorem measurableSet_slabsOf (w : Space) (h : ℝ) (A : Set Space) :
    MeasurableSet (slabsOf w h A) :=
  measurable_slabIndex w h (by trivial : MeasurableSet {z : ℤ | (A ∩ slab w h z).Nonempty})

theorem slabsOf_inter_slab {w : Space} {h : ℝ} (hh : 0 < h) (A : Set Space) (z : ℤ) :
    slabsOf w h A ∩ slab w h z = if (A ∩ slab w h z).Nonempty then slab w h z else ∅ := by
  ext p
  simp only [slabsOf, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [slabIndex_eq_of_mem hh h2] at h1
    rw [if_pos h1]; exact h2
  · intro hp
    split_ifs at hp with hz
    · exact ⟨by rwa [slabIndex_eq_of_mem hh hp], hp⟩
    · exact absurd hp (Set.notMem_empty p)

/-- Points of the unit ball lie in a fixed finite set of slabs. -/
theorem slabIndex_mem_Icc {w : Space} (hw : ‖w‖ = 1) {h : ℝ} (hh : 0 < h) {p : Space}
    (hp : p ∈ ball (0 : Space) 1) :
    slabIndex w h p ∈ Finset.Icc (-(⌈1 / h⌉ + 1)) (⌈1 / h⌉ + 1) := by
  have h1 : |⟪p, w⟫| < 1 := by
    have := abs_real_inner_le_norm p w
    rw [hw, mul_one] at this
    have : ‖p‖ < 1 := by simpa using hp
    linarith
  rw [abs_lt] at h1
  have hc := Int.le_ceil (1 / h)
  rw [Finset.mem_Icc, slabIndex]
  constructor
  · have h2 : -(1 / h) < ⟪p, w⟫ / h := by
      rw [lt_div_iff₀ hh]; field_simp; linarith
    have h3 : (-(⌈1 / h⌉ + 1) : ℤ) ≤ ⌊⟪p, w⟫ / h⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    exact h3
  · have h2 : ⟪p, w⟫ / h < 1 / h := by
      rw [div_lt_div_iff_of_pos_right hh]; linarith
    have h3 : ⌊⟪p, w⟫ / h⌋ ≤ ⌈1 / h⌉ + 1 := by
      have := Int.floor_le (⟪p, w⟫ / h)
      have h4 : (⌊⟪p, w⟫ / h⌋ : ℝ) < ⌈1 / h⌉ + 1 := by linarith
      exact_mod_cast h4.le
    exact h3

/-- A set in the unit ball is the disjoint union of its slab pieces. -/
theorem volume_eq_sum_slab {w : Space} (hw : ‖w‖ = 1) {h : ℝ} (hh : 0 < h) {A : Set Space}
    (hA : MeasurableSet A) (hAb : A ⊆ ball 0 1) :
    volume A = ∑ z ∈ Finset.Icc (-(⌈1 / h⌉ + 1)) (⌈1 / h⌉ + 1), volume (A ∩ slab w h z) := by
  rw [← measure_biUnion_finset (fun z _ z' _ hzz => (slab_disjoint hh hzz).mono
    inter_subset_right inter_subset_right) (fun z _ => hA.inter (measurableSet_slab w h z))]
  congr 1
  ext p
  simp only [mem_iUnion, mem_inter_iff, exists_prop]
  constructor
  · intro hp
    exact ⟨slabIndex w h p, slabIndex_mem_Icc hw hh (hAb hp), hp, mem_slab_slabIndex hh p⟩
  · rintro ⟨z, -, hp, -⟩; exact hp

/-- Property (P): some shading meets every slab met by a `τ^ε` fraction of the mass. -/
theorem slab_selection {ε τ h : ℝ} (hτ : 0 < τ) (hτh : τ ≤ h) (hh1 : h ≤ 1)
    {m : ℕ} {X V : Fin m → Space} {Y : Fin m → Set Space}
    (hF : Family ε τ m X V Y) {w : Space} (hw : ‖w‖ = 1)
    (hVw : ∀ q, 1 / 2 ≤ |⟪V q, w⟫|) :
    ∃ q0 : Fin m, τ ^ ε * τ ^ ε * m * τ ^ 2 / 11648 ≤
      ∑ q, (volume (Y q ∩ slabsOf w h (Y q0))).toReal := by
  classical
  obtain ⟨hm, hV, hball, -, hYm, hYT, hmass⟩ := hF
  have hh : 0 < h := lt_of_lt_of_le hτ hτh
  set Z := Finset.Icc (-(⌈1 / h⌉ + 1)) (⌈1 / h⌉ + 1) with hZ
  have hYb : ∀ q, Y q ⊆ ball 0 1 := fun q => (hYT q).trans (hball q)
  have hYfin : ∀ q (A : Set Space), volume (Y q ∩ A) ≠ ⊤ := fun q A =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (inter_subset_left.trans (hYb q)))
  set a : Fin m → ℤ → ℝ := fun q z => (volume (Y q ∩ slab w h z)).toReal with ha
  have ha0 : ∀ q z, 0 ≤ a q z := fun q z => ENNReal.toReal_nonneg
  -- decomposition of the masses over the slabs
  have hdec : ∀ q (A : Set Space), MeasurableSet A →
      (volume (Y q ∩ A)).toReal = ∑ z ∈ Z, (volume (Y q ∩ A ∩ slab w h z)).toReal := by
    intro q A hA
    rw [volume_eq_sum_slab hw hh ((hYm q).inter hA) (inter_subset_left.trans (hYb q)),
      ENNReal.toReal_sum (fun z _ => ne_top_of_le_ne_top (hYfin q A)
        (measure_mono inter_subset_left))]
  have hM : ∀ q, (volume (Y q)).toReal = ∑ z ∈ Z, a q z := by
    intro q
    have := hdec q univ MeasurableSet.univ
    simpa only [inter_univ] using this
  have hR : ∀ q q0, (volume (Y q ∩ slabsOf w h (Y q0))).toReal =
      ∑ z ∈ Z, if (Y q0 ∩ slab w h z).Nonempty then a q z else 0 := by
    intro q q0
    rw [hdec q _ (measurableSet_slabsOf w h (Y q0))]
    apply Finset.sum_congr rfl
    intro z _
    rw [inter_assoc, slabsOf_inter_slab hh]
    split_ifs <;> simp [ha]
  -- slab masses and the number of shadings meeting a slab
  set μ : ℤ → ℝ := fun z => ∑ q, a q z with hμ
  set N : ℤ → ℕ := fun z => (Finset.univ.filter (fun q => (Y q ∩ slab w h z).Nonempty)).card
    with hN
  have hμN : ∀ z, μ z ≤ N z * (1664 * h * τ ^ 2) := by
    intro z
    calc μ z = ∑ q, if (Y q ∩ slab w h z).Nonempty then a q z else 0 := by
          apply Finset.sum_congr rfl
          intro q _
          split_ifs with hne
          · rfl
          · rw [not_nonempty_iff_eq_empty] at hne
            simp [ha, hne]
      _ ≤ ∑ q, if (Y q ∩ slab w h z).Nonempty then 1664 * h * τ ^ 2 else 0 := by
          apply Finset.sum_le_sum
          intro q _
          split_ifs
          · have hvq : 1 / 2 ≤ |⟪V q, w⟫| := hVw q
            exact ENNReal.toReal_le_of_le_ofReal (by positivity)
              ((measure_mono (inter_subset_inter_left _ (hYT q))).trans
                (volume_tube_inter_slab_le hτ hτh (hV q) hw hvq z))
          · exact le_rfl
      _ = N z * (1664 * h * τ ^ 2) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  -- double counting
  have hdouble : ∑ q0, ∑ q, (volume (Y q ∩ slabsOf w h (Y q0))).toReal =
      ∑ z ∈ Z, (N z : ℝ) * μ z := by
    have h1 : ∀ q0, ∑ q, (volume (Y q ∩ slabsOf w h (Y q0))).toReal =
        ∑ z ∈ Z, if (Y q0 ∩ slab w h z).Nonempty then μ z else 0 := by
      intro q0
      simp only [hR]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      split_ifs with hz
      · rfl
      · exact Finset.sum_const_zero
    simp only [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  -- total mass
  set Mt : ℝ := ∑ q, (volume (Y q)).toReal with hMt
  have hMt_eq : Mt = ∑ z ∈ Z, μ z := by
    rw [hMt]
    simp only [hM, hμ]
    exact Finset.sum_comm
  have hMlow : τ ^ ε * m * τ ^ 2 ≤ Mt := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun q _ => by
      simpa only [inter_univ] using hYfin q univ) hmass
    rwa [ENNReal.toReal_sum (fun q _ => by simpa only [inter_univ] using hYfin q univ),
      ENNReal.toReal_ofReal (by positivity)] at h
  -- Cauchy–Schwarz over the slabs
  have hZcard : (Z.card : ℝ) * h ≤ 7 := by
    have h0 : 0 ≤ ⌈1 / h⌉ + 1 := by
      have := Int.ceil_nonneg (show (0 : ℝ) ≤ 1 / h by positivity)
      omega
    have e1 : (Z.card : ℤ) = 2 * (⌈1 / h⌉ + 1) + 1 := by
      rw [hZ, Int.card_Icc, Int.toNat_of_nonneg (by omega)]; ring
    have hc : (Z.card : ℝ) = 2 * ((⌈1 / h⌉ : ℝ) + 1) + 1 := by
      have e2 : ((Z.card : ℤ) : ℝ) = ((2 * (⌈1 / h⌉ + 1) + 1 : ℤ) : ℝ) := by rw [e1]
      push_cast at e2; linarith
    rw [hc]
    have h1 : (⌈1 / h⌉ : ℝ) < 1 / h + 1 := Int.ceil_lt_add_one _
    have h2 : (2 * ((⌈1 / h⌉ : ℝ) + 1) + 1) * h ≤ (2 * (1 / h + 1 + 1) + 1) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    have h3 : (2 * (1 / h + 1 + 1) + 1) * h = 2 + 5 * h := by field_simp; ring
    linarith
  have hCS : Mt ^ 2 ≤ Z.card * (1664 * h * τ ^ 2) * ∑ z ∈ Z, (N z : ℝ) * μ z := by
    rw [hMt_eq]
    calc (∑ z ∈ Z, μ z) ^ 2 ≤ Z.card * ∑ z ∈ Z, μ z ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ Z.card * ∑ z ∈ Z, (1664 * h * τ ^ 2) * ((N z : ℝ) * μ z) := by
          gcongr with z hz
          have hμ0 : 0 ≤ μ z := Finset.sum_nonneg fun q _ => ha0 q z
          nlinarith [hμN z]
      _ = Z.card * (1664 * h * τ ^ 2) * ∑ z ∈ Z, (N z : ℝ) * μ z := by
          rw [← Finset.mul_sum]; ring
  -- an average shading
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set S : ℝ := ∑ z ∈ Z, (N z : ℝ) * μ z with hS
  have hSlow : τ ^ ε * τ ^ ε * m * τ ^ 2 / 11648 * m ≤ S := by
    have hτ2 : 0 < 11648 * τ ^ 2 := by positivity
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun z _ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun q _ => ha0 q z)
    have h1 : Mt ^ 2 ≤ 11648 * τ ^ 2 * S := by
      calc Mt ^ 2 ≤ Z.card * (1664 * h * τ ^ 2) * S := hCS
        _ = (Z.card * h) * (1664 * τ ^ 2) * S := by ring
        _ ≤ 7 * (1664 * τ ^ 2) * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZcard (by positivity)) hS0
        _ = 11648 * τ ^ 2 * S := by ring
    have h2 : (τ ^ ε * m * τ ^ 2) ^ 2 ≤ Mt ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMlow 2
    have h3 : τ ^ ε * τ ^ ε * m * τ ^ 2 / 11648 * m * (11648 * τ ^ 2) =
        (τ ^ ε * m * τ ^ 2) ^ 2 := by field_simp
    have h4 : τ ^ ε * τ ^ ε * m * τ ^ 2 / 11648 * m * (11648 * τ ^ 2) ≤
        S * (11648 * τ ^ 2) := by
      rw [h3]; linarith only [h2, h1]
    exact le_of_mul_le_mul_right h4 hτ2
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
  have hle : ∑ q0 : Fin m, τ ^ ε * τ ^ ε * m * τ ^ 2 / 11648 ≤
      ∑ q0, ∑ q, (volume (Y q ∩ slabsOf w h (Y q0))).toReal := by
    rw [hdouble, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  obtain ⟨q0, -, hq0⟩ := Finset.exists_le_of_sum_le hne hle
  exact ⟨q0, hq0⟩

/-- Pigeonhole over thick slabs: some slab of height `H ≤ 1` carries a fraction
`H / 7` of the total mass. -/
theorem thick_slab_selection {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) {m : ℕ}
    {Y : Fin m → Set Space} (hYm : ∀ q, MeasurableSet (Y q)) (hYb : ∀ q, Y q ⊆ ball 0 1)
    {w : Space} (hw : ‖w‖ = 1) :
    ∃ k : ℤ, H / 7 * ∑ q, (volume (Y q)).toReal ≤
      ∑ q, (volume (Y q ∩ slab w H k)).toReal := by
  classical
  set Z := Finset.Icc (-(⌈1 / H⌉ + 1)) (⌈1 / H⌉ + 1) with hZ
  have hYfin : ∀ q (A : Set Space), volume (Y q ∩ A) ≠ ⊤ := fun q A =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (inter_subset_left.trans (hYb q)))
  have hdec : ∀ q, (volume (Y q)).toReal = ∑ k ∈ Z, (volume (Y q ∩ slab w H k)).toReal := by
    intro q
    rw [volume_eq_sum_slab hw hH (hYm q) (hYb q), ENNReal.toReal_sum (fun k _ => hYfin q _)]
  have hsum : ∑ q, (volume (Y q)).toReal =
      ∑ k ∈ Z, ∑ q, (volume (Y q ∩ slab w H k)).toReal := by
    simp only [hdec]
    exact Finset.sum_comm
  have hZne : Z.Nonempty := ⟨0, by
    rw [hZ, Finset.mem_Icc]
    have := Int.ceil_nonneg (show (0 : ℝ) ≤ 1 / H by positivity)
    constructor <;> omega⟩
  have hZcard : (Z.card : ℝ) * H ≤ 7 := by
    have h0 : 0 ≤ ⌈1 / H⌉ + 1 := by
      have := Int.ceil_nonneg (show (0 : ℝ) ≤ 1 / H by positivity)
      omega
    have e1 : (Z.card : ℤ) = 2 * (⌈1 / H⌉ + 1) + 1 := by
      rw [hZ, Int.card_Icc, Int.toNat_of_nonneg (by omega)]; ring
    have hc : (Z.card : ℝ) = 2 * ((⌈1 / H⌉ : ℝ) + 1) + 1 := by
      have e2 : ((Z.card : ℤ) : ℝ) = ((2 * (⌈1 / H⌉ + 1) + 1 : ℤ) : ℝ) := by rw [e1]
      push_cast at e2; linarith
    rw [hc]
    have h1 : (⌈1 / H⌉ : ℝ) < 1 / H + 1 := Int.ceil_lt_add_one _
    have h2 : (2 * ((⌈1 / H⌉ : ℝ) + 1) + 1) * H ≤ (2 * (1 / H + 1 + 1) + 1) * H :=
      mul_le_mul_of_nonneg_right (by linarith) hH.le
    have h3 : (2 * (1 / H + 1 + 1) + 1) * H = 2 + 5 * H := by field_simp; ring
    linarith
  have hM0 : 0 ≤ ∑ q, (volume (Y q)).toReal := Finset.sum_nonneg fun q _ => ENNReal.toReal_nonneg
  have hle : ∑ k ∈ Z, H / 7 * ∑ q, (volume (Y q)).toReal ≤
      ∑ k ∈ Z, ∑ q, (volume (Y q ∩ slab w H k)).toReal := by
    rw [← hsum, Finset.sum_const, nsmul_eq_mul]
    have : (Z.card : ℝ) * (H / 7) ≤ 1 := by linarith
    calc (Z.card : ℝ) * (H / 7 * ∑ q, (volume (Y q)).toReal)
        = ((Z.card : ℝ) * (H / 7)) * ∑ q, (volume (Y q)).toReal := by ring
      _ ≤ 1 * ∑ q, (volume (Y q)).toReal := mul_le_mul_of_nonneg_right this hM0
      _ = _ := one_mul _
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le hZne hle
  exact ⟨k, hk⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
