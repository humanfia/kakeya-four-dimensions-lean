-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_prism_fan_avoidance.Trim.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_prism_fan_avoidance.Defs

/-!
# Uniform trimming of selected prisms

Given stage-one prism data `D` and a set `J` of prisms, each of which meets the other selected
prisms of its coarse tube in a small part of its box (`hown`), remove from every selected piece
the other selected boxes of its coarse tube.  By the multiplicity cap, the trimmed pieces keep
three quarters of their incidence mass and of their union density, and the trimmed family has
cross-prism avoidance (`trim_selected`).

The reindexing of `J` by `Fin J.card` (with `rIdx`, `rIdx_injective`, `rIdx_mem` and
`sum_enumerate`) follows x0570's `PrismData.restrict` (o198 branch x0570,
`WangZahlLot/Obl/wz_move_two_prism_grains_transfer/PrismRestriction.lean`).
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_prism_fan_avoidance

open Set MeasureTheory

/-- The prisms `P` are measurable (they are closed). -/
theorem measurableSet_P (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) : MeasurableSet (P a b c z e) :=
  (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_isClosed a b c z e).measurableSet

/-- The volume of a prism `P`. -/
theorem volume_P {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : V)
    (e : V ≃ₗᵢ[ℝ] V) : volume (P a b c z e) = ENNReal.ofReal (a * b * c) :=
  WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha hb hc z e

/-- Multiplicity bound: if every point lies in at most `B` of the measurable sets `A i`, then
the sets `A i ∩ E` have total measure at most `B · ν E`. -/
theorem sum_measure_inter_le_of_ncard_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {n : ℕ} {A : Fin n → Set α} (hA : ∀ i, MeasurableSet (A i)) {B : ℝ}
    (hB : ∀ p, (({i | p ∈ A i} : Set (Fin n)).ncard : ℝ) ≤ B) {E : Set α}
    (hE : MeasurableSet E) :
    ∑ i, ν (A i ∩ E) ≤ ENNReal.ofReal B * ν E := by
  classical
  have h1 : ∀ i, ν (A i ∩ E) = ∫⁻ p in E, (A i).indicator 1 p ∂ν := by
    intro i
    rw [lintegral_indicator_one (hA i), Measure.restrict_apply (hA i)]
  simp_rw [h1]
  rw [← lintegral_finsetSum _ (fun i _ => measurable_one.indicator (hA i))]
  calc ∫⁻ p in E, ∑ i, (A i).indicator 1 p ∂ν ≤ ∫⁻ _ in E, ENNReal.ofReal B ∂ν := by
        refine lintegral_mono fun p => ?_
        have hsum : ∑ i, (A i).indicator (1 : α → ENNReal) p =
            ((Finset.univ.filter fun i => p ∈ A i).card : ENNReal) := by
          simp only [Set.indicator_apply, Pi.one_apply]
          exact Finset.sum_boole _ _
        have hcard : (({i | p ∈ A i} : Set (Fin n)).ncard : ℝ) =
            ((Finset.univ.filter fun i => p ∈ A i).card : ℝ) := by
          rw [← Set.ncard_coe_finset]
          congr 2
          ext i
          simp
        rw [hsum, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by rw [← hcard]; exact hB p)
    _ = ENNReal.ofReal B * ν E := setLIntegral_const _ _

/-- If `a` (finite) is at most a quarter of itself plus `b`, then three quarters of `a` are at
most `b`. -/
theorem three_quarters_le {a b : ENNReal} (ha : a ≠ ⊤)
    (h : a ≤ ENNReal.ofReal (1 / 4) * a + b) : ENNReal.ofReal (3 / 4) * a ≤ b := by
  have h1 : ENNReal.ofReal (1 / 4) * a + ENNReal.ofReal (3 / 4) * a = a := by
    rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [← ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha), h1]
  exact h

/-- Shrinking the power of `δ` by the factor three quarters. -/
theorem ofReal_mul_le_three_quarters {x y : ℝ} (m : ENNReal) (hxy : x ≤ 3 / 4 * y) :
    ENNReal.ofReal x * m ≤ ENNReal.ofReal (3 / 4) * (ENNReal.ofReal y * m) := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  gcongr

/-- The key estimates of the trimming, for one prism `j` and the set `S` of prisms whose boxes
are removed from its pieces: three quarters of the incidence mass and of the union density
survive. -/
theorem trim_key {ω ζ δ h ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (D : NData ω ζ δ h ρ c n x v Y) (j : Fin D.L) (S : Finset (Fin D.L))
    (hS : ∑ j' ∈ S, (μ (P D.a (ρ * c) c (D.z j) (D.e j) ∩
        P D.a (ρ * c) c (D.z j') (D.e j'))).toReal ≤ δ ^ h / 4 * (D.a * (ρ * c) * c)) :
    ENNReal.ofReal (3 / 4) * ∑ i, volume (D.W i j) ≤
        ∑ i, volume (D.W i j \ ⋃ j' ∈ S, P D.a (ρ * c) c (D.z j') (D.e j')) ∧
      ENNReal.ofReal (3 / 4) *
          (ENNReal.ofReal (δ ^ h) * volume (P D.a (ρ * c) c (D.z j) (D.e j))) ≤
        volume (⋃ i, D.W i j \ ⋃ j' ∈ S, P D.a (ρ * c) c (D.z j') (D.e j')) := by
  set U := P D.a (ρ * c) c (D.z j) (D.e j) with hU
  set Ex := ⋃ j' ∈ S, P D.a (ρ * c) c (D.z j') (D.e j') with hEx
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hUvol : volume U = ENNReal.ofReal (D.a * (ρ * c) * c) := volume_P ha.le hrc.le hc.le _ _
  have hUfin : volume U ≠ ⊤ := by rw [hUvol]; exact ENNReal.ofReal_ne_top
  have hExm : MeasurableSet Ex :=
    Finset.measurableSet_biUnion S (fun j' _ => measurableSet_P _ _ _ _ _)
  have hEm : MeasurableSet (U ∩ Ex) := (measurableSet_P _ _ _ _ _).inter hExm
  have hhpos : 0 ≤ δ ^ h := Real.rpow_nonneg hδ.le h
  -- the removed part of `U` is small
  have hE : volume (U ∩ Ex) ≤
      ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h) * volume U) := by
    calc volume (U ∩ Ex) = volume (⋃ j' ∈ S, U ∩ P D.a (ρ * c) c (D.z j') (D.e j')) := by
          rw [hEx, Set.inter_iUnion₂]
      _ ≤ ∑ j' ∈ S, volume (U ∩ P D.a (ρ * c) c (D.z j') (D.e j')) :=
          measure_biUnion_finset_le S _
      _ = ENNReal.ofReal (∑ j' ∈ S, (volume (U ∩ P D.a (ρ * c) c (D.z j') (D.e j'))).toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [ENNReal.ofReal_toReal]
          exact ne_top_of_le_ne_top hUfin (measure_mono inter_subset_left)
      _ ≤ ENNReal.ofReal (δ ^ h / 4 * (D.a * (ρ * c) * c)) := ENNReal.ofReal_le_ofReal hS
      _ = ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h) * volume U) := by
          rw [hUvol, ← ENNReal.ofReal_mul hhpos, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  -- each piece lies in `U`
  have hWU : ∀ i, D.W i j ⊆ U := fun i => (D.pieces i j).2.1.trans inter_subset_right
  have hWfin : ∀ i, volume (D.W i j) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top hUfin (measure_mono (hWU i))
  refine ⟨?_, ?_⟩
  · -- incidence mass
    have hB : 0 ≤ D.B j := (D.cap j).1.le
    have hcap : ENNReal.ofReal (δ ^ h * D.B j) * volume U ≤ ∑ i, volume (D.W i j) :=
      (D.cap j).2.2
    have hmult : ∑ i, volume (D.W i j ∩ (U ∩ Ex)) ≤ ENNReal.ofReal (D.B j) * volume (U ∩ Ex) :=
      sum_measure_inter_le_of_ncard_le volume (fun i => (D.pieces i j).1) (D.cap j).2.1 hEm
    have hsplit : ∑ i, volume (D.W i j) =
        ∑ i, volume (D.W i j ∩ (U ∩ Ex)) + ∑ i, volume (D.W i j \ Ex) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Set.inter_assoc, Set.inter_eq_left.mpr (hWU i), measure_inter_add_sdiff _ hExm]
    have hmult' : ∑ i, volume (D.W i j ∩ (U ∩ Ex)) ≤
        ENNReal.ofReal (1 / 4) * ∑ i, volume (D.W i j) := by
      calc ∑ i, volume (D.W i j ∩ (U ∩ Ex)) ≤ ENNReal.ofReal (D.B j) * volume (U ∩ Ex) := hmult
        _ ≤ ENNReal.ofReal (D.B j) *
            (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h) * volume U)) := by gcongr
        _ = ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h * D.B j) * volume U) := by
            rw [ENNReal.ofReal_mul hhpos]; ring
        _ ≤ ENNReal.ofReal (1 / 4) * ∑ i, volume (D.W i j) := by gcongr
    apply three_quarters_le (ENNReal.sum_ne_top.mpr fun i _ => hWfin i)
    calc ∑ i, volume (D.W i j) =
        ∑ i, volume (D.W i j ∩ (U ∩ Ex)) + ∑ i, volume (D.W i j \ Ex) := hsplit
      _ ≤ ENNReal.ofReal (1 / 4) * ∑ i, volume (D.W i j) + ∑ i, volume (D.W i j \ Ex) := by
          gcongr
  · -- union density
    have hdense : ENNReal.ofReal (δ ^ h) * volume U ≤ volume (⋃ i, D.W i j) := D.dense j
    have hsub : (⋃ i, D.W i j) ⊆ (⋃ i, D.W i j \ Ex) ∪ (U ∩ Ex) := by
      intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      by_cases hpE : p ∈ Ex
      · exact Or.inr ⟨hWU i hi, hpE⟩
      · exact Or.inl (mem_iUnion.mpr ⟨i, hi, hpE⟩)
    apply three_quarters_le (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hUfin)
    calc ENNReal.ofReal (δ ^ h) * volume U ≤ volume (⋃ i, D.W i j) := hdense
      _ ≤ volume ((⋃ i, D.W i j \ Ex) ∪ (U ∩ Ex)) := measure_mono hsub
      _ ≤ volume (⋃ i, D.W i j \ Ex) + volume (U ∩ Ex) := measure_union_le _ _
      _ ≤ volume (⋃ i, D.W i j \ Ex) +
          ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h) * volume U) := by gcongr
      _ = ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (δ ^ h) * volume U) +
          volume (⋃ i, D.W i j \ Ex) := add_comm _ _

/-- Uniform trimming: keep the prisms of `J`, and remove from each kept piece the other kept boxes
of its coarse tube.  When these overlaps are small (`hown`) and the kept prisms carry enough mass
(`hmass`), the result is prism data at the error `h'` with cross-prism avoidance. -/
theorem trim_selected {ω ζ δ h h' ρ c : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh' : h ≤ h')
    (D : NData ω ζ δ h ρ c n x v Y) (J : Finset (Fin D.L))
    (hown : ∀ j ∈ J, ∑ j' ∈ J.filter (fun j' => j' ≠ j ∧ D.γ j' = D.γ j),
        (μ (P D.a (ρ * c) c (D.z j) (D.e j) ∩ P D.a (ρ * c) c (D.z j') (D.e j'))).toReal ≤
      δ ^ h / 4 * (D.a * (ρ * c) * c))
    (hmass : O (δ ^ h') * ∑ i, μ (Y i) ≤ O (3 / 4) * ∑ j ∈ J, ∑ i, μ (D.W i j))
    (hh' : δ ^ h' ≤ 3 / 4 * δ ^ h) :
    ∃ D' : NData ω ζ δ h' ρ c n x v Y, D'.Avoid := by
  let fj := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx J
  have hfj : Function.Injective fj := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective J
  have hfjJ : ∀ k, fj k ∈ J := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem J
  let S : Fin D.L → Finset (Fin D.L) := fun j => J.filter (fun j' => j' ≠ j ∧ D.γ j' = D.γ j)
  let Ex : Fin D.L → Set V := fun j => ⋃ j' ∈ S j, P D.a (ρ * c) c (D.z j') (D.e j')
  have hExm : ∀ j, MeasurableSet (Ex j) := fun j =>
    Finset.measurableSet_biUnion (S j) (fun j' _ => measurableSet_P _ _ _ _ _)
  have key := fun k => trim_key hδ D (fj k) (S (fj k)) (hown (fj k) (hfjJ k))
  have ha : 0 < D.a := hδ.trans_le D.lower
  have hrc : 0 < ρ * c := ha.trans_le D.middle
  have hc : 0 < c := hrc.trans_le D.upper
  have hρ : 0 < ρ := pos_of_mul_pos_left hrc hc.le
  refine ⟨{
    a := D.a
    L := J.card
    N := D.N
    z := D.z ∘ fj
    e := D.e ∘ fj
    W := fun i k => D.W i (fj k) \ Ex (fj k)
    y := D.y
    w := D.w
    γ := D.γ ∘ fj
    B := D.B ∘ fj
    lower := D.lower
    middle := D.middle
    upper := D.upper
    length := D.length
    pieces := fun i k => ⟨(D.pieces i (fj k)).1.diff (hExm (fj k)),
      sdiff_subset.trans (D.pieces i (fj k)).2.1,
      fun k' hne => ((D.pieces i (fj k)).2.2 (fj k') (fun he => hne (hfj he))).mono
        sdiff_subset sdiff_subset⟩
    mass := ?mass
    dense := ?dense
    crossing := fun i k hne => D.crossing i (fj k) (hne.mono sdiff_subset)
    broad := ?broad
    distinct := D.distinct
    unit := D.unit
    geometry := fun k => D.geometry (fj k)
    disjoint := fun k k' hne he => (D.disjoint (fj k) (fj k') (fun hh => hne (hfj hh)) he).mono
      (iUnion_mono fun i => sdiff_subset) (iUnion_mono fun i => sdiff_subset)
    cap := ?cap }, ?avoid⟩
  case mass =>
    show ENNReal.ofReal (δ ^ h') * ∑ i, volume (Y i) ≤
      ∑ i, ∑ k, volume (D.W i (fj k) \ Ex (fj k))
    rw [Finset.sum_comm]
    calc ENNReal.ofReal (δ ^ h') * ∑ i, volume (Y i) ≤
        ENNReal.ofReal (3 / 4) * ∑ j ∈ J, ∑ i, volume (D.W i j) := hmass
      _ = ∑ k, ENNReal.ofReal (3 / 4) * ∑ i, volume (D.W i (fj k)) := by
          rw [Finset.mul_sum]
          exact (WangZahlLot.Obl.wz_regular_transverse_affine_cells.sum_enumerate J
            (fun j => ENNReal.ofReal (3 / 4) * ∑ i, volume (D.W i j))).symm
      _ ≤ ∑ k, ∑ i, volume (D.W i (fj k) \ Ex (fj k)) :=
          Finset.sum_le_sum fun k _ => (key k).1
  case dense =>
    intro k
    show ENNReal.ofReal (δ ^ h') * volume (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k))) ≤
      volume (⋃ i, D.W i (fj k) \ Ex (fj k))
    exact (ofReal_mul_le_three_quarters _ hh').trans (key k).2
  case broad =>
    intro k p u r hu hdr hrρ
    show q n {i | p ∈ D.W i (fj k) \ Ex (fj k) ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h') * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ D.W i (fj k) \ Ex (fj k)}
    by_cases hp : p ∈ Ex (fj k)
    · have h1 : {i | p ∈ D.W i (fj k) \ Ex (fj k) ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} = ∅ := by
        ext i; simp [hp]
      have h2 : {i | p ∈ D.W i (fj k) \ Ex (fj k)} = ∅ := by
        ext i; simp [hp]
      rw [h1, h2]
      simp [q]
    · have h1 : {i | p ∈ D.W i (fj k) \ Ex (fj k) ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} =
          {i | p ∈ D.W i (fj k) ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
        ext i; simp [hp]
      have h2 : {i | p ∈ D.W i (fj k) \ Ex (fj k)} = {i | p ∈ D.W i (fj k)} := by
        ext i; simp [hp]
      rw [h1, h2]
      apply (D.broad (fj k) p u r hu hdr hrρ).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hhh'))
          (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _)) (Nat.cast_nonneg _)
  case cap =>
    intro k
    refine ⟨(D.cap (fj k)).1, fun p => ?_, ?_⟩
    · show q n {i | p ∈ D.W i (fj k) \ Ex (fj k)} ≤ D.B (fj k)
      refine le_trans ?_ ((D.cap (fj k)).2.1 p)
      exact Nat.cast_le.mpr (Set.ncard_le_ncard (fun i hi => hi.1) (Set.toFinite _))
    · show ENNReal.ofReal (δ ^ h' * D.B (fj k)) *
          volume (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k))) ≤
        ∑ i, volume (D.W i (fj k) \ Ex (fj k))
      have hB : 0 ≤ D.B (fj k) := (D.cap (fj k)).1.le
      have hcap : ENNReal.ofReal (δ ^ h * D.B (fj k)) *
          volume (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k))) ≤ ∑ i, volume (D.W i (fj k)) :=
        (D.cap (fj k)).2.2
      calc ENNReal.ofReal (δ ^ h' * D.B (fj k)) *
            volume (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k))) ≤
          ENNReal.ofReal (3 / 4) * (ENNReal.ofReal (δ ^ h * D.B (fj k)) *
            volume (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k)))) := by
            apply ofReal_mul_le_three_quarters
            calc δ ^ h' * D.B (fj k) ≤ 3 / 4 * δ ^ h * D.B (fj k) :=
                  mul_le_mul_of_nonneg_right hh' hB
              _ = 3 / 4 * (δ ^ h * D.B (fj k)) := by ring
        _ ≤ ENNReal.ofReal (3 / 4) * ∑ i, volume (D.W i (fj k)) := by gcongr
        _ ≤ ∑ i, volume (D.W i (fj k) \ Ex (fj k)) := (key k).1
  case avoid =>
    intro i k k' hne hγ _
    show Disjoint (D.W i (fj k') \ Ex (fj k')) (P D.a (ρ * c) c (D.z (fj k)) (D.e (fj k)))
    refine Set.disjoint_sdiff_left.mono_right ?_
    intro p hp
    exact mem_iUnion₂.mpr ⟨fj k, Finset.mem_filter.mpr ⟨hfjJ k, fun hh => hne (hfj hh), hγ⟩, hp⟩

end WangZahlLot.Obl.wz_move_two_prism_fan_avoidance
