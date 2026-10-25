-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.ConvexEnlarge
import Submission.WZ.Obl.wz_compact_offset_normalization.Crossing
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

/-!
# An essentially distinct subfamily with regular multiplicity

Tubes of radius `ρ` *conflict* when they overlap in volume more than `ρ² / 2`. Given a finite
family `U` of transverse tubes in the unit ball, take a conflict-free subfamily `S₀ ⊆ U` of
maximal size and assign every tube of `U` to a conflicting member of `S₀` (or to itself). By
the crossing lemma of `wz_compact_offset_normalization`, if a member of `S₀` lies in a convex
set `W` then its whole cluster lies in `W + 5003 (W - W)`.

The essentially distinct tube count bounds `|S₀| ≤ C ρ⁻⁶`, so clusters smaller than
`ρ¹⁰ |U|` contain at most half of `U`. The other clusters have sizes in
`[ρ¹⁰ |U|, |U|]`; a dyadic class of sizes `(μ_b, 2μ_b]` among the `O(log(1/ρ))` classes covers
a proportional part of `U` (`regularize`).
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal Pointwise
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube)
open WangZahlLot.Obl.wz_compact_offset_normalization (crossing extSeg mem_tube_iff)

/-- Two tubes conflict when they overlap in volume more than `ρ² / 2`. -/
def conflict (ρ : ℝ) (x v x' v' : Space) : Prop :=
  ENNReal.ofReal (ρ ^ 2 / 2) < volume (tube ρ x v ∩ tube ρ x' v')

/-- The neighbourhood of the extended axis lies in the difference-body enlargement. -/
theorem thick_extSeg_subset {ρ : ℝ} (hρ : 0 < ρ) {y u : Space} {W : Set Space}
    (hW : Convex ℝ W) (hT : tube ρ y u ⊆ W) :
    thickening (5000 * ρ) (extSeg y u) ⊆ W + (5003 : ℝ) • (W - W) := by
  intro p hp
  obtain ⟨e0, he0, hpe⟩ := mem_thickening_iff.mp hp
  rw [extSeg, segment_eq_image'] at he0
  obtain ⟨θ, hθ, rfl⟩ := he0
  have hy : y ∈ W := hT (self_subset_thickening hρ _ (left_mem_segment ℝ y (y + u)))
  have hyu : y + u ∈ W := hT (self_subset_thickening hρ _ (right_mem_segment ℝ y (y + u)))
  have hsub : Convex ℝ (W - W) := hW.sub hW
  have hu : u ∈ W - W := by have := Set.sub_mem_sub hyu hy; simpa using this
  have hnu : -u ∈ W - W := by have := Set.sub_mem_sub hy hyu; simpa using this
  set l := 5 * θ - 2 with hl
  have hl1 : -1 ≤ l / 3 := by rw [hl]; linarith [hθ.1]
  have hl2 : l / 3 ≤ 1 := by rw [hl]; linarith [hθ.2]
  have hlu : (l / 3) • u ∈ W - W := by
    have := hsub hu hnu (a := (1 + l / 3) / 2) (b := (1 - l / 3) / 2) (by linarith)
      (by linarith) (by ring)
    have he : ((1 + l / 3) / 2) • u + ((1 - l / 3) / 2) • -u = (l / 3) • u := by module
    rwa [he] at this
  set w' := (1 / 5000 : ℝ) • (p - (y - (2 : ℝ) • u + θ • (y + (3 : ℝ) • u - (y - (2 : ℝ) • u))))
    with hw'def
  have hw'norm : ‖w'‖ < ρ := by
    rw [hw'def, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), ← dist_eq_norm]
    linarith
  have hw' : y + w' ∈ W := by
    apply hT
    rw [tube, mem_thickening_iff]
    refine ⟨y, left_mem_segment ℝ y (y + u), ?_⟩
    rwa [dist_eq_norm, add_sub_cancel_left]
  have hw'm : w' ∈ W - W := by have := Set.sub_mem_sub hw' hy; simpa using this
  have hcomb : (3 / 5003 : ℝ) • ((l / 3) • u) + (5000 / 5003 : ℝ) • w' ∈ W - W :=
    hsub hlu hw'm (by norm_num) (by norm_num) (by norm_num)
  refine ⟨y, hy, _, Set.smul_mem_smul_set hcomb, ?_⟩
  rw [hw'def, hl]
  module

open Classical in
/-- **Regularization.** -/
theorem regularize {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 10000) (x v : ι → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, tube ρ (x i) (v i) ⊆ ball 0 1) (U : Finset ι) (hU : U.Nonempty) {C43 : ℝ}
    (hC43 : ∀ (k : ℕ) (x' v' : Fin k → Space), (∀ i, ‖v' i‖ = 1) →
      (∀ i, tube ρ (x' i) (v' i) ⊆ ball 0 1) →
      (∀ i j, i ≠ j → volume (tube ρ (x' i) (v' i) ∩ tube ρ (x' j) (v' j)) ≤
        (1 / 2 : ℝ≥0∞) * volume (tube ρ (x' i) (v' i))) → (k : ℝ) * ρ ^ 6 ≤ C43)
    (hsmall : C43 * ρ ^ 4 ≤ 1 / 2) :
    ∃ S ⊆ U, S.Nonempty ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ conflict ρ (x i) (v i) (x j) (v j)) ∧
      ∃ μb : ℝ, 0 < μb ∧
        (∀ W : Set Space, Convex ℝ W →
          ((S.filter (fun r => tube ρ (x r) (v r) ⊆ W)).card : ℝ) * μb ≤
            ((U.filter (fun q => tube ρ (x q) (v q) ⊆ W + (5003 : ℝ) • (W - W))).card : ℝ)) ∧
        (U.card : ℝ) ≤ 4 * (Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ + 1) * (S.card * μb) := by
  classical
  -- a conflict-free subfamily of maximal size
  set ED : Finset ι → Prop := fun A =>
    ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ conflict ρ (x i) (v i) (x j) (v j) with hED
  have hEDne : (U.powerset.filter ED).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp [hED]⟩⟩
  obtain ⟨S0, hS0mem, hS0max⟩ := Finset.exists_max_image _ Finset.card hEDne
  obtain ⟨hS0U, hS0ED⟩ := Finset.mem_filter.mp hS0mem
  rw [Finset.mem_powerset] at hS0U
  -- every tube outside conflicts with a member
  have hconf : ∀ q ∈ U, q ∉ S0 → ∃ r ∈ S0, conflict ρ (x q) (v q) (x r) (v r) := by
    intro q hq hqS
    by_contra hno
    push Not at hno
    have hins : insert q S0 ∈ U.powerset.filter ED := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hq hS0U), ?_⟩
      intro i hi j hj hij
      rw [Finset.mem_insert] at hi hj
      rcases hi with rfl | hi <;> rcases hj with rfl | hj
      · exact absurd rfl hij
      · exact hno j hj
      · intro hc
        apply hno i hi
        unfold conflict at hc ⊢
        rwa [inter_comm] at hc
      · exact hS0ED i hi j hj hij
    have := hS0max _ hins
    rw [Finset.card_insert_of_notMem hqS] at this
    omega
  -- the assignment to representatives
  let rep : ι → ι := fun q =>
    if hq : q ∈ U ∧ q ∉ S0 then Classical.choose (hconf q hq.1 hq.2) else q
  have hrep : ∀ q ∈ U, rep q ∈ S0 ∧ (rep q = q ∨ conflict ρ (x q) (v q) (x (rep q)) (v (rep q))) := by
    intro q hq
    by_cases hqS : q ∈ S0
    · have : rep q = q := by simp [rep, hqS]
      rw [this]; exact ⟨hqS, Or.inl rfl⟩
    · have hspec := Classical.choose_spec (hconf q hq hqS)
      have : rep q = Classical.choose (hconf q hq hqS) := by simp [rep, hq, hqS]
      rw [this]
      exact ⟨hspec.1, Or.inr hspec.2⟩
  have hrep_self : ∀ r ∈ S0, rep r = r := by
    intro r hr; simp [rep, hr]
  -- cluster sizes
  let μ : ι → ℕ := fun r => (U.filter (fun q => rep q = r)).card
  have hμpos : ∀ r ∈ S0, 1 ≤ μ r := by
    intro r hr
    apply Finset.card_pos.mpr
    exact ⟨r, Finset.mem_filter.mpr ⟨hS0U hr, hrep_self r hr⟩⟩
  have hμsum : ∑ r ∈ S0, μ r = U.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rep) (t := S0) (fun q hq => (hrep q hq).1)]
  have hμle : ∀ r, μ r ≤ U.card := fun r => Finset.card_filter_le _ _
  -- the size of `S₀`
  have hS0card : (S0.card : ℝ) * ρ ^ 6 ≤ C43 := by
    let e := S0.equivFin.symm
    apply hC43 S0.card (fun i => x (e i)) (fun i => v (e i)) (fun i => hv _) (fun i => hT _)
    intro i j hij
    have hne : (e i : ι) ≠ e j := fun h => hij (e.injective (Subtype.ext h))
    have hnc := hS0ED _ (e i).2 _ (e j).2 hne
    unfold conflict at hnc
    push Not at hnc
    refine hnc.trans ?_
    calc ENNReal.ofReal (ρ ^ 2 / 2) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (ρ ^ 2) := by
          rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
      _ ≤ (1 / 2 : ℝ≥0∞) * volume (tube ρ (x (e i)) (v (e i))) := by
          gcongr
          exact WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hρ _ _ (hv _)
  -- small clusters cover at most half
  set θ := ρ ^ (10 : ℕ) * (U.card : ℝ) with hθ
  set large := S0.filter (fun r => θ ≤ (μ r : ℝ)) with hlarge
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hsmallsum : ∑ r ∈ S0.filter (fun r => ¬ θ ≤ (μ r : ℝ)), (μ r : ℝ) ≤ U.card / 2 := by
    calc ∑ r ∈ S0.filter (fun r => ¬ θ ≤ (μ r : ℝ)), (μ r : ℝ)
        ≤ ∑ _r ∈ S0, θ := by
          refine (Finset.sum_le_sum fun r hr => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity))
          have := (Finset.mem_filter.mp hr).2
          push Not at this
          exact this.le
      _ = S0.card * θ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (S0.card * ρ ^ 6) * (ρ ^ 4 * U.card) := by rw [hθ]; ring
      _ ≤ C43 * (ρ ^ 4 * U.card) := by gcongr
      _ = (C43 * ρ ^ 4) * U.card := by ring
      _ ≤ 1 / 2 * U.card := by gcongr
      _ = U.card / 2 := by ring
  have hlargesum : (U.card : ℝ) / 2 ≤ ∑ r ∈ large, (μ r : ℝ) := by
    have h := Finset.sum_filter_add_sum_filter_not S0 (fun r => θ ≤ (μ r : ℝ))
      (fun r => (μ r : ℝ))
    have hs : ∑ r ∈ S0, (μ r : ℝ) = U.card := by exact_mod_cast hμsum
    rw [hs] at h
    linarith
  -- dyadic classes of the large clusters
  set B0 := Nat.log 2 ⌊ρ ^ (-10 : ℝ)⌋₊ with hB0
  let cls : ι → ℕ := fun r => Nat.log 2 ⌊(U.card : ℝ) / μ r⌋₊
  have hρ10 : ρ ^ (-10 : ℝ) = (ρ ^ (10 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hρ.le]; norm_cast
  have hcls_le : ∀ r ∈ large, cls r ≤ B0 := by
    intro r hr
    have h1 : θ ≤ (μ r : ℝ) := (Finset.mem_filter.mp hr).2
    have hμ0 : (0 : ℝ) < μ r := by
      have := hμpos r (Finset.mem_filter.mp hr).1; exact_mod_cast this
    have h2 : (U.card : ℝ) / μ r ≤ ρ ^ (-10 : ℝ) := by
      rw [hρ10, div_le_iff₀ hμ0]
      rw [hθ] at h1
      have hp : 0 < ρ ^ (10 : ℕ) := by positivity
      calc (U.card : ℝ) = (ρ ^ (10 : ℕ))⁻¹ * (ρ ^ (10 : ℕ) * U.card) := by field_simp
        _ ≤ (ρ ^ (10 : ℕ))⁻¹ * μ r := by gcongr
    exact Nat.log_mono_right (Nat.floor_le_floor h2)
  have hpig : ∃ b ∈ Finset.range (B0 + 1),
      (U.card : ℝ) / 2 / (B0 + 1) ≤ ∑ r ∈ large.filter (fun r => cls r = b), (μ r : ℝ) := by
    by_contra hno
    push Not at hno
    have hsum : ∑ r ∈ large, (μ r : ℝ) =
        ∑ b ∈ Finset.range (B0 + 1), ∑ r ∈ large.filter (fun r => cls r = b), (μ r : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to (fun r hr => Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hcls_le r hr))) _).symm
    have hlt : ∑ b ∈ Finset.range (B0 + 1), ∑ r ∈ large.filter (fun r => cls r = b), (μ r : ℝ) <
        ∑ _b ∈ Finset.range (B0 + 1), (U.card : ℝ) / 2 / (B0 + 1) :=
      Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hno
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
    have : ((B0 + 1 : ℕ) : ℝ) * ((U.card : ℝ) / 2 / (B0 + 1)) = U.card / 2 := by
      push_cast; field_simp
    linarith
  obtain ⟨b, -, hb⟩ := hpig
  set S := large.filter (fun r => cls r = b) with hSdef
  have hSS0 : S ⊆ S0 := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  set μb : ℝ := (U.card : ℝ) / 2 ^ (b + 1) with hμbdef
  have hμb : 0 < μb := by positivity
  -- cluster sizes in the class
  have hμrange : ∀ r ∈ S, μb < μ r ∧ (μ r : ℝ) ≤ U.card / 2 ^ b := by
    intro r hr
    have hcl : cls r = b := (Finset.mem_filter.mp hr).2
    have hrS0 := hSS0 hr
    have hμ0 : (0 : ℝ) < μ r := by have := hμpos r hrS0; exact_mod_cast this
    have hy1 : (1 : ℝ) ≤ (U.card : ℝ) / μ r := by
      rw [le_div_iff₀ hμ0, one_mul]; exact_mod_cast hμle r
    have hfl : ⌊(U.card : ℝ) / μ r⌋₊ ≠ 0 := by
      have := Nat.floor_pos.mpr hy1; omega
    constructor
    · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊(U.card : ℝ) / μ r⌋₊
      have h2 : (U.card : ℝ) / μ r < 2 ^ (b + 1) := by
        rw [← hcl]
        have := (Nat.floor_lt (by positivity)).mp (h1.trans_le le_rfl)
        exact_mod_cast this
      rw [hμbdef, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hμ0] at h2
      linarith
    · have h1 := Nat.pow_log_le_self 2 hfl
      have h2 : (2 : ℝ) ^ b ≤ (U.card : ℝ) / μ r := by
        rw [← hcl]
        exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ hμ0] at h2
      linarith
  refine ⟨S, hSS0.trans hS0U, ?_, fun i hi j hj hij => hS0ED i (hSS0 hi) j (hSS0 hj) hij,
    μb, hμb, ?_, ?_⟩
  · -- nonempty
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hb
    have : (0 : ℝ) < (U.card : ℝ) / 2 / (B0 + 1) := by positivity
    linarith
  · -- the count transfer
    intro W hW
    calc ((S.filter (fun r => tube ρ (x r) (v r) ⊆ W)).card : ℝ) * μb
        = ∑ _r ∈ S.filter (fun r => tube ρ (x r) (v r) ⊆ W), μb := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S.filter (fun r => tube ρ (x r) (v r) ⊆ W), (μ r : ℝ) :=
          Finset.sum_le_sum fun r hr => (hμrange r (Finset.mem_filter.mp hr).1).1.le
      _ = ((U.filter (fun q => rep q ∈ S.filter (fun r => tube ρ (x r) (v r) ⊆ W))).card : ℝ) := by
          set S' := S.filter (fun r => tube ρ (x r) (v r) ⊆ W) with hS'
          have hcf : (U.filter (fun q => rep q ∈ S')).card = ∑ r ∈ S',
              ((U.filter (fun q => rep q ∈ S')).filter (fun q => rep q = r)).card :=
            Finset.card_eq_sum_card_fiberwise (fun q hq => (Finset.mem_filter.mp hq).2)
          rw [hcf]
          push_cast
          refine Finset.sum_congr rfl fun r hr => ?_
          have hset : (U.filter (fun q => rep q ∈ S')).filter (fun q => rep q = r) =
              U.filter (fun q => rep q = r) := by
            ext q
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨⟨hq, _⟩, hqr⟩; exact ⟨hq, hqr⟩
            · rintro ⟨hq, hqr⟩; exact ⟨⟨hq, hqr ▸ hr⟩, hqr⟩
          rw [hset]
      _ ≤ ((U.filter (fun q => tube ρ (x q) (v q) ⊆ W + (5003 : ℝ) • (W - W))).card : ℝ) := by
          gcongr with q hq
          intro hrq
          obtain ⟨hrS, hrW⟩ := Finset.mem_filter.mp hrq
          obtain ⟨-, hcase⟩ := hrep q hq
          rcases hcase with heq | hc
          · rw [heq] at hrW
            intro p hp
            exact ⟨p, hrW hp, 0, ⟨0, ⟨p, hrW hp, p, hrW hp, sub_self p⟩, smul_zero _⟩, add_zero p⟩
          · have hc' : ENNReal.ofReal (ρ ^ 2 / 2) <
                volume (tube ρ (x (rep q)) (v (rep q)) ∩ tube ρ (x q) (v q)) := by
              unfold conflict at hc; rwa [inter_comm] at hc
            exact (crossing hρ hρ1 (hv _) (hv _) hc').trans (thick_extSeg_subset hρ hW hrW)
  · -- the size of the class
    have hsumS : (U.card : ℝ) / 2 / (B0 + 1) ≤ S.card * ((U.card : ℝ) / 2 ^ b) := by
      calc (U.card : ℝ) / 2 / (B0 + 1) ≤ ∑ r ∈ S, (μ r : ℝ) := hb
        _ ≤ ∑ _r ∈ S, (U.card : ℝ) / 2 ^ b := Finset.sum_le_sum fun r hr => (hμrange r hr).2
        _ = S.card * ((U.card : ℝ) / 2 ^ b) := by rw [Finset.sum_const, nsmul_eq_mul]
    have he : S.card * ((U.card : ℝ) / 2 ^ b) = 2 * (S.card * μb) := by
      rw [hμbdef, pow_succ]; field_simp
    rw [he] at hsumS
    have hB : (0 : ℝ) < B0 + 1 := by positivity
    rw [div_div, div_le_iff₀ (by positivity)] at hsumS
    nlinarith

end WangZahlLot.Obl.wz_intermediate_twist_normalization
