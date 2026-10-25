-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PacketCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RelativeCore
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PacketLocal
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/-! Uniform tube mass in broad local packets, with an aggregate mass budget. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal
open wz_measurable_angular_selection (pd)

/-- Prune a finite family of broad local packets. Row costs are paid only once,
and each packet keeps its own pointwise broadness with a factor-four loss. -/
theorem broad_packet_core {κ : Type*} [Fintype κ] {n : ℕ}
    {d θ β : ℝ} (hd : 0 < d) (hθ : 0 < θ)
    (v : Fin n → V) (Y : κ → Fin n → Set V)
    (hYm : ∀ k i, MeasurableSet (Y k i)) (hfin : ∀ k i, volume (Y k i) ≠ ∞)
    (hBr : ∀ k p u r, d ≤ r →
      q n {i | p ∈ Y k i ∧ pd (v i) u ≤ r} ≤
        2 * (r/θ)^β * q n {i | p ∈ Y k i})
    (cost : κ → Fin n → ENNReal)
    (hbudget : (∑ k, ∑ i, cost k i) ≤ (1/4 : ENNReal) * ∑ k, ∑ i, volume (Y k i)) :
    ∃ Z : κ → Fin n → Set V,
      (∀ k i, MeasurableSet (Z k i) ∧ Z k i ⊆ Y k i) ∧
      (1/2 : ENNReal) * (∑ k, ∑ i, volume (Y k i)) ≤ ∑ k, ∑ i, volume (Z k i) ∧
      (∀ k i, (Z k i).Nonempty → cost k i ≤ volume (Z k i)) ∧
      ∀ k p u r, d ≤ r →
        q n {i | p ∈ Z k i ∧ pd (v i) u ≤ r} ≤
          8 * (r/θ)^β * q n {i | p ∈ Z k i} := by
  obtain ⟨Z, hZ, hmass, hdense, hcount⟩ :=
    relative_shading_core_family volume Y hYm hfin cost (1/4)
  have hquarter : ENNReal.ofReal (1/4 : ℝ) = (1/4 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hquarters : (1/4 : ENNReal) + 1/4 = 1/2 := by
    rw [← hquarter, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (1/4 : ℝ) + 1/4 = 1/2 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  refine ⟨Z, hZ, ?_, hdense, ?_⟩
  · apply wz_clustered_cover_volume_gain.half_mass_after_loss
      (ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.sum_ne_top.mpr (fun i _ => hfin k i)))
      (by simpa only [add_assoc] using hmass)
    calc
      _ ≤ (1/4 : ENNReal) * (∑ k, ∑ i, volume (Y k i)) +
          (1/4 : ENNReal) * ∑ k, ∑ i, volume (Y k i) := add_le_add hbudget le_rfl
      _ = _ := by rw [← add_mul, hquarters]
  · intro k p u r hr
    by_cases hp : p ∈ ⋃ i, Z k i
    · have hc := ENNReal.toReal_mono (by simp) (hcount k p hp)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hc
      have hc' : q n {i | p ∈ Y k i} ≤ 4 * q n {i | p ∈ Z k i} := by
        change ({i | p ∈ Y k i}.ncard : ℝ) ≤ 4 * ({i | p ∈ Z k i}.ncard : ℝ)
        linarith
      have hcap : q n {i | p ∈ Z k i ∧ pd (v i) u ≤ r} ≤
          q n {i | p ∈ Y k i ∧ pd (v i) u ≤ r} := by
        exact_mod_cast Set.ncard_le_ncard (show
          {i | p ∈ Z k i ∧ pd (v i) u ≤ r} ⊆
            {i | p ∈ Y k i ∧ pd (v i) u ≤ r} from
          fun i hi => ⟨(hZ k i).2 hi.1, hi.2⟩)
      calc
        _ ≤ 2 * (r/θ)^β * q n {i | p ∈ Y k i} := hcap.trans (hBr k p u r hr)
        _ ≤ 2 * (r/θ)^β * (4 * q n {i | p ∈ Z k i}) :=
          mul_le_mul_of_nonneg_left hc' (by have : 0 < r := hd.trans_le hr; positivity)
        _ = _ := by ring
    · have he : {i | p ∈ Z k i ∧ pd (v i) u ≤ r} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hp (mem_iUnion.mpr ⟨i, hi.1⟩)
      change (Set.ncard _ : ℝ) ≤ _
      rw [he, Set.ncard_empty, Nat.cast_zero]
      have : 0 < r := hd.trans_le hr
      positivity

/-- Broadness with coefficient strictly below one forces a transverse partner
at every occupied point. -/
theorem transverse_partner_of_broad {n : ℕ} {v : Fin n → V} {Y : Fin n → Set V}
    {p u : V} {r B : ℝ} (hB : B < 1)
    (hBr : q n {i | p ∈ Y i ∧ pd (v i) u ≤ r} ≤ B * q n {i | p ∈ Y i})
    (hp : p ∈ ⋃ i, Y i) : ∃ i, p ∈ Y i ∧ r < pd (v i) u := by
  classical
  by_contra hn
  have he : {i | p ∈ Y i ∧ pd (v i) u ≤ r} = {i | p ∈ Y i} := by
    ext i
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact ⟨hi, le_of_not_gt (fun hh => hn ⟨i, hi, hh⟩)⟩
  have hpos : 0 < q n {i | p ∈ Y i} := by
    change 0 < ({i | p ∈ Y i}.ncard : ℝ)
    apply Nat.cast_pos.mpr
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨i, hi⟩
  rw [he] at hBr
  nlinarith


/-- A common spatial restriction preserves a pointwise cap inequality. -/
theorem broad_common_cut {n : ℕ} {v : Fin n → V} {Y : Fin n → Set V}
    (Q : Set V) {p u : V} {r B : ℝ} (hB : 0 ≤ B)
    (hBr : q n {i | p ∈ Y i ∧ pd (v i) u ≤ r} ≤ B*q n {i | p ∈ Y i}) :
    q n {i | p ∈ Y i ∩ Q ∧ pd (v i) u ≤ r} ≤
      B*q n {i | p ∈ Y i ∩ Q} := by
  by_cases hp : p ∈ Q
  · simpa only [Set.mem_inter_iff, hp, and_true] using hBr
  · simp [hp, q, wz_move_two_long_grains_gain.q]

/-- Changing the normalizing angular scale has an explicit multiplicative cost. -/
theorem broad_scale_change {n : ℕ} {v : Fin n → V} {Y : Fin n → Set V}
    {p u : V} {r θ ρ β B C : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hρ : 0 < ρ)
    (hbudget : B*(ρ/θ)^β ≤ C)
    (hBr : q n {i | p ∈ Y i ∧ pd (v i) u ≤ r} ≤
      B*(r/θ)^β*q n {i | p ∈ Y i}) :
    q n {i | p ∈ Y i ∧ pd (v i) u ≤ r} ≤
      C*(r/ρ)^β*q n {i | p ∈ Y i} := by
  have he : (r/θ)^β = (ρ/θ)^β*(r/ρ)^β := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [he, ← mul_assoc] at hBr
  refine hBr.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbudget (by positivity)) (by positivity)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
