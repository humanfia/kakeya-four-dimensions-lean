-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.FixedPacket.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.DenseSelection

/-! A packet's directional bounds are properties of its fixed tube set. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal
open wz_broad_grains_initialization (PacketRefinement)
open wz_measurable_angular_selection (pd)

/-- At one occupied point an angular refinement yields a fixed nonempty set
of tubes whose directional distribution is broad, independently of later
choices of shadings. -/
theorem exists_fixed_packet {n : ℕ} {β d θ : ℝ} {v : Fin n → V}
    {Y Z : Fin n → Set V} {F : V → Finset (Finset (Fin n))}
    {j : V → Finset (Fin n) → Fin n}
    (hR : PacketRefinement β d θ v Y Z F j) (hv : ∀ i, ‖v i‖ = 1)
    (hZ : ∃ i, (Z i).Nonempty) :
    ∃ (p u : V) (S : Finset (Fin n)), ‖u‖ = 1 ∧ S.Nonempty ∧
      (∀ i ∈ S, p ∈ Z i) ∧ (∀ i ∈ S, pd (v i) u ≤ 2*θ) ∧
      ∀ u' r, d ≤ r → ((S.filter (fun i => pd (v i) u' ≤ r)).card : ℝ) ≤
        2*(r/θ)^β*(S.card : ℝ) := by
  obtain ⟨i, p, hi⟩ := hZ
  have hcover := (hR.2.2.2 p).2.1
  have hiU : i ∈ (F p).biUnion id := by
    change i ∈ ((F p).biUnion id : Set (Fin n))
    rw [hcover]
    exact hi
  obtain ⟨S, hSF, hiS⟩ := Finset.mem_biUnion.mp hiU
  have hS := (hR.2.2.2 p).2.2 S hSF
  refine ⟨p, v (j p S), S, hv _, hS.1, ?_, hS.2.1, hS.2.2.2⟩
  intro i' hi'
  change i' ∈ {i | p ∈ Z i}
  rw [← hcover]
  exact Finset.mem_biUnion.mpr ⟨S, hSF, hi'⟩

/-- Narrow input has a fixed packet at one of its finite dyadic scales. -/
theorem DensePrismInput.Narrow.fixed_packet {ω d lam a b L s β r₀ t : ℝ}
    {n N K : ℕ} {x v : Fin n → V} {y w : Fin N → V} {Y : Fin n → Set V}
    {B : DensePrismInput ω d lam a b L s x v y w Y}
    (hN : B.Narrow β r₀ t K) (hd : 0 < d) (ht : 0 < t)
    (hv : ∀ i, ‖v i‖ = 1) :
    ∃ (k : Fin (K+1)) (p u : V) (S : Finset (Fin n)), ‖u‖ = 1 ∧ S.Nonempty ∧
      d ≤ (1/2 : ℝ)^(k : ℕ) ∧ (1/2 : ℝ)^(k : ℕ) ≤ 1 ∧
      r₀ < (1/2 : ℝ)^(k : ℕ) ∧ (1/2 : ℝ)^(k : ℕ)*L < d ∧
      (∀ i ∈ S, p ∈ B.shading i) ∧
      (∀ i ∈ S, pd (v i) u ≤ 2*((1/2 : ℝ)^(k : ℕ))) ∧
      ∀ u' r, d ≤ r → ((S.filter (fun i => pd (v i) u' ≤ r)).card : ℝ) ≤
        2*(r/((1/2 : ℝ)^(k : ℕ)))^β*(S.card : ℝ) := by
  obtain ⟨k, Z, F, j, hdθ, hθ1, hθlow, hnarrow, hR, hret⟩ := hN
  have hBmass : 0 < ∑ i, volume (B.shading i) :=
    lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (mul_ne_zero
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hd _)).ne' (B.volume_pos hd).ne')) B.incidence
  have hZmass : 0 < ∑ i, volume (Z i) :=
    lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (mul_ne_zero
      (ENNReal.ofReal_pos.mpr ht).ne' hBmass.ne')) hret
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hZmass
  have hZ : (Z i).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty] at hi
    exact lt_irrefl _ hi
  obtain ⟨p, u, S, hu, hS, hp, hang, hBr⟩ := exists_fixed_packet hR hv ⟨i, hZ⟩
  exact ⟨k, p, u, S, hu, hS, hdθ, hθ1, hθlow, hnarrow,
    fun i hi => (hR.1 i).2 (hp i hi), hang, hBr⟩

/-- Keeping a fixed fraction of a static packet at each occupied point passes
its broadness to arbitrary new shadings on those tubes. -/
theorem broad_of_fixed_packet {n : ℕ} {v : Fin n → V} {W : Fin n → Set V}
    (S : Finset (Fin n)) {d θ ρ β t C B : ℝ}
    (hd : 0 < d) (hθ : 0 < θ) (hρ : 0 < ρ) (ht : 0 < t) (hC : 0 ≤ C)
    (hzero : ∀ i, i ∉ S → W i = ∅)
    (hcount : ∀ p ∈ ⋃ i, W i, t*(S.card : ℝ) ≤ q n {i | p ∈ W i})
    (hcap : ∀ u r, d ≤ r → ((S.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
      C*(r/θ)^β*(S.card : ℝ))
    (hbudget : (C/t)*(ρ/θ)^β ≤ B) :
    ∀ p u r, d ≤ r → q n {i | p ∈ W i ∧ pd (v i) u ≤ r} ≤
      B*(r/ρ)^β*q n {i | p ∈ W i} := by
  classical
  intro p u r hdr
  apply broad_scale_change (hd.trans_le hdr) hθ hρ hbudget
  by_cases hp : p ∈ ⋃ i, W i
  · have hsub : {i | p ∈ W i ∧ pd (v i) u ≤ r} ⊆
        (S.filter (fun i => pd (v i) u ≤ r) : Set (Fin n)) := by
      intro i hi
      have hiS : i ∈ S := by
        by_contra hn
        simpa only [hzero i hn, mem_empty_iff_false] using hi.1
      exact Finset.mem_filter.mpr ⟨hiS, hi.2⟩
    have hmon : q n {i | p ∈ W i ∧ pd (v i) u ≤ r} ≤
        ((S.filter (fun i => pd (v i) u ≤ r)).card : ℝ) := by
      have hh := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset] at hh
      exact_mod_cast hh
    have hSc : (S.card : ℝ) ≤ q n {i | p ∈ W i}/t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hcount p hp)
    calc
      _ ≤ C*(r/θ)^β*(S.card : ℝ) := hmon.trans (hcap u r hdr)
      _ ≤ C*(r/θ)^β*(q n {i | p ∈ W i}/t) :=
        mul_le_mul_of_nonneg_left hSc (mul_nonneg hC (Real.rpow_nonneg (le_of_lt (div_pos (hd.trans_le hdr) hθ)) _))
      _ = (C/t)*(r/θ)^β*q n {i | p ∈ W i} := by ring
  · have hn (i : Fin n) : p ∉ W i := fun hi => hp (mem_iUnion.mpr ⟨i, hi⟩)
    simp [q, wz_move_two_long_grains_gain.q, hn]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
