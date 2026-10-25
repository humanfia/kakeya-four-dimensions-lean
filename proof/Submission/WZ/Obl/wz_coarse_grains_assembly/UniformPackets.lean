-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.UniformPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.RawCoverPackets
import Submission.WZ.Obl.wz_coarse_grains_assembly.CommonMultiplicity

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

def UniformFibrePacket (ω ζ δ ε ρ c : ℝ) {n N : ℕ}
    (x v : Fin n → V) (Z : Fin n → Set V) (S : Finset (Fin n))
    (f : Fin n → Fin N) (y w : Fin N → V) (M : ℕ) (k : Fin N) (U : Fin n → Set V) : Prop :=
  (∀ i, MeasurableSet (U i) ∧ U i ⊆ Z i) ∧
  (∀ i p, p ∈ U i → i ∈ S ∧ f i = k) ∧
  Nonempty (GrainPacket δ ε ρ c x v U (y k) (w k)) ∧
  (∀ p, (∃ i, p ∈ U i) → q n {i | p ∈ U i} = M) ∧
  ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    q n {i | p ∈ U i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-ε) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ U i}

/-- Size-coloring the fibre levels and equalizing point counts gives one
common multiplicity, with a loss of at most four times the palette size. -/
theorem uniform_cover_packets {ω ζ δ e ε ρ c : ℝ} {n N K : ℕ}
    {x v : Fin n → V} {Z : Fin n → Set V} {S : Finset (Fin n)}
    {f : Fin n → Fin N} {y w : Fin N → V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hc : 0 ≤ c) (heε : e ≤ ε)
    (hloss : 4 * δ ^ (-e) ≤ δ ^ (-ε))
    (hK : 0 < K) (color : ℕ → Fin K)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ 2 * b)
    (B : Finset (Fin N)) (hB : B.Nonempty) (W : Fin N → Fin n → Set V) (m : Fin N → ℝ)
    (hdata : ∀ k ∈ B, FibrePacketProperty ω ζ δ e ρ c x v Z S f y w k (W k) (m k))
    (hpositive : ∀ k ∈ B, 0 < ∑ i, μ (W k i)) :
    ∃ (A : Finset (Fin N)) (M : ℕ) (U : Fin N → Fin n → Set V),
      A ⊆ B ∧ A.Nonempty ∧ 0 < M ∧
      (∀ k ∈ A, UniformFibrePacket ω ζ δ ε ρ c x v Z S f y w M k (U k)) ∧
      (∑ k ∈ B, ∑ i, μ (W k i)) ≤ (4 * K : ENNReal) * ∑ k ∈ A, ∑ i, μ (U k i) ∧
      0 < ∑ k ∈ A, ∑ i, μ (U k i) := by
  classical
  have hceil (k : Fin N) (hk : k ∈ B) : 0 < ⌈m k⌉₊ ∧ ⌈m k⌉₊ ≤ n := by
    apply multiplicity_ceiling_bounds (Z := W k) _ (hdata k hk).2.2.2.2.1
    by_contra hh
    have he : ∀ i, W k i = ∅ := by
      intro i
      exact Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hh ⟨p, i, hp⟩)
    have hp := hpositive k hk
    simp only [he, μ, measure_empty, Finset.sum_const_zero, lt_self_iff_false] at hp
  have hBpos : 0 < ∑ k ∈ B, ∑ i, μ (W k i) := by
    obtain ⟨k, hk⟩ := hB
    exact (hpositive k hk).trans_le
      (Finset.single_le_sum (f := fun k => ∑ i, μ (W k i)) (fun _ _ => bot_le) hk)
  obtain ⟨A, M, hAB, hA, hM, hselected, hbounds⟩ :=
    select_common_size hK color hcolor B (fun k => ⌈m k⌉₊) (fun k => ∑ i, μ (W k i)) hceil hBpos
  have hexists : ∀ k : Fin N, ∃ Uk : Fin n → Set V, k ∈ A →
      UniformFibrePacket ω ζ δ ε ρ c x v Z S f y w M k Uk ∧
        (∑ i, μ (W k i)) ≤ 4 * ∑ i, μ (Uk i) := by
    intro k
    by_cases hk : k ∈ A
    · have hd := hdata k (hAB hk)
      obtain ⟨D⟩ := hd.2.2.2.2.2
      have hwindow : ∀ p, (∃ i, p ∈ W k i) →
          (M : ℝ) ≤ q n {i | p ∈ W k i} ∧ q n {i | p ∈ W k i} ≤ 4 * M := by
        simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
          multiplicity_window_of_ceiling (W k) (hbounds k hk).1 (hbounds k hk).2 hd.2.2.2.2.1
      obtain ⟨Uk, hUk, hDu, hmass, hexact, hbr⟩ := D.exact_multiplicity hδ.le hρ hM
        (by norm_num : (0 : ℝ) ≤ 4) (fun i => (hd.1 i).1) hwindow hd.2.2.2.1
      obtain ⟨Du⟩ := hDu
      refine ⟨Uk, fun _ => ⟨?_, ?_⟩⟩
      · refine ⟨fun i => ⟨(hUk i).1, (hUk i).2.trans (hd.1 i).2⟩,
          (fun i p hp => hd.2.1 i p ((hUk i).2 hp)),
          ⟨Du.mono_error hδ hδ1 heε hρ.le hc⟩, hexact, ?_⟩
        intro p u r hu hdr hrρ
        apply (hbr p u r hu hdr hrρ).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hloss
            (Real.rpow_nonneg (div_nonneg (hδ.le.trans hdr) hρ.le) _)) (Nat.cast_nonneg _)
      · simpa only [O, ENNReal.ofReal_ofNat] using hmass
    · exact ⟨fun _ => ∅, fun hh => False.elim (hk hh)⟩
  choose U hU using hexists
  have hmass : (∑ k ∈ B, ∑ i, μ (W k i)) ≤
      (4 * K : ENNReal) * ∑ k ∈ A, ∑ i, μ (U k i) := by
    calc
      _ ≤ (K : ENNReal) * ∑ k ∈ A, ∑ i, μ (W k i) := hselected
      _ ≤ (K : ENNReal) * ∑ k ∈ A, 4 * ∑ i, μ (U k i) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum (fun k hk => (hU k hk).2))
      _ = _ := by rw [← Finset.mul_sum]; ring
  refine ⟨A, M, U, hAB, hA, hM, fun k hk => (hU k hk).1, hmass, ?_⟩
  by_contra hh
  have he : (∑ k ∈ A, ∑ i, μ (U k i)) = 0 := le_antisymm (le_of_not_gt hh) bot_le
  rw [he, mul_zero] at hmass
  exact (not_le_of_gt hBpos) hmass

end WangZahlLot.Obl.wz_coarse_grains_assembly
