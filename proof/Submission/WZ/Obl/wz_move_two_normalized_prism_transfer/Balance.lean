-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.Balance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Cover
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Balance
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.MassTransfer

noncomputable section
namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
open Set MeasureTheory

/-- Selecting whole occupied coarse fibres supplies every condition of the frozen
cover while preserving broadness. The scalar loss budgets are explicit. -/
theorem balance_assigned_cover {ω ζ δ η h t ε ρ R : ℝ} {n N b : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) (hηt : η ≤ t)
    (hhε : h ≤ ε) (htε : t ≤ ε)
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ S → Z i = ∅))
    (hmass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (Z i))
    (hw : ∀ k, ‖w k‖ = 1)
    (hcont : ∀ i ∈ S, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i)))
    (hX : X ρ N y w)
    (huniq : ∀ i ∈ S, ∀ k k', T δ (x i) (v i) ⊆ T ρ (y k) (w k) →
      T δ (x i) (v i) ⊆ T ρ (y k') (w k') → k = k')
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hb : 0 < b) (hR : 1 < R) (hbn : (n : ℝ) < R ^ b)
    (hmassbudget : (b : ℝ) * δ ^ t ≤ δ ^ h)
    (hFbudget : R * (56 * δ ^ (-(4 * t))) * δ ^ (-η) ≤ δ ^ (-ε))
    (hRbudget : R ≤ δ ^ (-ε)) (hone : 1 ≤ δ ^ (-ε)) :
    ∃ (Q : Finset (Fin N)) (hQ : Q.Nonempty),
      let S' := S.filter (fun i => f i ∈ Q)
      let Z' := fun i => if f i ∈ Q then Z i else ∅
      let y' := y ∘ WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q
      let w' := w ∘ WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q
      let f' := WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ f
      C δ ε n x v Y S' Z' ρ Q.card y' w' f' True ∧
      Broad ω ζ δ ε ρ n Q.card v S' Z' f' ∧
      O (δ ^ t) * ∑ i, μ (Y i) ≤ ∑ i ∈ S', μ (Z' i) := by
  classical
  obtain ⟨S₁, hS₁, hmass₁, hwhole, hbalance⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.balance_whole_fibres hb hR hbn S f
      (fun i => μ (Z i))
  have hret : O (δ ^ t) * ∑ i, μ (Y i) ≤ ∑ i ∈ S₁, μ (Z i) := by
    apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.cancel_volume_factor (Nat.cast_pos.mpr hb)
    calc
      _ = O ((b : ℝ) * δ ^ t) * ∑ i, μ (Y i) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ O (δ ^ h) * ∑ i, μ (Y i) := mul_le_mul' (ENNReal.ofReal_le_ofReal hmassbudget) le_rfl
      _ ≤ ∑ i ∈ S, μ (Z i) := hmass
      _ ≤ (b : ENNReal) * ∑ i ∈ S₁, μ (Z i) := hmass₁
      _ = _ := by simp only [O, ENNReal.ofReal_natCast]
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hYpos : 0 < ∑ i, μ (Y i) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hA.2.2.2.1
  have hS₁pos : S₁.Nonempty := by
    by_contra hh
    rw [Finset.not_nonempty_iff_eq_empty.mp hh, Finset.sum_empty] at hret
    exact not_le_of_gt (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ t)).ne' hYpos.ne') hret
  let Q := S₁.image f
  have hQ : Q.Nonempty := hS₁pos.image _
  let S' := S.filter (fun i => f i ∈ Q)
  let Z' := fun i => if f i ∈ Q then Z i else ∅
  let fk := WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx Q
  let f' := WangZahlLot.Obl.wz_coarse_grains_assembly.rFib Q hQ f
  have hQmem {i} (hi : i ∈ S₁) : f i ∈ Q := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hSf : S' = S₁ := by
    ext i
    simp only [S', Finset.mem_filter]
    constructor
    · rintro ⟨hiS, hiQ⟩
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiQ
      exact hwhole j hj i hiS hji
    · intro hi
      exact ⟨hS₁ hi, hQmem hi⟩
  have hf (i) (hi : i ∈ S') : fk (f' i) = f i :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_rFib Q hQ f (Finset.mem_filter.mp hi).2
  have hZ' (i) : MeasurableSet (Z' i) ∧ Z' i ⊆ Y i ∧ (i ∉ S' → Z' i = ∅) := by
    by_cases hi : f i ∈ Q
    · simp only [Z', ite_eq_left hi]
      refine ⟨(hZ i).1, (hZ i).2.1, fun hnot => (hZ i).2.2 ?_⟩
      intro hiS
      exact hnot (Finset.mem_filter.mpr ⟨hiS, hi⟩)
    · simp [Z', hi]
  have hsum : ∑ i ∈ S', μ (Z' i) = ∑ i ∈ S₁, μ (Z i) := by
    rw [hSf]
    exact Finset.sum_congr rfl (fun i hi => by simp only [Z', ite_eq_left (hQmem hi)])
  have hret' : O (δ ^ t) * ∑ i, μ (Y i) ≤ ∑ i ∈ S', μ (Z' i) := by rwa [hsum]
  have hcount : (n : ℝ) ≤ (56 * δ ^ (-(4 * t))) * S'.card := by
    have hden : O (δ ^ t * n * δ ^ 2) ≤ ∑ i, μ (Y i) := by
      apply le_trans (b := O (δ ^ η * n * δ ^ 2)) _ hA.2.2.2.1
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηt)
          (Nat.cast_nonneg n)) (sq_nonneg δ))
    have hret₃ : O (δ ^ (3 * t)) * ∑ i, μ (Y i) ≤ ∑ i ∈ S', μ (Z' i) :=
      (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))) le_rfl).trans hret'
    have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.retained_card_of_mass hδ hδ hδ1
      x v Y id Z' S' (fun i => (hA.2.1 i).1)
      (fun i => (hZ' i).2.1.trans (hA.2.1 i).2.2.2) hden hret₃
    have hd : 0 < δ ^ (4 * t) := Real.rpow_pos_of_pos hδ _
    rw [Real.rpow_neg hδ.le]
    apply (mul_le_mul_iff_of_pos_right hd).mp
    field_simp
    nlinarith
  have hcont' (i) (hi : i ∈ S') :
      T δ (x i) (v i) ⊆ T ρ ((y ∘ fk) (f' i)) ((w ∘ fk) (f' i)) := by
    simpa only [Function.comp_apply, hf i hi] using hcont i (Finset.mem_filter.mp hi).1
  have hbal (k k' : Fin Q.card) :
      q n {i | i ∈ S' ∧ f' i = k} ≤ R * q n {i | i ∈ S' ∧ f' i = k'} := by
    have heq (k : Fin Q.card) : {i | i ∈ S' ∧ f' i = k} =
        (S₁.filter (fun i => f i = fk k) : Set (Fin n)) := by
      ext i
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hi, hik⟩
        exact ⟨hSf ▸ hi, (hf i hi).symm.trans (congrArg fk hik)⟩
      · rintro ⟨hi, hik⟩
        refine ⟨hSf.symm ▸ hi, ?_⟩
        exact (WangZahlLot.Obl.wz_coarse_grains_assembly.rFib_eq_iff Q hQ f (hQmem hi) k).2 hik
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp
      (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem Q k)
    obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp
      (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_mem Q k')
    change f i = fk k at hik
    change f j = fk k' at hjk
    simp only [q, heq, Set.ncard_coe_finset]
    rw [← hik, ← hjk]
    exact hbalance i hi j hj
  refine ⟨Q, hQ, ?_, ?_, hret'⟩
  · apply cover_of_unique_balanced (hSf.symm ▸ hS₁pos) (by linarith : 0 ≤ R)
      (by positivity) (Real.rpow_nonneg hδ.le _) hA hZ'
      ((mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 htε)) le_rfl).trans hret')
      (fun k => hw (fk k)) hcont' hbal hcount
      (fun k k' hne => hX (fk k) (fk k')
        (fun he => hne (WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q he)))
      ?_ hFbudget hRbudget hone
    intro i hi k hik
    apply WangZahlLot.Obl.wz_coarse_grains_assembly.rIdx_injective Q
    exact huniq i (Finset.mem_filter.mp hi).1 (fk k) (fk (f' i)) hik (hcont' i hi)
  · exact WangZahlLot.Obl.wz_coarse_grains_assembly.Broad_mono hδ hδ1 hhε
      (WangZahlLot.Obl.wz_coarse_grains_assembly.broad_restrict Q hQ hbr)

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
