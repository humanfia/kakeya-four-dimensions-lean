-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Grains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_terminal_grains_restoration.Cover

/-!
# The restored grains

The old grains attached to the retained coarse tubes are kept, with their boxes, and their
shadings are intersected with the new fibre unions. Their mass is controlled through the
multiplicity bounds: old multiplicities lie in `[m, 2m]` and the new ones are at most the old.
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory Finset
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem qc_mult {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (Z : Fin n → Set Space)
    (k : Fin N) (p : Space) :
    qc n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} = (mult (S.filter (fun i => f i = k)) Z p : ℝ) := by
  classical
  unfold qc mult
  rw [← Set.ncard_coe_finset]
  congr 2
  ext i
  simp [Finset.mem_filter, and_assoc]

/-- A fibre union as a union over a finset. -/
theorem fibre_union_eq {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (Z : Fin n → Set Space)
    (k : Fin N) : {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} = ⋃ i ∈ S.filter (fun i => f i = k), Z i := by
  ext p
  simp [Finset.mem_filter, and_assoc]

theorem grain_union_eq {L N : ℕ} (γ : Fin L → Fin N) (H : Fin L → Set Space) (k : Fin N) :
    {p | ∃ j, γ j = k ∧ p ∈ H j} = ⋃ j ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k), H j := by
  ext p
  simp [Finset.mem_filter]

theorem restore_grains {δ h η ζ ρ c a g s : ℝ} {n N : ℕ} {x v : Fin n → Space}
    {S : Finset (Fin n)} {Z : Fin n → Set Space} {y w : Fin N → Space} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n) (hρ : 0 < ρ) (hζh : ζ ≤ h)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hH : Hp δ η n x v S Z ρ N y w f a c 0 g)
    (hlen : δ ^ ζ * (ρ / δ) * N / n ≤ c) (hgζ : g ≤ δ ^ (-ζ))
    {S' : Finset (Fin n)} {Z' : Fin n → Set Space} (hS' : S' ⊆ S)
    (hZ' : ∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S' → Z' i = ∅))
    {R : Finset (Fin N)} {S₁ : Finset (Fin n)} {E : Fin N → Set Space} {ℓ : ℕ}
    (k0 : Fin R.card) (hS₁ : S₁ ⊆ S') (hmemR : ∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R))
    (hE : ∀ k, MeasurableSet (E k))
    (hmult : ∀ k p, p ∈ E k → (∃ i ∈ S₁, f i = k ∧ p ∈ Z' i) →
        2 ^ ℓ ≤ mult (S₁.filter (fun i => f i = k)) Z' p ∧
          mult (S₁.filter (fun i => f i = k)) Z' p < 2 ^ (ℓ + 1))
    (hs : 0 ≤ s)
    (hΦ : ENNReal.ofReal s * ∑ i ∈ S, volume (Z i) ≤ ∑ i ∈ S₁, volume (Z' i ∩ E (f i)))
    (hsh : 2 * δ ^ h ≤ s * δ ^ η) :
    Hp δ h n x v S₁ (fun i => if i ∈ S₁ then Z' i ∩ E (f i) else ∅) ρ R.card
      (fun k => y (emb R k)) (fun k => w (emb R k)) (fun i => back R k0 (f i))
      a c (δ ^ h * (ρ / δ) * R.card / n) (δ ^ (-h)) := by
  classical
  obtain ⟨L, z, e, Hs, γ, m, hb⟩ := hH
  obtain ⟨hda, haρc, hρcc, hc1, hHj, hdisj, hunion, hdens, hmultold, hcross, -, hconv⟩ := hb
  set Z₂ : Fin n → Set Space := fun i => if i ∈ S₁ then Z' i ∩ E (f i) else ∅ with hZ₂
  have hZ₂S : ∀ i ∈ S₁, Z₂ i = Z' i ∩ E (f i) := fun i hi => by simp [hZ₂, hi]
  have hZ₂meas : ∀ i, MeasurableSet (Z₂ i) := by
    intro i
    by_cases hi : i ∈ S₁
    · rw [hZ₂S i hi]; exact (hZ' i).1.inter (hE _)
    · simp [hZ₂, hi]
  have hZ₂sub : ∀ i, Z₂ i ⊆ Z i := by
    intro i
    by_cases hi : i ∈ S₁
    · rw [hZ₂S i hi]; exact Set.inter_subset_left.trans (hZ' i).2.1
    · simp [hZ₂, hi]
  have hS₁S : ∀ i ∈ S₁, i ∈ S := fun i hi => hS' (hS₁ hi)
  have hfR : ∀ i ∈ S₁, f i ∈ R := fun i hi => (hmemR i (hS₁ hi)).1 hi
  set RL : Finset (Fin L) := univ.filter (fun j => γ j ∈ R) with hRL
  have hγR : ∀ j : Fin RL.card, γ (emb RL j) ∈ R := fun j => (mem_filter.1 (emb_mem RL j)).2
  set Hn : Fin L → Set Space := fun j => Hs j ∩ ⋃ i ∈ S₁.filter (fun i => f i = γ j), Z₂ i
    with hHn
  have hHnsub : ∀ j, Hn j ⊆ Hs j := fun j => Set.inter_subset_left
  have hHnmeas : ∀ j, MeasurableSet (Hn j) := fun j =>
    (hHj j).1.inter (Finset.measurableSet_biUnion _ (fun i _ => hZ₂meas i))
  -- the new fibre unions
  have hnewunion : ∀ k : Fin N, ⋃ j ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k), Hn j =
      ⋃ i ∈ S₁.filter (fun i => f i = k), Z₂ i := by
    intro k
    ext p
    simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop, hHn,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨j, hj, -, i, ⟨hi, hfi⟩, hp⟩
      exact ⟨i, ⟨hi, hfi.trans hj⟩, hp⟩
    · rintro ⟨i, ⟨hi, hfi⟩, hp⟩
      have hpold : p ∈ {p | ∃ i ∈ S, f i = k ∧ p ∈ Z i} := ⟨i, hS₁S i hi, hfi, hZ₂sub i hp⟩
      rw [← hunion k] at hpold
      obtain ⟨j, hj, hpj⟩ := hpold
      exact ⟨j, hj, hpj, i, ⟨hi, hfi.trans hj.symm⟩, hp⟩
  refine ⟨RL.card, fun j => z (emb RL j), fun j => e (emb RL j), fun j => Hn (emb RL j),
    fun j => back R k0 (γ (emb RL j)), (2:ℝ) ^ ℓ, ?_⟩
  unfold HBody
  refine ⟨hda, haρc, hρcc, hc1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- grains in boxes in coarse tubes
    intro j
    obtain ⟨-, hHU, hUT, hal⟩ := hHj (emb RL j)
    refine ⟨hHnmeas _, (hHnsub _).trans hHU, ?_, ?_⟩
    · simp only [emb_back R k0 (hγR j)]
      exact hUT
    · simp only [emb_back R k0 (hγR j)]
      exact hal
  · -- disjointness
    intro j j' hjj' hγ
    have hne : emb RL j ≠ emb RL j' := fun h => hjj' (emb_injective RL h)
    have hγ' : γ (emb RL j) = γ (emb RL j') := by
      have := congrArg (emb R) hγ
      simp only [emb_back R k0 (hγR j), emb_back R k0 (hγR j')] at this
      exact this
    exact (hdisj _ _ hne hγ').mono (hHnsub _) (hHnsub _)
  · -- fibre unions
    intro k
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hp⟩
      have hk : γ (emb RL j) = emb R k := (back_eq_iff R k0 (hγR j) k).1 hj
      obtain ⟨-, hp2⟩ := hp
      simp only [Set.mem_iUnion, mem_filter, exists_prop] at hp2
      obtain ⟨i, ⟨hi, hfi⟩, hpi⟩ := hp2
      refine ⟨i, hi, ?_, hpi⟩
      rw [back_eq_iff R k0 (hfR i hi)]
      exact hfi.trans hk
    · rintro ⟨i, hi, hk, hp⟩
      have hfi : f i = emb R k := (back_eq_iff R k0 (hfR i hi) k).1 hk
      have hp' : p ∈ ⋃ i ∈ S₁.filter (fun i => f i = emb R k), Z₂ i := by
        simp only [Set.mem_iUnion, mem_filter, exists_prop]
        exact ⟨i, ⟨hi, hfi⟩, hp⟩
      rw [← hnewunion (emb R k)] at hp'
      simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop] at hp'
      obtain ⟨j₀, hj₀, hpj₀⟩ := hp'
      have hj₀RL : j₀ ∈ RL := mem_filter.2 ⟨mem_univ _, hj₀ ▸ emb_mem R k⟩
      have hRLpos : 0 < RL.card := card_pos.2 ⟨j₀, hj₀RL⟩
      refine ⟨back RL ⟨0, hRLpos⟩ j₀, ?_, ?_⟩
      · rw [emb_back RL _ hj₀RL, hj₀, back_emb]
      · rw [emb_back RL _ hj₀RL]; exact hpj₀
  · -- grain density
    show ENNReal.ofReal (δ ^ h * (RL.card : ℝ) * a * (ρ * c) * c) ≤
      ∑ j : Fin RL.card, volume (Hn (emb RL j))
    rw [sum_emb RL (fun j₀ => volume (Hn j₀))]
    have hoff : ∑ j₀ ∈ RL, volume (Hn j₀) = ∑ j₀, volume (Hn j₀) := by
      refine sum_subset (subset_univ _) (fun j₀ _ hj₀ => ?_)
      have hγ : γ j₀ ∉ R := fun h => hj₀ (mem_filter.2 ⟨mem_univ _, h⟩)
      have : Hn j₀ = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro p hp
        have hp2 := hp.2
        simp only [Set.mem_iUnion, mem_filter, exists_prop] at hp2
        obtain ⟨i, ⟨hi, hfi⟩, _⟩ := hp2
        exact hγ (hfi ▸ hfR i hi)
      rw [this, measure_empty]
    rw [hoff]
    have hHsmeas : ∀ j, MeasurableSet (Hs j) := fun j => (hHj j).1
    have hfib_new : ∀ k : Fin N, ∑ j₀ ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k),
        volume (Hn j₀) = volume (⋃ i ∈ S₁.filter (fun i => f i = k), Z₂ i) := by
      intro k
      rw [← hnewunion k, measure_biUnion_finset]
      · intro j₀ hj₀ j₁ hj₁ hne
        exact (hdisj j₀ j₁ hne ((mem_filter.1 (Finset.mem_coe.1 hj₀)).2.trans
          (mem_filter.1 (Finset.mem_coe.1 hj₁)).2.symm)).mono (hHnsub _) (hHnsub _)
      · intro j₀ _; exact hHnmeas j₀
    have hfib_old : ∀ k : Fin N, ∑ j₀ ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k),
        volume (Hs j₀) = volume (⋃ i ∈ S.filter (fun i => f i = k), Z i) := by
      intro k
      rw [← fibre_union_eq, ← hunion k, grain_union_eq, measure_biUnion_finset]
      · intro j₀ hj₀ j₁ hj₁ hne
        exact hdisj j₀ j₁ hne ((mem_filter.1 (Finset.mem_coe.1 hj₀)).2.trans
          (mem_filter.1 (Finset.mem_coe.1 hj₁)).2.symm)
      · intro j₀ _; exact hHsmeas j₀
    have hm2 : ∀ k : Fin N, ∑ i ∈ S₁.filter (fun i => f i = k), volume (Z₂ i) ≤
        ENNReal.ofReal (2 * m) * volume (⋃ i ∈ S₁.filter (fun i => f i = k), Z₂ i) := by
      intro k
      refine sum_measure_le_of_mult_le volume _ Z₂ (fun i _ => hZ₂meas i) (2 * m) ?_
      intro p hp
      simp only [Set.mem_iUnion, mem_filter, exists_prop] at hp
      obtain ⟨i₀, ⟨hi₀, hfi₀⟩, hpi₀⟩ := hp
      have hold := (hmultold k p ⟨i₀, hS₁S i₀ hi₀, hfi₀, hZ₂sub i₀ hpi₀⟩).2
      rw [qc_mult] at hold
      have hle : mult (S₁.filter (fun i => f i = k)) Z₂ p ≤
          mult (S.filter (fun i => f i = k)) Z p := by
        unfold mult
        apply card_le_card
        intro i
        simp only [mem_filter]
        rintro ⟨⟨hi, hfi⟩, hp⟩
        exact ⟨⟨hS₁S i hi, hfi⟩, hZ₂sub i hp⟩
      calc (mult (S₁.filter (fun i => f i = k)) Z₂ p : ℝ)
          ≤ mult (S.filter (fun i => f i = k)) Z p := by exact_mod_cast hle
        _ ≤ 2 * m := hold
    have hm1 : ∀ k : Fin N, ENNReal.ofReal m * volume (⋃ i ∈ S.filter (fun i => f i = k), Z i) ≤
        ∑ i ∈ S.filter (fun i => f i = k), volume (Z i) := by
      intro k
      refine le_sum_measure_of_le_mult volume _ Z (fun i _ => hZm i) m ?_
      intro p hp
      simp only [Set.mem_iUnion, mem_filter, exists_prop] at hp
      obtain ⟨i₀, ⟨hi₀, hfi₀⟩, hpi₀⟩ := hp
      have hold := (hmultold k p ⟨i₀, hi₀, hfi₀, hpi₀⟩).1
      rw [qc_mult] at hold
      exact hold
    have hΦ₂ : ∑ i ∈ S₁, volume (Z' i ∩ E (f i)) ≤ ENNReal.ofReal (2 * m) * ∑ j₀, volume (Hn j₀) := by
      calc ∑ i ∈ S₁, volume (Z' i ∩ E (f i)) = ∑ i ∈ S₁, volume (Z₂ i) :=
            sum_congr rfl (fun i hi => by rw [hZ₂S i hi])
        _ = ∑ k, ∑ i ∈ S₁.filter (fun i => f i = k), volume (Z₂ i) := (sum_fiberwise S₁ f _).symm
        _ ≤ ∑ k, ENNReal.ofReal (2 * m) * volume (⋃ i ∈ S₁.filter (fun i => f i = k), Z₂ i) :=
            sum_le_sum (fun k _ => hm2 k)
        _ = ∑ k, ENNReal.ofReal (2 * m) *
              ∑ j₀ ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k), volume (Hn j₀) := by
            refine sum_congr rfl (fun k _ => ?_); rw [hfib_new k]
        _ = ENNReal.ofReal (2 * m) * ∑ j₀, volume (Hn j₀) := by
            rw [← mul_sum, sum_fiberwise]
    have hΦold : ENNReal.ofReal m * ∑ j₀, volume (Hs j₀) ≤ ∑ i ∈ S, volume (Z i) := by
      calc ENNReal.ofReal m * ∑ j₀, volume (Hs j₀) = ∑ k, ENNReal.ofReal m *
            ∑ j₀ ∈ (univ : Finset (Fin L)).filter (fun j => γ j = k), volume (Hs j₀) := by
            rw [← mul_sum, sum_fiberwise]
        _ = ∑ k, ENNReal.ofReal m * volume (⋃ i ∈ S.filter (fun i => f i = k), Z i) := by
            refine sum_congr rfl (fun k _ => ?_); rw [hfib_old k]
        _ ≤ ∑ k, ∑ i ∈ S.filter (fun i => f i = k), volume (Z i) := sum_le_sum (fun k _ => hm1 k)
        _ = ∑ i ∈ S, volume (Z i) := sum_fiberwise S f _
    have hRLL : (RL.card : ℝ) ≤ L := by
      have := card_le_univ RL
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hapos : 0 < a := lt_of_lt_of_le hδ hda
    have hρcpos : 0 < ρ * c := lt_of_lt_of_le hapos haρc
    have hcpos : 0 < c := lt_of_lt_of_le hρcpos hρcc
    have hP : 0 < a * (ρ * c) * c := by positivity
    by_cases hm : 0 < m
    · set X := ∑ j₀, volume (Hn j₀) with hX
      have key : ENNReal.ofReal m * ENNReal.ofReal (s * (δ ^ η * L * a * (ρ * c) * c)) ≤
          ENNReal.ofReal m * (ENNReal.ofReal 2 * X) := by
        calc ENNReal.ofReal m * ENNReal.ofReal (s * (δ ^ η * L * a * (ρ * c) * c))
            = ENNReal.ofReal s *
                (ENNReal.ofReal m * ENNReal.ofReal (δ ^ η * L * a * (ρ * c) * c)) := by
              rw [ENNReal.ofReal_mul hs]; ring
          _ ≤ ENNReal.ofReal s * (ENNReal.ofReal m * ∑ j₀, volume (Hs j₀)) := by gcongr
          _ ≤ ENNReal.ofReal s * ∑ i ∈ S, volume (Z i) := by gcongr
          _ ≤ ∑ i ∈ S₁, volume (Z' i ∩ E (f i)) := hΦ
          _ ≤ ENNReal.ofReal (2 * m) * X := hΦ₂
          _ = ENNReal.ofReal m * (ENNReal.ofReal 2 * X) := by
              rw [mul_comm 2 m, ENNReal.ofReal_mul hm.le]; ring
      have key2 := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hm).ne'
        ENNReal.ofReal_ne_top).1 key
      have hreal : 2 * (δ ^ h * RL.card * a * (ρ * c) * c) ≤ s * (δ ^ η * L * a * (ρ * c) * c) := by
        have h1 : 2 * (δ ^ h * RL.card * a * (ρ * c) * c) =
            (2 * δ ^ h) * (RL.card * (a * (ρ * c) * c)) := by ring
        have h2 : s * (δ ^ η * L * a * (ρ * c) * c) = (s * δ ^ η) * (L * (a * (ρ * c) * c)) := by
          ring
        rw [h1, h2]
        apply mul_le_mul hsh (mul_le_mul_of_nonneg_right hRLL hP.le) (by positivity)
          (by have := Real.rpow_pos_of_pos hδ η; positivity)
      have h3 : ENNReal.ofReal 2 * ENNReal.ofReal (δ ^ h * RL.card * a * (ρ * c) * c) ≤
          ENNReal.ofReal 2 * X := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact (ENNReal.ofReal_le_ofReal hreal).trans key2
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 two_pos).ne'
        ENNReal.ofReal_ne_top).1 h3
    · rw [not_lt] at hm
      have hHempty : ∀ j₀, Hs j₀ = ∅ := by
        intro j₀
        apply Set.eq_empty_of_forall_notMem
        intro p hp
        have hp' : p ∈ {p | ∃ j, γ j = γ j₀ ∧ p ∈ Hs j} := ⟨j₀, rfl, hp⟩
        rw [hunion] at hp'
        obtain ⟨i, hi, hfi, hpi⟩ := hp'
        have hq := hmultold (γ j₀) p ⟨i, hi, hfi, hpi⟩
        rw [qc_mult] at hq
        have hpos : 0 < mult (S.filter (fun i => f i = γ j₀)) Z p :=
          mult_pos_of_mem (mem_filter.2 ⟨hi, hfi⟩) hpi
        have : (1 : ℝ) ≤ mult (S.filter (fun i => f i = γ j₀)) Z p := by exact_mod_cast hpos
        linarith [hq.2]
      have hL0 : L = 0 := by
        by_contra hL
        have hsum0 : ∑ j₀, volume (Hs j₀) = 0 := by simp [hHempty]
        rw [hsum0] at hdens
        have hQ := ENNReal.ofReal_eq_zero.1 (le_antisymm hdens bot_le)
        have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL
        have : 0 < δ ^ η * L * a * (ρ * c) * c :=
          mul_pos (mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos hδ η) hLpos) hapos) hρcpos)
            hcpos
        linarith
      have hRL0 : RL.card = 0 := by
        have := card_le_univ RL
        simp only [Fintype.card_fin, hL0] at this
        omega
      rw [hRL0]
      simp
  · -- multiplicity
    intro k p ⟨i₀, hi₀, hk₀, hp₀⟩
    have hf₀ : f i₀ = emb R k := (back_eq_iff R k0 (hfR i₀ hi₀) k).1 hk₀
    rw [hZ₂S i₀ hi₀, hf₀] at hp₀
    have hset : {i | i ∈ S₁ ∧ back R k0 (f i) = k ∧ p ∈ Z₂ i} =
        {i | i ∈ S₁ ∧ f i = emb R k ∧ p ∈ Z' i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hi, hk, hp⟩
        have hfi := (back_eq_iff R k0 (hfR i hi) k).1 hk
        rw [hZ₂S i hi] at hp
        exact ⟨hi, hfi, hp.1⟩
      · rintro ⟨hi, hfi, hp⟩
        refine ⟨hi, (back_eq_iff R k0 (hfR i hi) k).2 hfi, ?_⟩
        rw [hZ₂S i hi, hfi]
        exact ⟨hp, hp₀.2⟩
    show qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k ∧ p ∈ Z₂ i} ∈ Set.Icc ((2:ℝ) ^ ℓ) (2 * 2 ^ ℓ)
    rw [hset, qc_mult]
    obtain ⟨hlo, hhi⟩ := hmult (emb R k) p hp₀.2 ⟨i₀, hi₀, hf₀, hp₀.1⟩
    constructor
    · exact_mod_cast hlo
    · have : mult (S₁.filter (fun i => f i = emb R k)) Z' p ≤ 2 * 2 ^ ℓ := by
        rw [pow_succ] at hhi; omega
      exact_mod_cast this
  · -- robust crossing
    intro i hi j hij hne
    have hfi : f i = γ (emb RL j) := by
      have := congrArg (emb R) hij
      simp only [emb_back R k0 (hfR i hi), emb_back R k0 (hγR j)] at this
      exact this
    obtain ⟨p, hpZ, hpH⟩ := hne
    obtain ⟨hsub, hfront, hend⟩ :=
      hcross i (hS₁S i hi) (emb RL j) hfi ⟨p, hZ₂sub i hpZ, hHnsub _ hpH⟩
    refine ⟨?_, hfront, hend⟩
    intro q ⟨hqZ, hqU⟩
    refine ⟨hsub ⟨hZ₂sub i hqZ, hqU⟩, ?_⟩
    simp only [Set.mem_iUnion, mem_filter, exists_prop]
    exact ⟨i, ⟨hi, hfi⟩, hqZ⟩
  · -- length bound
    have hRN : (R.card : ℝ) ≤ N := by
      have := card_le_univ R
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hpow : δ ^ h ≤ δ ^ ζ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hζh
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc δ ^ h * (ρ / δ) * R.card / n ≤ δ ^ ζ * (ρ / δ) * N / n := by
          gcongr
      _ ≤ c := hlen
  · -- local convex count
    intro j W hW
    have h1 := hconv (emb RL j) W hW
    have hcnt : qc RL.card {j' | Pb (a/ρ) c c (z (emb RL j')) (e (emb RL j')) ⊆
          Pb (2*a/ρ) (2*c) (2*c) (z (emb RL j)) (e (emb RL j)) ∧
          Pb a (ρ*c) c (z (emb RL j')) (e (emb RL j')) ⊆ W} ≤
        qc L {j' | Pb (a/ρ) c c (z j') (e j') ⊆
          Pb (2*a/ρ) (2*c) (2*c) (z (emb RL j)) (e (emb RL j)) ∧
          Pb a (ρ*c) c (z j') (e j') ⊆ W} := by
      unfold qc
      exact_mod_cast ncard_preimage_le (emb_injective RL) (fun j' =>
        Pb (a/ρ) c c (z j') (e j') ⊆ Pb (2*a/ρ) (2*c) (2*c) (z (emb RL j)) (e (emb RL j)) ∧
          Pb a (ρ*c) c (z j') (e j') ⊆ W)
    have ha : 0 ≤ a * (ρ * c) * c := by
      have : 0 < a := lt_of_lt_of_le hδ hda
      have : 0 < ρ * c := lt_of_lt_of_le this haρc
      have : 0 < c := lt_of_lt_of_le this hρcc
      positivity
    have hg : g ≤ δ ^ (-h) := hgζ.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    calc ENNReal.ofReal (qc RL.card {j' | Pb (a/ρ) c c (z (emb RL j')) (e (emb RL j')) ⊆
          Pb (2*a/ρ) (2*c) (2*c) (z (emb RL j)) (e (emb RL j)) ∧
          Pb a (ρ*c) c (z (emb RL j')) (e (emb RL j')) ⊆ W} * (a * (ρ * c) * c))
        ≤ ENNReal.ofReal (qc L {j' | Pb (a/ρ) c c (z j') (e j') ⊆
          Pb (2*a/ρ) (2*c) (2*c) (z (emb RL j)) (e (emb RL j)) ∧
          Pb a (ρ*c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcnt ha)
      _ ≤ ENNReal.ofReal g * volume W := h1
      _ ≤ ENNReal.ofReal (δ ^ (-h)) * volume W := by
          gcongr

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
