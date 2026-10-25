-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Cover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_terminal_grains_restoration.Defs
import Submission.WZ.Obl.wz_terminal_grains_restoration.Selection

/-!
# The restored cover

After the dyadic selection, the retained coarse tubes are reindexed by `Fin R.card`; the cover
clauses of `C`, with the below-slab condition `B` in its slot, hold for the selected fine
family at exponent `h`.
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

open MeasureTheory Finset
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- Counting a filtered finset as an `ncard`. -/
theorem qc_filter {n : ℕ} (s : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    qc n {i | i ∈ s ∧ P i} = ((s.filter P).card : ℝ) := by
  unfold qc
  rw [← Finset.coe_filter, Set.ncard_coe_finset]

theorem qc_nonneg {n : ℕ} (s : Set (Fin n)) : 0 ≤ qc n s := by
  unfold qc; positivity

theorem qc_fibre {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N) (k : Fin N) :
    qc n {i | i ∈ S ∧ f i = k} = (fc S f k : ℝ) := by
  rw [qc_filter]; rfl

/-- Fibres of the reindexed assignment, with an extra condition. -/
theorem fibre_set_reindex {n N : ℕ} {S' S₁ : Finset (Fin n)} {f : Fin n → Fin N}
    {R : Finset (Fin N)} (k0 : Fin R.card) (hS₁ : S₁ ⊆ S')
    (hmemR : ∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R)) (k : Fin R.card) (P : Fin n → Prop) :
    {i | i ∈ S₁ ∧ back R k0 (f i) = k ∧ P i} = {i | i ∈ S' ∧ f i = emb R k ∧ P i} := by
  ext i
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hi, hk, hP⟩
    have hiS' := hS₁ hi
    have hfR := (hmemR i hiS').1 hi
    exact ⟨hiS', (back_eq_iff R k0 hfR k).1 hk, hP⟩
  · rintro ⟨hi, hk, hP⟩
    have hfR : f i ∈ R := hk ▸ emb_mem R k
    exact ⟨(hmemR i hi).2 hfR, (back_eq_iff R k0 hfR k).2 hk, hP⟩

/-- Fibres of the reindexed assignment. -/
theorem fibre_set_reindex' {n N : ℕ} {S' S₁ : Finset (Fin n)} {f : Fin n → Fin N}
    {R : Finset (Fin N)} (k0 : Fin R.card) (hS₁ : S₁ ⊆ S')
    (hmemR : ∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R)) (k : Fin R.card) :
    {i | i ∈ S₁ ∧ back R k0 (f i) = k} = {i | i ∈ S' ∧ f i = emb R k} := by
  have := fibre_set_reindex k0 hS₁ hmemR k (fun _ => True)
  simp only [and_true] at this
  exact this

theorem Fp_reindex {ρ l l' : ℝ} {N N₂ : ℕ} {y w : Fin N → Space} (e : Fin N₂ → Fin N)
    (he : Function.Injective e) (hF : Fp ρ l N y w) (hll : l * N ≤ l' * N₂) :
    Fp ρ l' N₂ (fun k => y (e k)) (fun k => w (e k)) := by
  intro u t r hu hr
  have h1 := hF u t r hu hr
  have hcnt : qc N₂ {k | Tb ρ (y (e k)) (w (e k)) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r} ≤
      qc N {k | Tb ρ (y k) (w k) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r} := by
    unfold qc
    exact_mod_cast
      ncard_preimage_le he (fun k => Tb ρ (y k) (w k) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r)
  calc ENNReal.ofReal (qc N₂ {k | Tb ρ (y (e k)) (w (e k)) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r})
      ≤ ENNReal.ofReal (qc N {k | Tb ρ (y k) (w k) ⊆ Metric.ball (0:Space) 1 ∩ Qs u t r}) :=
        ENNReal.ofReal_le_ofReal hcnt
    _ ≤ ENNReal.ofReal (l * N) * volume (Metric.ball (0:Space) 1 ∩ Qs u t r) := h1
    _ ≤ ENNReal.ofReal (l' * N₂) * volume (Metric.ball (0:Space) 1 ∩ Qs u t r) := by
        gcongr

theorem Xp_reindex {ρ : ℝ} {N N₂ : ℕ} {y w : Fin N → Space} (e : Fin N₂ → Fin N)
    (he : Function.Injective e) (hX : Xp ρ N y w) :
    Xp ρ N₂ (fun k => y (e k)) (fun k => w (e k)) := by
  intro i j hij
  exact hX (e i) (e j) (fun h => hij (he h))

theorem count_reindex {ρ : ℝ} {N N₂ : ℕ} {y w : Fin N → Space} (e : Fin N₂ → Fin N)
    (he : Function.Injective e) (T : Set Space) :
    qc N₂ {k | T ⊆ Tb ρ (y (e k)) (w (e k))} ≤ qc N {k | T ⊆ Tb ρ (y k) (w k)} := by
  unfold qc
  exact_mod_cast ncard_preimage_le he (fun k => T ⊆ Tb ρ (y k) (w k))

theorem restore_cover {δ h η τ ρ : ℝ} {n N : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {S : Finset (Fin n)} {Z : Fin n → Set Space} {y w : Fin N → Space} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηh : η ≤ h) (hτh : τ ≤ h) (h2 : (2:ℝ) ≤ δ ^ (-h))
    (hC : Cp δ η n x v Y S Z ρ N y w f True)
    {S' : Finset (Fin n)} {Z' : Fin n → Set Space} (hS' : S' ⊆ S)
    (hZ' : ∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S' → Z' i = ∅))
    (hB : Bp δ ρ (δ ^ (-τ)) n N x v S' y w f)
    {R : Finset (Fin N)} {S₁ : Finset (Fin n)} {E : Fin N → Set Space} (k0 : Fin R.card)
    (hS₁ : S₁ ⊆ S') (hmemR : ∀ i ∈ S', (i ∈ S₁ ↔ f i ∈ R))
    (hbal : ∀ k ∈ R, ∀ k' ∈ R, fc S' f k ≤ 2 * fc S' f k')
    (hE : ∀ k, MeasurableSet (E k))
    (hmass₂ : ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S₁, volume (Z' i ∩ E (f i)))
    (hbudget : δ ^ (-η) * N ≤ δ ^ (-h) * R.card) :
    Cp δ h n x v Y S₁ (fun i => if i ∈ S₁ then Z' i ∩ E (f i) else ∅) ρ R.card
      (fun k => y (emb R k)) (fun k => w (emb R k)) (fun i => back R k0 (f i))
      (Bp δ ρ (δ ^ (-h)) n R.card x v S₁ (fun k => y (emb R k)) (fun k => w (emb R k))
        (fun i => back R k0 (f i))) := by
  obtain ⟨hZ, -, hw, hTsub, hF, -, -, hX, hcount⟩ := hC
  have hpow_le : ∀ {a b : ℝ}, a ≤ b → δ ^ (-a) ≤ δ ^ (-b) := fun hab =>
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  unfold Cp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- shadings
    intro i
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · split_ifs
      · exact (hZ' i).1.inter (hE _)
      · exact MeasurableSet.empty
    · split_ifs
      · exact Set.inter_subset_left.trans ((hZ' i).2.1.trans (hZ i).2.1)
      · exact Set.empty_subset _
    · intro hi
      simp [hi]
  · -- mass
    calc ENNReal.ofReal (δ ^ h) * ∑ i, volume (Y i) ≤ ∑ i ∈ S₁, volume (Z' i ∩ E (f i)) := hmass₂
      _ = ∑ i ∈ S₁, volume (if i ∈ S₁ then Z' i ∩ E (f i) else ∅) := by
          refine sum_congr rfl (fun i hi => ?_)
          simp [hi]
  · intro k; exact hw _
  · intro i hi
    have hfR : f i ∈ R := (hmemR i (hS₁ hi)).1 hi
    simp only [emb_back R k0 hfR]
    exact hTsub i (hS' (hS₁ hi))
  · -- Frostman
    exact Fp_reindex (emb R) (emb_injective R) hF hbudget
  · -- below slab
    intro k u t r hu hr
    have h1 := hB (emb R k) u t r hu hr
    have e1 : qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k ∧ Tb δ (x i) (v i) ⊆
          Tb (2*ρ) (y (emb R k) - (1/2:ℝ) • w (emb R k)) (2 • w (emb R k)) ∩ Qs u t r} =
        qc n {i | i ∈ S' ∧ f i = emb R k ∧ Tb δ (x i) (v i) ⊆
          Tb (2*ρ) (y (emb R k) - (1/2:ℝ) • w (emb R k)) (2 • w (emb R k)) ∩ Qs u t r} := by
      rw [fibre_set_reindex k0 hS₁ hmemR k]
    have e2 : qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k} = qc n {i | i ∈ S' ∧ f i = emb R k} := by
      rw [fibre_set_reindex' k0 hS₁ hmemR k]
    show ENNReal.ofReal (qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k ∧ Tb δ (x i) (v i) ⊆
          Tb (2*ρ) (y (emb R k) - (1/2:ℝ) • w (emb R k)) (2 • w (emb R k)) ∩ Qs u t r}) *
        volume (Tb (2*ρ) (y (emb R k) - (1/2:ℝ) • w (emb R k)) (2 • w (emb R k))) ≤
      ENNReal.ofReal (δ ^ (-h) * qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k}) *
        volume (Tb (2*ρ) (y (emb R k) - (1/2:ℝ) • w (emb R k)) (2 • w (emb R k)) ∩ Qs u t r)
    rw [e1, e2]
    refine h1.trans ?_
    have hle : δ ^ (-τ) * qc n {i | i ∈ S' ∧ f i = emb R k} ≤
        δ ^ (-h) * qc n {i | i ∈ S' ∧ f i = emb R k} :=
      mul_le_mul_of_nonneg_right (hpow_le hτh) (qc_nonneg _)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl
  · -- balance
    intro k k'
    show qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k} ≤
      δ ^ (-h) * qc n {i | i ∈ S₁ ∧ back R k0 (f i) = k'}
    rw [fibre_set_reindex' k0 hS₁ hmemR k, fibre_set_reindex' k0 hS₁ hmemR k', qc_fibre,
      qc_fibre]
    have hb := hbal (emb R k) (emb_mem R k) (emb R k') (emb_mem R k')
    have hb' : (fc S' f (emb R k) : ℝ) ≤ 2 * (fc S' f (emb R k') : ℝ) := by exact_mod_cast hb
    calc (fc S' f (emb R k) : ℝ) ≤ 2 * (fc S' f (emb R k') : ℝ) := hb'
      _ ≤ δ ^ (-h) * (fc S' f (emb R k') : ℝ) := by gcongr
  · exact Xp_reindex (emb R) (emb_injective R) hX
  · intro i hi
    calc qc R.card {k | Tb δ (x i) (v i) ⊆ Tb ρ (y (emb R k)) (w (emb R k))}
        ≤ qc N {k | Tb δ (x i) (v i) ⊆ Tb ρ (y k) (w k)} :=
          count_reindex (emb R) (emb_injective R) _
      _ ≤ δ ^ (-η) := hcount i (hS' (hS₁ hi))
      _ ≤ δ ^ (-h) := hpow_le hηh

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
