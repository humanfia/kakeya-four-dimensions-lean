-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.PacketComposition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PacketNumerics
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatRegularization

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridKeys gridUnion_measurable gridUnion_volume_ne_top)

/-- The fine estimate with the prism, scale and counting coefficient fixed. -/
def FineEstimateAt (σ u ε A η δ a b L : ℝ) (e : AffineIsometryEquiv ℝ Space Space) : Prop :=
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ e '' StandardPrism a b) →
    (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    (∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (L * n / (a * b)) * volume Q) →
    ENNReal.ofReal (A * δ ^ ε * (δ / a) ^ u * L⁻¹ *
      (a * b) ^ (1 - σ) * (n : ℝ) ^ (σ / 2) * δ ^ (2 * σ)) ≤ volume (⋃ i, Y i)

set_option maxHeartbeats 800000 in
/-- One prism supplies a dense coarse shade and a uniform lower density on each
of its selected cubes. The occupancy parameter `N` can be shared by all prisms. -/
theorem regularized_flat_packet {σ u ε A ηf ηc δ ν s a b N : ℝ}
    (hσ : 0 ≤ σ) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδa : δ ≤ a) (hab : a ≤ b) (hb2 : b ≤ 2) (haSmall : a ≤ 1 / 100)
    (hs : 0 < s) (hνs : ν ≤ s) (hηf : 2 * s ≤ ηf) (hηc : 8 * s ≤ ηc)
    (hN : 0 < N) (e : AffineIsometryEquiv ℝ Space Space)
    (Hfine : FineEstimateAt σ u ε A ηf δ a b (δ ^ (-3 * s)) e)
    {K : ℕ} (hK : 0 < K) (hretBudget : 224 * K * δ ^ s ≤ 1)
    (hcut : 432 * (δ ^ s) ^ K * a * b ≤ δ ^ ν * δ ^ 2 / 2)
    (Kc : ℕ) (hKc : (1 / 2 : ℝ) ^ Kc ≤ δ)
    (hlog : (10 : ℝ) ^ (15 : ℕ) * ((Kc : ℝ) + 1) * δ ^ s ≤ 1)
    {n : ℕ} (hn : 0 < n) (hNn : N ≤ n) (hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ))
    (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hT : ∀ i, Tube δ (x i) (v i) ⊆ e '' StandardPrism a b)
    (hsep : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i)))
    (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYd : ∀ i, ENNReal.ofReal (δ ^ ν * δ ^ 2) ≤ volume (Y i))
    (hraw : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-ν) * n / (a * b)) * volume Q) :
    ∃ S : Finset (Fin 3 → ℤ), S ⊆ gridKeys a ∧
      (∀ z ∈ S, (e '' StandardPrism a b ∩ gridCell a z).Nonempty) ∧
      ENNReal.ofReal (δ ^ ηc * (a * b)) ≤ volume (gridUnion a S) ∧
      ∀ z ∈ S, flatCellDensity σ u ε A δ a b s N * a ^ 3 ≤
        volume.real ((⋃ i, Y i) ∩ gridCell a z) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hρ : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hlam : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ _
  have hκ : 0 < δ ^ (2 * s) := Real.rpow_pos_of_pos hδ _
  obtain ⟨S, t, M, j, hS, hmeet, ht, hM, hj, hret, hInd, hlocal, htotal⟩ :=
    flat_prism_regularization hδ hδa hab hb2 (haSmall.trans (by norm_num)) hlam hρ hK hcut e hn x v Y
      hv hYm hYT (fun i => (hYT i).trans (hball i)) (fun i => (hYT i).trans (hT i)) hYd
  have hbudget := power_retention_budget hδ hδ1 hνs hK hretBudget
  have hret' : δ ^ (2 * s) * (n : ℝ) ≤ M :=
    (mul_le_mul_of_nonneg_right hbudget.1 (Nat.cast_nonneg n)).trans hret
  have hNM : δ ^ (2 * s) * N ≤ M :=
    (mul_le_mul_of_nonneg_left hNn hκ.le).trans hret'
  have hMn : M ≤ n := by simpa using Fintype.card_le_of_injective j hj
  have hMmax : (M : ℝ) ≤ δ ^ (-100 : ℝ) := (Nat.cast_le.mpr hMn).trans hnmax
  let Z := fun i => Y (j i) ∩ gridUnion a S
  have hZmeas : ∀ i, MeasurableSet (Z i) := fun i => (hYm (j i)).inter (gridUnion_measurable a S)
  have hZT : ∀ i, Z i ⊆ Tube δ (x (j i)) (v (j i)) := fun i => inter_subset_left.trans (hYT (j i))
  have hZgrid : ∀ i, Z i ⊆ gridUnion a S := fun _ => inter_subset_right
  have hZden : ∀ i, ENNReal.ofReal (δ ^ (2 * s) * δ ^ 2) ≤ volume (Z i) := fun i =>
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hbudget.2 (sq_nonneg δ))).trans (hInd i)
  have hcoef := power_raw_count_budget hδ hδ1 hνs (Nat.cast_nonneg n) hret'
  have hraw' : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x (j i)) (v (j i)) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (δ ^ (-3 * s) * M / (a * b)) * volume Q := by
    intro Q hQ
    have hcount := WangZahlLot.Obl.wz_tower_balanced_refinement.count_restrict j hj
      (fun i => Tube δ (x i) (v i) ⊆ Q)
    exact ((ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hcount)).trans (hraw Q hQ)).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hcoef (mul_pos ha hb).le)) le_rfl)
  have hLf : 1 ≤ δ ^ (-3 * s) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcoarse := flat_cordoba_density hδ hδa hab hb2 haSmall hκ hLf e hM
    (x ∘ j) (v ∘ j) Z S (fun i => hv (j i)) (fun i => hT (j i)) hZT hZgrid hZden hraw' Kc hKc
  have hcoarse' : ENNReal.ofReal (δ ^ ηc * (a * b)) ≤ volume (gridUnion a S) :=
    (ENNReal.ofReal_le_ofReal (cordoba_power_budget hδ hδ1 ha hb hηc Kc hlog)).trans hcoarse
  have hZfine : ∀ i, ENNReal.ofReal (δ ^ ηf * δ ^ 2) ≤ volume (Z i) := fun i =>
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηf) (sq_nonneg δ))).trans (hZden i)
  have hfine := Hfine M (x ∘ j) (v ∘ j) Z hM hMmax (fun i => hv (j i))
    (fun i => hball (j i)) (fun i => hT (j i)) (fun i k hik => hsep _ _ (hj.ne hik)) hZmeas hZT hZfine hraw'
  have hZfin : volume (⋃ i, Z i) ≠ ⊤ :=
    ne_top_of_le_ne_top (gridUnion_volume_ne_top ha S) (measure_mono (iUnion_subset hZgrid))
  have hfineReal := (ENNReal.ofReal_le_iff_le_toReal hZfin).mp hfine
  have hsmallFine : A * δ ^ ε * (δ / a) ^ u * (δ ^ (-3 * s))⁻¹ * (a * b) ^ (1 - σ) *
      (δ ^ (2 * s) * N) ^ (σ / 2) * δ ^ (2 * σ) ≤ volume.real (⋃ i, Z i) := by
    apply le_trans _ hfineReal
    gcongr
  have ht0 : flatCellDensity σ u ε A δ a b s N ≤ t := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 432 * a * b)).mp
    rw [flat_cell_factorization hA hδ ha hb hN]
    exact (mul_le_mul_of_nonneg_left hsmallFine hρ.le).trans htotal
  refine ⟨S, hS, hmeet, hcoarse', ?_⟩
  intro z hz
  exact (mul_le_mul_of_nonneg_right ht0 (by positivity)).trans (hlocal z hz)

end WangZahlLot.Obl.wz_flat_factored_improvement
