-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FineCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineNormalized
import Submission.WZ.Obl.wz_nonflat_factored_improvement.PrismRegularization

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

/-- The fine estimate gives a uniform lower union density in the chosen coarse cells. -/
theorem fine_cell_estimate {σ u : ℝ} (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A η : ℝ, 0 < A ∧ 0 < η ∧
      ∀ a b δ lam ρ m L : ℝ, 0 < δ → δ ≤ a → a ≤ b → b ≤ 1 →
      0 < lam → 0 < ρ → 1 ≤ m → 1 ≤ L →
      ∀ K : ℕ, 0 < K → 288 * ρ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2 →
      (fineRadius δ b) ^ η ≤ fineContraction * lam / (64 * K) →
      ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
        (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i, tube δ (x i) (v i) ⊆ e '' standardPrism a b) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) → ConvexCount δ m x v →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * (a * b)) ≤
          ENNReal.ofReal (L * n) * volume U) →
      ∃ s : Finset (Fin 3 → ℤ), s ⊆ gridKeys b ∧
        (∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty) ∧
        ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
        ∀ z ∈ s,
          ENNReal.ofReal (A * lam * ρ / K * (δ / b) ^ (u + ε) * m⁻¹ *
            ((n : ℝ) * (δ / b) ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ)) *
              volume (gridCell b z) ≤ volume ((⋃ i, Y i) ∩ gridCell b z) := by
  obtain ⟨A, η, hA, hη, H⟩ := fine_estimate_normalized hE hε
  refine ⟨A / 64512, η, by positivity, hη, ?_⟩
  intro a b δ lam ρ m L hδ hδa hab hb1 hlam hρ hm hL K hK hcut hden e n x v Y
    hn hv hB hT hover hYm hYT hind hconv hrel
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  obtain ⟨s, t, N, j, hs, hmeet, ht, hN, hj, hsize, hInd, hcoarse, hlocal, htotal⟩ :=
    prism_shading_regularization hδ (hδa.trans hab) hab hb1 hlam hρ hK hcut e hn x v Y
      hv hYm hYT (fun i => (hYT i).trans (hB i)) (fun i => (hYT i).trans (hT i)) hind
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNn : (N : ℝ) ≤ n := by
    exact_mod_cast (show N ≤ n by simpa using Fintype.card_le_of_injective j hj)
  let L' := L * n / N
  have hL' : 1 ≤ L' := by
    apply (le_div_iff₀ hN0).mpr
    have hh := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg n)
    linarith
  have hLprod : L' * N = L * n := by dsimp [L']; field_simp
  let Z : Fin N → Set Space := fun i => Y (j i) ∩ gridUnion b s
  have hZmeas : ∀ i, MeasurableSet (Z i) := fun i => (hYm (j i)).inter (gridUnion_measurable b s)
  have hZsub : ∀ i, Z i ⊆ tube δ (x (j i)) (v (j i)) := fun i =>
    inter_subset_left.trans (hYT (j i))
  have hrel' : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal ((Set.ncard {i | tube δ (x (j i)) (v (j i)) ⊆ U} : ℝ) * (a * b)) ≤
        ENNReal.ofReal (L' * N) * volume U := by
    intro U hU
    rw [hLprod]
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (subfamily_count j hj (fun i => tube δ (x i) (v i) ⊆ U)))
        (by positivity))).trans (hrel U hU)
  have hden' : (fineRadius δ b) ^ η ≤ fineContraction * (lam / (4 * K)) / 16 := by
    convert hden using 1 <;> ring
  have hFine := H a b δ (lam / (4 * K)) m L' hδ hδa hab hb1 hm hL'
    (by positivity) hden' e N (fun i => x (j i)) (fun i => v (j i)) Z hN
    (fun i => hv (j i)) (fun i => hT (j i))
    (fun i k hik => hover (j i) (j k) (fun he => hik (hj he))) hZmeas hZsub hInd
    (convexCount_subfamily j hj hconv) hrel'
  have hbr : m ^ (-(3 / 2 : ℝ)) * L' * ((N : ℝ) * δ / a) =
      m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a) := by
    dsimp [L']
    field_simp
  rw [hbr] at hFine
  have hFfin : volume (⋃ i, Z i) ≠ ⊤ := ne_top_of_le_ne_top
    (gridUnion_volume_ne_top hb s) (measure_mono (Set.iUnion_subset (fun _ => inter_subset_right)))
  have hfineR : A * (lam / (224 * K)) * (δ / b) ^ (u + ε) * m⁻¹ *
      ((n : ℝ) * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ) ≤
        volume.real (⋃ i, Z i) := by
    apply le_trans _ ((ENNReal.ofReal_le_iff_le_toReal hFfin).mp hFine)
    have hpos : 0 ≤ A * (δ / b) ^ (u + ε) * m⁻¹ * δ ^ 2 *
        (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ) := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hsize hpos]
  let D := (A / 64512) * lam * ρ / K * (δ / b) ^ (u + ε) * m⁻¹ *
    ((n : ℝ) * (δ / b) ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDt : D ≤ t := by
    have he : (288 * b ^ 2) * D = ρ * (A * (lam / (224 * K)) * (δ / b) ^ (u + ε) * m⁻¹ *
        ((n : ℝ) * δ ^ 2) * (m ^ (-(3 / 2 : ℝ)) * L * ((n : ℝ) * δ / a)) ^ (-σ)) := by
      dsimp [D]
      field_simp
      ring
    have hh := (mul_le_mul_of_nonneg_left hfineR hρ.le).trans htotal
    rw [← he, mul_comm t] at hh
    exact (mul_le_mul_iff_right₀ (by positivity : 0 < 288 * b ^ 2)).mp hh
  refine ⟨s, hs, hmeet, hcoarse, ?_⟩
  intro z hz
  change ENNReal.ofReal D * volume (gridCell b z) ≤ _
  rw [gridCell_volume hb.le, ← ENNReal.ofReal_mul hD0]
  apply (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top (gridCell_volume_ne_top hb z) (measure_mono inter_subset_right))).mpr
  exact (mul_le_mul_of_nonneg_right hDt (by positivity)).trans (hlocal z hz)

end WangZahlLot.Obl.wz_nonflat_factored_improvement
