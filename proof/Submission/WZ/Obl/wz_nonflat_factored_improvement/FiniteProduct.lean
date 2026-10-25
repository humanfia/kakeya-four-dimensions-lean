-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.FiniteProduct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.FineCells
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseEstimate
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseFamily
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem gridUnion_family (b : ℝ) {M : ℕ} (s : Fin M → Finset (Fin 3 → ℤ)) :
    gridUnion b (Finset.univ.biUnion s) = ⋃ i, gridUnion b (s i) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hzs, hpz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hzs
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hi, hpz⟩⟩⟩
  · intro hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hi
    obtain ⟨hzs, hpz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hzs⟩, hpz⟩⟩

set_option maxHeartbeats 500000 in
/-- The complete geometric two-scale argument with explicit scalar admissibility conditions. -/
theorem finite_two_scale_product {σ ω u : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : EstimateD σ ω) (hE : EstimateE σ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ηD ηE : ℝ, 0 < A ∧ 0 < ηD ∧ 0 < ηE ∧
      ∀ a b δ lam ρ m D l : ℝ,
      0 < δ → δ ≤ a → a ≤ b → b ≤ 1 → 0 < lam → 0 < ρ → 1 ≤ m → 1 ≤ D → 0 ≤ l →
      ∀ K : ℕ, 0 < K → 288 * ρ ^ K * b ^ 2 ≤ lam * δ ^ 2 / 2 →
      (fineRadius δ b) ^ ηE ≤ fineContraction * lam / (64 * K) →
      (coarseRadius b) ^ ηD ≤ coarseContraction * lam / (4608 * K) →
      coarseConvexCoefficient a b D ≤ (coarseRadius b) ^ (-ηD) →
      coarseSlabCoefficient a b D l ≤ (coarseRadius b) ^ (-ηD) →
      ∀ (n q : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space)
        (e : Fin q → AffineIsometryEquiv ℝ Space Space),
      0 < n → 0 < q → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) →
      ConvexCount δ m x v → SlabCount δ l x v →
      (∀ i, ∃ j, tube δ (x i) (v i) ⊆ e j '' standardPrism a b) →
      (∀ i, (Set.ncard {j | tube δ (x i) (v i) ⊆ e j '' standardPrism a b} : ℝ) ≤ D) →
      (∀ j, 0 < Set.ncard {i | tube δ (x i) (v i) ⊆ e j '' standardPrism a b}) →
      (∀ j k, (Set.ncard {i | tube δ (x i) (v i) ⊆ e j '' standardPrism a b} : ℝ) ≤
        D * Set.ncard {i | tube δ (x i) (v i) ⊆ e k '' standardPrism a b}) →
      PrismCount a b D (fun j => e j '' standardPrism a b) →
      (∀ j U, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ e j '' standardPrism a b ∧
          tube δ (x i) (v i) ⊆ U} : ℝ) * (a * b)) ≤
        ENNReal.ofReal (D * Set.ncard {i | tube δ (x i) (v i) ⊆ e j '' standardPrism a b}) * volume U) →
      ENNReal.ofReal (A * lam * ρ / K * (D * b / a) ^ (-σ) * coarseMassFraction a b D *
        δ ^ (u + ε) * b ^ (ω - u) * weight σ δ m n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨B, ηD, hB, hηD, HD⟩ := coarse_cell_estimate hD hε
  obtain ⟨A, ηE, hA, hηE, HE⟩ := fine_cell_estimate hE hε
  refine ⟨A * B, ηD, ηE, mul_pos hA hB, hηD, hηE, ?_⟩
  intro a b δ lam ρ m D l hδ hδa hab hb1 hlam hρ hm hD1 hl K hK hcut hfden hcden
    hcc hsc n q x v Y e hn hq hv hball hover hYm hYT hind hconv hslab hcover hdegree hpos hbal hprism hrel
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  obtain ⟨N, hN, hNle, hNupper, hcoverN⟩ := balanced_cover_minimum hq
    (fun i j => tube δ (x i) (v i) ⊆ e j '' standardPrism a b) hD0.le hcover hpos hbal
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  let F : ℝ → ℝ := fun k => A * lam * ρ / K * (δ / b) ^ (u + ε) * m⁻¹ *
    (k * (δ / b) ^ 2) * (m ^ (-(3 / 2 : ℝ)) * D * (k * δ / a)) ^ (-σ)
  have hF0 : 0 ≤ F N := by dsimp [F]; positivity
  have hFmono {k : ℝ} (hk : (N : ℝ) ≤ k) : F N ≤ F k := by
    have hh := count_power_mono (C := m ^ (-(3 / 2 : ℝ)) * D * δ / a)
      (by positivity) hN0 hk hσ1
    have he (t : ℝ) : m ^ (-(3 / 2 : ℝ)) * D * δ / a * t =
        m ^ (-(3 / 2 : ℝ)) * D * (t * δ / a) := by ring
    simp only [he] at hh
    have hp : 0 ≤ A * lam * ρ / K * (δ / b) ^ (u + ε) * m⁻¹ * (δ / b) ^ 2 := by positivity
    dsimp [F]
    nlinarith only [mul_le_mul_of_nonneg_left hh hp]
  have hex (j : Fin q) : ∃ s : Finset (Fin 3 → ℤ), s ⊆ gridKeys b ∧
      (∀ z ∈ s, (e j '' standardPrism a b ∩ gridCell b z).Nonempty) ∧
      ENNReal.ofReal (lam / (32 * K) * b ^ 2) ≤ volume (gridUnion b s) ∧
      ∀ z ∈ s, ENNReal.ofReal (F N) * volume (gridCell b z) ≤ volume ((⋃ i, Y i) ∩ gridCell b z) := by
    let g := packetIndex δ x v (e j '' standardPrism a b)
    have hg := packetIndex_injective δ x v (e j '' standardPrism a b)
    have hNg : 0 < packetSize δ x v (e j '' standardPrism a b) := by rw [packetSize_eq]; exact hpos j
    have hrel' : ∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((Set.ncard {i | tube δ (x (g i)) (v (g i)) ⊆ U} : ℝ) * (a * b)) ≤
          ENNReal.ofReal (D * packetSize δ x v (e j '' standardPrism a b)) * volume U := by
      intro U hU
      dsimp [g]
      rw [packetIndex_count, packetSize_eq]
      exact hrel j U hU
    obtain ⟨s, hs, hmeet, hmass, hloc⟩ := HE a b δ lam ρ m D hδ hδa hab hb1 hlam hρ hm hD1
      K hK hcut hfden (e j) _ (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i))
      hNg (fun i => hv (g i)) (fun i => hball (g i))
      (packetIndex_contained δ x v (e j '' standardPrism a b))
      (fun i k hik => hover (g i) (g k) (hg.ne hik)) (fun i => hYm (g i))
      (fun i => hYT (g i)) (fun i => hind (g i)) (convexCount_subfamily g hg hconv) hrel'
    refine ⟨s, hs, hmeet, hmass, ?_⟩
    intro z hz
    have hh : F N ≤ F (packetSize δ x v (e j '' standardPrism a b)) :=
      hFmono (by rw [packetSize_eq]; exact Nat.cast_le.mpr (hNle j))
    calc
      _ ≤ ENNReal.ofReal (F (packetSize δ x v (e j '' standardPrism a b))) * volume (gridCell b z) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hh) le_rfl
      _ ≤ volume ((⋃ i, Y (g i)) ∩ gridCell b z) := hloc z hz
      _ ≤ _ := measure_mono (Set.inter_subset_inter_left _
        (Set.iUnion_subset (fun i => Set.subset_iUnion Y (g i))))
  choose s hs hmeet hmass hloc using hex
  obtain ⟨M, j, z, w, hM, hj, hw, hballC, hsep, hbig, hconvC, hslabC, hMN⟩ :=
    coarse_factored_family ha hab hb1 hδ hD0 hl hq hN x v e hball hNle hcoverN hdegree hprism hslab
  let C := fun i : Fin M => gridUnion b (s (j i))
  have hcoverC : ∀ i, (fun p : Space => coarseContraction • p) '' C i ⊆ tube (coarseRadius b) (z i) (w i) :=
    fun i => (Set.image_mono (gridUnion_subset_prism_neighborhood hb _ (e (j i)) (hmeet (j i)))).trans (hbig i)
  have hcoarse := HD b lam hb hb1 hlam K hK hcden M z w C hM hw hballC hsep
    (fun i => gridUnion_measurable b (s (j i))) hcoverC (fun i => hmass (j i))
    (convexCount_mono hcc hconvC) (slabCount_mono hsc hslabC)
  classical
  let all := Finset.univ.biUnion (fun i : Fin M => s (j i))
  have hall : gridUnion b all = ⋃ i, C i := gridUnion_family b (fun i => s (j i))
  have hprod := gridUnion_product hb all (⋃ i, Y i) (MeasurableSet.iUnion hYm) (ENNReal.ofReal (F N)) (by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    exact hloc (j i) z hi)
  rw [hall] at hprod
  have hfull : ENNReal.ofReal ((B * b ^ (ω + ε) * ((M : ℝ) * b ^ 2) * ((M : ℝ) * b) ^ (-σ)) * F N) ≤
      volume (⋃ i, Y i) := by
    calc
      _ = ENNReal.ofReal (F N) * ENNReal.ofReal
          (B * b ^ (ω + ε) * ((M : ℝ) * b ^ 2) * ((M : ℝ) * b) ^ (-σ)) := by
        rw [← ENNReal.ofReal_mul hF0]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (F N) * volume (⋃ i, C i) := mul_le_mul' le_rfl hcoarse
      _ ≤ _ := hprod
  dsimp [F] at hfull
  rw [exact_two_scale_product hδ hb ha hm0 hD0 (Nat.cast_pos.mpr hM) hN0] at hfull
  have hfrac : 0 < coarseMassFraction a b D := by
    dsimp [coarseMassFraction]
    exact div_pos (mul_pos coarseFraction_pos (div_pos ha hb)) (sq_pos_of_pos hD0)
  have hfrac1 : coarseMassFraction a b D ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hD0)).mpr
    calc
      _ ≤ 1 * 1 := mul_le_mul coarseFraction_le_one ((div_le_one hb).mpr hab)
        (by positivity) (by norm_num)
      _ ≤ D ^ 2 := by nlinarith
  have hweight := realWeight_fraction hδ hm0 (Nat.cast_pos.mpr hn) hfrac hfrac1 hMN hσ0 hσ1
  apply (ENNReal.ofReal_le_ofReal ?_).trans hfull
  have hp : 0 ≤ (A * B) * lam * ρ / K * (D * b / a) ^ (-σ) * δ ^ (u + ε) * b ^ (ω - u) := by positivity
  change coarseMassFraction a b D * weight σ δ m n ≤ realWeight σ δ m (M * N) at hweight
  convert mul_le_mul_of_nonneg_left hweight hp using 1 <;> ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
