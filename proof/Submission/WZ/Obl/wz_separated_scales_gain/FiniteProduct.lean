-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.FiniteProduct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.AssemblyHelpers

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

set_option maxHeartbeats 1200000 in
/-- The three-scale geometric argument, leaving only explicit scalar admissibility conditions. -/
theorem finite_three_scale_product {σ ω u : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hu : 0 ≤ u) (hD : EstimateD σ ω) (hE : EstimateE σ u) {e : ℝ} (he : 0 < e) :
    ∃ A ηF ηM ηO : ℝ, 0 < A ∧ 0 < ηF ∧ 0 < ηM ∧ 0 < ηO ∧
      ∀ δ lam θ R ζ₁ ζ₂ : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      0 < θ → 0 < R → R ≤ 1 → 0 ≤ ζ₂ →
      ∀ K : ℕ, 0 < K →
      (∀ τ ρ : ℝ, δ ≤ τ → τ < ρ → ρ ≤ 1 → τ ≤ δ ^ ζ₁ * ρ →
        ScaleConditions δ τ ρ lam θ (δ ^ (-ζ₂)) R ηF ηM ηO K) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ unitBall) →
      (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i)) →
      SeparatedStructure ζ₁ ζ₂ δ n x v →
      ∃ τ ρ : ℝ, 0 < τ ∧ 0 < ρ ∧ τ ≤ δ ^ ζ₁ * ρ ∧
        ENNReal.ofReal (A / K ^ 5 * lam ^ 3 * θ ^ 2 * R ^ 4 * (δ ^ (-ζ₂))⁻¹ ^ 4 *
          δ ^ (u + e) * (ρ / τ) ^ (u - ω) * ((n : ℝ) * δ ^ 4) ^ (σ / 2)) ≤
            volume (⋃ i, Y i) := by
  obtain ⟨AF, ηF, hAF, hηF, HF⟩ := uniform_fine_cells hσ0 hσ1 hu hE he
  obtain ⟨AM, ηM, hAM, hηM, HM⟩ := middle_cells hσ0 (by linarith) hD he
  obtain ⟨AO, ηO, hAO, hηO, HO⟩ := uniform_outer_estimate hσ0 hσ1 hu hE he
  let A := AF * AM * AO / (2048 ^ 3 * 4096 ^ 2)
  refine ⟨A, ηF, ηM, ηO, by dsimp [A]; positivity, hηF, hηM, hηO, ?_⟩
  intro δ lam θ R ζ₁ ζ₂ hδ hδ1 hlam hlam1 hθ hR hR1 hζ₂ K hK hconditions
    n x v Y hn hv hB hover hYm hYT hind hSB
  obtain ⟨τ, ρ, hδτ, hτρ, hρ1, hsep, p, y, vP, q, z, vR, hvP, hvR, hPover, hRover,
    hcoverF, hnonemptyF, hcoverM, hnonemptyM, hbalF, hbalM, hrelF, hKT, hsat, hrelO⟩ := hSB
  have hτ : 0 < τ := hδ.trans_le hδτ
  have hρ : 0 < ρ := hτ.trans hτρ
  have hτ1 : τ ≤ 1 := hτρ.le.trans hρ1
  let L := δ ^ (-ζ₂)
  have hL : 1 ≤ L := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLi : L⁻¹ = δ ^ ζ₂ := by dsimp [L]; rw [Real.rpow_neg hδ.le, inv_inv]
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hc := hconditions τ ρ hδτ hτρ hρ1 hsep
  obtain ⟨j0, _, _⟩ := hcoverF ⟨0, hn⟩
  have hp : 0 < p := Fin.pos j0
  obtain ⟨l0, _, _⟩ := hcoverM j0
  have hq : 0 < q := Fin.pos l0
  have hposF (j : Fin p) : 0 < Set.ncard {i | tube δ (x i) (v i) ⊆ tube τ (y j) (vP j)} :=
    (Set.ncard_pos (Set.toFinite _)).mpr (hnonemptyF j)
  have hposM (l : Fin q) : 0 < Set.ncard {j | tube τ (y j) (vP j) ⊆ tube ρ (z l) (vR l)} :=
    (Set.ncard_pos (Set.toFinite _)).mpr (hnonemptyM l)
  obtain ⟨N, hN, hNle, _, hcoverN⟩ := balanced_cover_minimum hp
    (fun i j => tube δ (x i) (v i) ⊆ tube τ (y j) (vP j)) hL0.le
    (fun i => (hcoverF i).exists) hposF hbalF
  obtain ⟨M, hM, hMle, hcoverM', hsatM⟩ := balanced_cover_minimum_lower hq
    (fun j l => tube τ (y j) (vP j) ⊆ tube ρ (z l) (vR l)) hL0.le
    (fun j => (hcoverM j).exists) hposM hbalM hsat
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hM0 : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hq0 : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hcard : (n : ℝ) ≤ L ^ 2 * ((N : ℝ) * M * q) := by
    have hh := mul_le_mul_of_nonneg_right hcoverM' (by positivity : 0 ≤ L * N)
    nlinarith only [hcoverN, hh]
  have hsatM' : L⁻¹ ≤ (M : ℝ) * (τ / ρ) ^ 2 := by
    rw [← hLi] at hsatM
    have hh := mul_le_mul_of_nonneg_right hsatM (sq_nonneg (τ / ρ))
    have hid : L⁻¹ * (ρ / τ) ^ 2 * (τ / ρ) ^ 2 = L⁻¹ := by field_simp
    rwa [hid] at hh
  have hPB (j : Fin p) : tube τ (y j) (vP j) ⊆ ball (0 : Space) 5 := by
    apply tube_subset_ball_five hτ1 (hvP j)
    exact packet_meets_ball hδ x v hB _ (by rw [packetSize_eq]; exact hposF j)
  have hRB (l : Fin q) : tube ρ (z l) (vR l) ⊆ ball (0 : Space) 5 := by
    apply tube_subset_ball_five hρ1 (hvR l)
    obtain ⟨j, hj⟩ := hnonemptyM l
    obtain ⟨i, hi⟩ := hnonemptyF j
    have hx : x i ∈ tube δ (x i) (v i) := self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
    exact ⟨x i, hj (hi hx), hB i hx⟩
  let F (k : ℝ) := AF * lam * θ / K * R ^ 2 * (δ / τ) ^ (u + e) * L⁻¹ *
    (k * (δ / τ) ^ 4) ^ (σ / 2)
  have hF0 : 0 ≤ F N := by dsimp [F]; positivity
  have hexF (j : Fin p) : ∃ s : Finset (Fin 3 → ℤ),
      (∀ c ∈ s, (tube τ (y j) (vP j) ∩ gridCell τ c).Nonempty) ∧
      ENNReal.ofReal (lam / (32 * K) * τ ^ 2) ≤ volume (gridUnion τ s) ∧
      ∀ c ∈ s, ENNReal.ofReal (F N) * volume (gridCell τ c) ≤ volume ((⋃ i, Y i) ∩ gridCell τ c) := by
    let g := packetIndex δ x v (tube τ (y j) (vP j))
    have hg := packetIndex_injective δ x v (tube τ (y j) (vP j))
    have hNg : 0 < packetSize δ x v (tube τ (y j) (vP j)) := by rw [packetSize_eq]; exact hposF j
    have hrel : RelativeCount τ L δ (fun i => x (g i)) (fun i => v (g i)) := by
      intro W hW
      dsimp [g]
      rw [packetIndex_count, packetSize_eq]
      exact hrelF j W hW
    obtain ⟨s, hmeet, hmass, hlocal⟩ := HF τ δ lam θ L R hδ hδτ hτ1 hlam hθ hL hR hR1
      K hK hc.fineCut hc.fineDensity _ (fun i => x (g i)) (fun i => v (g i)) (fun i => Y (g i))
      (y j) (vP j) hNg (hvP j) (fun i => hv (g i)) (fun i => hB (g i))
      (packetIndex_contained δ x v (tube τ (y j) (vP j)))
      (fun i k hik => hover (g i) (g k) (hg.ne hik)) (fun i => hYm (g i))
      (fun i => hYT (g i)) (fun i => hind (g i)) hrel
    refine ⟨s, hmeet, hmass, ?_⟩
    intro c hcs
    have hFN : F N ≤ F (packetSize δ x v (tube τ (y j) (vP j))) := by
      dsimp [F]
      gcongr
      rw [packetSize_eq]
      exact_mod_cast hNle j
    calc
      _ ≤ ENNReal.ofReal (F (packetSize δ x v (tube τ (y j) (vP j)))) * volume (gridCell τ c) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hFN) le_rfl
      _ ≤ volume ((⋃ i, Y (g i)) ∩ gridCell τ c) := hlocal c hcs
      _ ≤ _ := measure_mono (inter_subset_inter_left _ (iUnion_subset fun i => subset_iUnion Y (g i)))
  choose sF hmeetF hmassF hlocalF using hexF
  let C : Fin p → Set Space := fun j => paddedShading τ (sF j) (y j) (vP j)
  let lam1 := lam / (2048 * K)
  have hlam1pos : 0 < lam1 := by dsimp [lam1]; positivity
  have hlam1le : lam1 ≤ 1 := by dsimp [lam1]; apply (div_le_one (by positivity)).mpr; linarith
  have hCm : ∀ j, MeasurableSet (C j) := fun j => paddedShading_measurable _ _ _ _
  have hCT : ∀ j, C j ⊆ tube τ (y j) (vP j) := fun _ => inter_subset_left
  have hCden : ∀ j, ENNReal.ofReal (lam1 * τ ^ 2) ≤ volume (C j) := fun j =>
    paddedShading_density hτ _ _ _ (hmeetF j) (hmassF j)
  have hprodF : ENNReal.ofReal (F N) * volume (⋃ j, C j) ≤ 4096 * volume (⋃ i, Y i) :=
    padded_union_product hτ sF y vP _ (MeasurableSet.iUnion hYm) _ hlocalF
  let G (k : ℝ) := AM * lam1 * θ / K * (τ / ρ) ^ (ω + e) *
    ((k * (τ / ρ) ^ 2) * (k * (τ / ρ)) ^ (-σ))
  have hG0 : 0 ≤ G M := by dsimp [G]; positivity
  have hexM (l : Fin q) : ∃ s : Finset (Fin 3 → ℤ),
      (∀ c ∈ s, (tube ρ (z l) (vR l) ∩ gridCell ρ c).Nonempty) ∧
      ENNReal.ofReal (lam1 / (32 * K) * ρ ^ 2) ≤ volume (gridUnion ρ s) ∧
      ∀ c ∈ s, ENNReal.ofReal (G M) * volume (gridCell ρ c) ≤ volume ((⋃ j, C j) ∩ gridCell ρ c) := by
    let g := packetIndex τ y vP (tube ρ (z l) (vR l))
    have hg := packetIndex_injective τ y vP (tube ρ (z l) (vR l))
    have hNg : 0 < packetSize τ y vP (tube ρ (z l) (vR l)) := by rw [packetSize_eq]; exact hposM l
    have hconv : ConvexCount τ L (fun i => y (g i)) (fun i => vP (g i)) := by
      intro W hW
      dsimp [g]
      rw [packetIndex_count]
      exact hKT l W hW
    have hsatg : L⁻¹ ≤ (packetSize τ y vP (tube ρ (z l) (vR l)) : ℝ) * (τ / ρ) ^ 2 := by
      apply hsatM'.trans
      gcongr
      rw [packetSize_eq]
      exact_mod_cast hMle l
    have hslab := (middle_slab_bound hτ hρ hL0 hlam1pos (Nat.cast_pos.mpr hNg) hK hsatg).trans hc.middleSlab
    obtain ⟨s, hmeet, hmass, hlocal⟩ := HM ρ τ lam1 θ L hτ hτρ.le hρ1 hlam1pos hlam1le hθ hL0.le
      K hK hc.middleCut hc.middleDensity hc.middleConvex _ (fun i => y (g i)) (fun i => vP (g i))
      (fun i => C (g i)) (z l) (vR l) hNg hslab (hvR l) (fun i => hvP (g i))
      (packetIndex_contained τ y vP (tube ρ (z l) (vR l)))
      (fun i k hik => hPover (g i) (g k) (hg.ne hik)) (fun i => hCm (g i))
      (fun i => hCT (g i)) (fun i => (hCT (g i)).trans (hPB (g i))) (fun i => hCden (g i)) hconv
    refine ⟨s, hmeet, hmass, ?_⟩
    intro c hcs
    have hGM : G M ≤ G (packetSize τ y vP (tube ρ (z l) (vR l))) := by
      apply mul_le_mul_of_nonneg_left (middle_weight_mono hM0 (div_pos hτ hρ) _ (by linarith)) (by positivity)
      rw [packetSize_eq]
      exact_mod_cast hMle l
    calc
      _ ≤ ENNReal.ofReal (G (packetSize τ y vP (tube ρ (z l) (vR l)))) * volume (gridCell ρ c) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hGM) le_rfl
      _ ≤ volume ((⋃ i, C (g i)) ∩ gridCell ρ c) := by
        convert hlocal c hcs using 1 <;> dsimp [G] <;> congr 2 <;> ring
      _ ≤ _ := measure_mono (inter_subset_inter_left _ (iUnion_subset fun i => subset_iUnion C (g i)))
  choose sM hmeetM hmassM hlocalM using hexM
  let B : Fin q → Set Space := fun l => paddedShading ρ (sM l) (z l) (vR l)
  let lam2 := lam1 / (2048 * K)
  have hlam2 : 0 < lam2 := by dsimp [lam2]; positivity
  have hlam2le : lam2 ≤ 1 := by dsimp [lam2]; apply (div_le_one (by positivity)).mpr; linarith
  have hprodM : ENNReal.ofReal (G M) * volume (⋃ l, B l) ≤ 4096 * volume (⋃ j, C j) :=
    padded_union_product hρ sM z vR _ (MeasurableSet.iUnion hCm) _ hlocalM
  let O := AO * lam2 * R ^ 2 * ρ ^ (u + e) * L⁻¹ * ((q : ℝ) * ρ ^ 4) ^ (σ / 2)
  have hO0 : 0 ≤ O := by dsimp [O]; positivity
  have houter : ENNReal.ofReal O ≤ volume (⋃ l, B l) := by
    apply HO ρ lam2 L R hρ hρ1 hlam2 hlam2le hL hR hR1 hc.outerDensity q z vR B hq hvR hRB hRover
      (fun l => paddedShading_measurable _ _ _ _) (fun _ => inter_subset_left)
      (fun l => paddedShading_density hρ _ _ _ (hmeetM l) (hmassM l))
    intro W hW
    simpa only [one_pow, mul_one] using hrelO W hW
  have hfull : ENNReal.ofReal (F N * G M * O) ≤ 4096 ^ 2 * volume (⋃ i, Y i) := by
    calc
      _ = ENNReal.ofReal (F N) * (ENNReal.ofReal (G M) * ENNReal.ofReal O) := by
        rw [← ENNReal.ofReal_mul hG0, ← ENNReal.ofReal_mul hF0]; congr 1; ring
      _ ≤ ENNReal.ofReal (F N) * (4096 * volume (⋃ j, C j)) :=
        mul_le_mul' le_rfl ((mul_le_mul' le_rfl houter).trans hprodM)
      _ = 4096 * (ENNReal.ofReal (F N) * volume (⋃ j, C j)) := by ring
      _ ≤ 4096 * (4096 * volume (⋃ i, Y i)) := mul_le_mul' le_rfl hprodF
      _ = _ := by ring
  have hweight := tower_weight_lower hN0 hM0 hq0 (Nat.cast_nonneg n) hδ hτ hρ hL hσ0 hσ1 hcard hsatM'
  let P := AF * AM * AO / (2048 ^ 3 * K ^ 5) * lam ^ 3 * θ ^ 2 * R ^ 4 * L⁻¹ ^ 2 *
    δ ^ (u + e) * (ρ / τ) ^ (u - ω)
  have hidentity : F N * G M * O = P * ((N * (δ / τ) ^ 4) ^ (σ / 2) *
      (((M : ℝ) * (τ / ρ) ^ 2) * ((M : ℝ) * (τ / ρ)) ^ (-σ)) *
      ((q : ℝ) * ρ ^ 4) ^ (σ / 2)) := by
    have hscale := tower_scale_identity hδ hτ hρ u ω e
    dsimp [F, G, O, P, lam1, lam2]
    calc
      _ = (AF * AM * AO / (2048 ^ 3 * K ^ 5) * lam ^ 3 * θ ^ 2 * R ^ 4 * L⁻¹ ^ 2) *
          ((δ / τ) ^ (u + e) * (τ / ρ) ^ (ω + e) * ρ ^ (u + e)) *
          ((N * (δ / τ) ^ 4) ^ (σ / 2) *
            (((M : ℝ) * (τ / ρ) ^ 2) * ((M : ℝ) * (τ / ρ)) ^ (-σ)) *
            ((q : ℝ) * ρ ^ 4) ^ (σ / 2)) := by ring
      _ = _ := by rw [hscale]; ring
  rw [hidentity] at hfull
  have hfull' := (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hweight
    (by dsimp [P]; positivity))).trans hfull
  refine ⟨τ, ρ, hτ, hρ, hsep, ?_⟩
  have heq : P * (L⁻¹ ^ 2 * ((n : ℝ) * δ ^ 4) ^ (σ / 2)) = 4096 ^ 2 *
      (A / K ^ 5 * lam ^ 3 * θ ^ 2 * R ^ 4 * L⁻¹ ^ 4 * δ ^ (u + e) *
        (ρ / τ) ^ (u - ω) * ((n : ℝ) * δ ^ 4) ^ (σ / 2)) := by dsimp [P, A]; ring
  rw [heq] at hfull'
  exact ofReal_cancel_factor (by norm_num : (0 : ℝ) < 4096 ^ 2) (by simpa using hfull')

end WangZahlLot.Obl.wz_separated_scales_gain
