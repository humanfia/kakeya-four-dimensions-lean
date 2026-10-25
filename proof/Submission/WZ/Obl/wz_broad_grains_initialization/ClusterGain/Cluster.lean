-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain.Cluster.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.ClusterGain.RelativeSlab

/-!
# Cluster gain: the rescaled estimate for one carrier cluster

A cluster `S` of tubes of an admissible family, lying in one carrier `Carrier 6 ρ y w`, with a
`δ^η₀`-dense shading, satisfies the volume bound of `E` at scale `δ/ρ` (accepted o095,
`local_rescaling_carrier_of_estimate`). The global Frostman constant `δ^-η` controls both the
cluster's relative slab constant and its size, so the normalized factor becomes `(nδ)^-σ`.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

namespace WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain

/-- Sums over a cluster reindexed by `orderEmbOfFin`. -/
theorem sum_orderEmb {n : ℕ} (S : Finset (Fin n)) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) (hf : ∀ i, i ∉ S → f i = 0) :
    ∑ j, f (S.orderEmbOfFin rfl j) = ∑ i, f i := by
  have h1 : ∑ j, f (S.orderEmbOfFin rfl j) = ∑ i ∈ S, f i := by
    calc ∑ j, f (S.orderEmbOfFin rfl j) = ∑ s : S, f s :=
          Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
            (fun j => by simp [Finset.coe_orderIsoOfFin_apply])
      _ = ∑ i ∈ S, f i := Finset.sum_coe_sort S f
  rw [h1]
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hf i hi)

/-- The rescaled estimate for one carrier cluster. -/
theorem cluster_estimate {σ ω : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : Interfaces.E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ δ ρ η : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 → 0 ≤ η →
    ∀ (n : ℕ) (x v : Fin n → Space),
    (∀ i, ‖v i‖ = 1) →
    (∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1) →
    (∀ i j, i ≠ j → volume (thickening δ (segment ℝ (x i) (x i + v i)) ∩
        thickening δ (segment ℝ (x j) (x j + v j))) ≤
        1 / 2 * volume (thickening δ (segment ℝ (x i) (x i + v i)))) →
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η)) * volume W) →
    (∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
      ENNReal.ofReal (({i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ)) ≤
        ENNReal.ofReal (δ ^ (-η) * n) *
          volume (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})) →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set Space) (y w : Space), ‖w‖ = 1 → S.Nonempty →
    (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ thickening δ (segment ℝ (x i) (x i + v i))) →
    (∀ i, i ∉ S → Z i = ∅) →
    (∀ i ∈ S, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Carrier 6 ρ y w) →
    ENNReal.ofReal (δ ^ η₀ * S.card * δ ^ 2) ≤ ∑ i, volume (Z i) →
    ENNReal.ofReal (κ * δ ^ (ε + η) * (δ / ρ) ^ ω * (S.card * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Z i) := by
  intro ε hε
  obtain ⟨κR, hκR, ηR, hηR, hR⟩ :=
    Interfaces.local_rescaling_carrier_of_estimate hσ.le hσ2 hω.le hE ε hε
  refine ⟨κR * 20480 ^ (-σ), by positivity, ηR, hηR, ?_⟩
  intro δ ρ η hδ hδ100 hδρ hρ1 hη n x v hv hball hX hK hF S Z y w hw hS hZ hZS hcar hdense
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hδ1 : δ ≤ 1 := by linarith
  set m := S.card with hm
  have hm0 : 0 < m := Finset.card_pos.mpr hS
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  set g : Fin m ↪o Fin n := S.orderEmbOfFin rfl with hg
  have hgS : ∀ j, g j ∈ S := fun j => S.orderEmbOfFin_mem rfl j
  set lg := δ ^ (-η) with hlg
  have hlg0 : 0 ≤ lg := by positivity
  have hlg1 : 1 ≤ lg := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  set lc := max 2560 (20480 * lg * n * ρ / m) with hlc
  have hlc1 : 1 ≤ lc := le_trans (by norm_num) (le_max_left _ _)
  have hslab := cluster_slab_count hδ hρ hρ1 (by norm_num : (0 : ℝ) < 6) (by norm_num) hlg0
    hm0 hv hball hF g g.injective hw (fun j => hcar _ (hgS j))
  have hcount : (m : ℝ) ≤ lg * n * (8 * ρ) := cluster_card_le hρ hlg0 hball hF hw hcar
  have hunion : (⋃ j, Z (g j)) = ⋃ i, Z i := by
    apply Subset.antisymm
    · exact iUnion_subset fun j => subset_iUnion (fun i => Z i) (g j)
    · refine iUnion_subset fun i p hp => ?_
      by_cases hi : i ∈ S
      · have : i ∈ Set.range g := by
          rw [hg, Finset.range_orderEmbOfFin]; exact hi
        obtain ⟨j, rfl⟩ := this
        exact mem_iUnion.mpr ⟨j, hp⟩
      · rw [hZS i hi] at hp; simp at hp
  have hsum : ∑ j, volume (Z (g j)) = ∑ i, volume (Z i) :=
    sum_orderEmb S (fun i => volume (Z i)) (fun i hi => by rw [hZS i hi, measure_empty])
  have h := hR δ ρ hδ hδ100 hδρ hρ1 lg lc hlg1 hlc1 6 (by norm_num) (by norm_num) m
    (fun j => x (g j)) (fun j => v (g j)) (fun j => Z (g j)) y w hm0 hw
    (fun j => ⟨hv _, hcar _ (hgS j), (hZ _).1, (hZ _).2⟩)
    (fun j j' hjj' => hX _ _ (fun h => hjj' (g.injective h)))
    (by
      show ENNReal.ofReal (δ ^ ηR * m * δ ^ 2) ≤ ∑ j, volume (Z (g j))
      rw [hsum]; exact hdense)
    (by
      intro W hW
      refine le_trans ?_ (hK W hW)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold Interfaces.q Interfaces.T
      exact_mod_cast Set.ncard_le_ncard_of_injOn g
        (t := {i | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W})
        (fun j hj => hj) g.injective.injOn (Set.toFinite _))
    hslab
  have h' : ENNReal.ofReal (κR * δ ^ ε * (δ / ρ) ^ ω * lg⁻¹ * (m * δ ^ 2) *
      (lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ)) ^ (-σ)) ≤ volume (⋃ j, Z (g j)) := h
  rw [← hunion]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h'
  have hlginv : lg⁻¹ = δ ^ η := by rw [hlg, Real.rpow_neg hδ.le, inv_inv]
  have hΦpos : 0 < lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ) := by positivity
  have hlcm : lc * (m : ℝ) ≤ 20480 * lg * n * ρ := by
    have e : lc * (m : ℝ) = max (2560 * (m : ℝ)) (20480 * lg * n * ρ) := by
      rw [hlc, max_mul_of_nonneg _ _ hmR.le]
      congr 1
      field_simp
    rw [e]
    apply max_le _ le_rfl
    nlinarith
  have hpow : lg ^ (-(3 / 2 : ℝ)) * lg = δ ^ (η / 2) := by
    rw [hlg, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    congr 1; ring
  have hη2 : δ ^ (η / 2) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  have hnδ : 0 < (n : ℝ) * δ := by
    have : 0 < n := by
      obtain ⟨i, -⟩ := hS
      exact i.pos
    positivity
  have hΦ : lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ) ≤ 20480 * (n * δ) := by
    calc lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ) = lg ^ (-(3 / 2 : ℝ)) * (lc * m) * (δ / ρ) := by
          ring
      _ ≤ lg ^ (-(3 / 2 : ℝ)) * (20480 * lg * n * ρ) * (δ / ρ) := by gcongr
      _ = (lg ^ (-(3 / 2 : ℝ)) * lg) * (20480 * (n * δ)) := by field_simp
      _ = δ ^ (η / 2) * (20480 * (n * δ)) := by rw [hpow]
      _ ≤ 1 * (20480 * (n * δ)) := by gcongr
      _ = 20480 * (n * δ) := one_mul _
  have hΦσ : (20480 : ℝ) ^ (-σ) * (n * δ) ^ (-σ) ≤
      (lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ)) ^ (-σ) := by
    rw [← Real.mul_rpow (by norm_num) hnδ.le]
    exact Real.rpow_le_rpow_of_nonpos hΦpos hΦ (by linarith)
  rw [hlginv, Real.rpow_add hδ]
  have hA : 0 ≤ κR * δ ^ ε * (δ / ρ) ^ ω * δ ^ η * (m * δ ^ 2) := by positivity
  calc κR * 20480 ^ (-σ) * (δ ^ ε * δ ^ η) * (δ / ρ) ^ ω * (m * δ ^ 2) * (n * δ) ^ (-σ)
      = (κR * δ ^ ε * (δ / ρ) ^ ω * δ ^ η * (m * δ ^ 2)) *
          ((20480 : ℝ) ^ (-σ) * (n * δ) ^ (-σ)) := by ring
    _ ≤ (κR * δ ^ ε * (δ / ρ) ^ ω * δ ^ η * (m * δ ^ 2)) *
          (lg ^ (-(3 / 2 : ℝ)) * lc * (m * δ / ρ)) ^ (-σ) := mul_le_mul_of_nonneg_left hΦσ hA
    _ = _ := by ring

end WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain
