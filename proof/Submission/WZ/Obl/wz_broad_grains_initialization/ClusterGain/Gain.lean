-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain.Gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.ClusterGain.Cluster
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularPruning

/-!
# Cluster gain: the volume gain from a cluster structure

Let `Zc c i` be shadings of the tubes of an admissible family, sorted into finitely many
clusters `c`, each lying in one carrier `Carrier 6 ρ (y c) (w c)`. Suppose every point lies in
at most `P` cluster unions, every tube belongs to at most `C₀` clusters and the total cluster
mass is at least `M n δ²` with `2 C₀ δ^η₀ ≤ M`. Then dense clusters carry half the mass, each
satisfies the rescaled estimate (`cluster_estimate`) and the overlap bound sums them:
`μ(⋃ Y) ≳ δ^(ε+η) (M/P) (δ/ρ)^ω (nδ²) (nδ)^-σ`.
-/

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

namespace WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain

/-- The volume gain from any cluster structure in carriers of radius `ρ`. -/
theorem cluster_gain {σ ω : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : Interfaces.E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
    ∀ δ ρ η : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ ρ → ρ ≤ 1 → 0 ≤ η →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
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
    ∀ (ι : Type) [Fintype ι] (Zc : ι → Fin n → Set Space) (y w : ι → Space) (P C₀ M : ℝ),
    (∀ c i, MeasurableSet (Zc c i) ∧ Zc c i ⊆ Y i) →
    (∀ i, Y i ⊆ thickening δ (segment ℝ (x i) (x i + v i))) →
    (∀ c, ‖w c‖ = 1) →
    (∀ c i, (Zc c i).Nonempty →
      thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Carrier 6 ρ (y c) (w c)) →
    1 ≤ P → (∀ p, ({c | ∃ i, p ∈ Zc c i}.ncard : ℝ) ≤ P) →
    0 ≤ C₀ → (∀ i, ({c | (Zc c i).Nonempty}.ncard : ℝ) ≤ C₀) →
    ENNReal.ofReal (M * n * δ ^ 2) ≤ ∑ c, ∑ i, volume (Zc c i) →
    2 * C₀ * δ ^ η₀ ≤ M →
    ENNReal.ofReal (κ * δ ^ (ε + η) * (M / P) * (δ / ρ) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      volume (⋃ i, Y i) := by
  intro ε hε
  obtain ⟨κC, hκC, η₀, hη₀, hC⟩ := cluster_estimate hσ hσ2 hω hE ε hε
  refine ⟨κC / 768, by positivity, η₀, hη₀, ?_⟩
  intro δ ρ η hδ hδ100 hδρ hρ1 hη n x v Y hv hball hX hK hF ι _ Zc y w P C₀ M hZc hYT hw
    hcar hP1 hP hC₀0 hC₀ hmass hdense
  classical
  have hδ1 : δ ≤ 1 := by linarith
  have hρ : 0 < ρ := hδ.trans_le hδρ
  -- clusters, their sizes, unions and masses
  set Sc : ι → Finset (Fin n) := fun c => Finset.univ.filter fun i => (Zc c i).Nonempty
    with hScdef
  set Uc : ι → Set Space := fun c => ⋃ i, Zc c i with hUcdef
  set Mc : ι → ENNReal := fun c => ∑ i, volume (Zc c i) with hMcdef
  set Dn : Finset ι := Finset.univ.filter fun c =>
    ENNReal.ofReal (δ ^ η₀ * (Sc c).card * δ ^ 2) ≤ Mc c with hDndef
  set G : ℝ := κC * δ ^ (ε + η) * (δ / ρ) ^ ω * δ ^ 2 * (n * δ) ^ (-σ) with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hUmeas : ∀ c, MeasurableSet (Uc c) := fun c => MeasurableSet.iUnion fun i => (hZc c i).1
  -- Step A: every dense cluster satisfies the rescaled estimate
  have hA : ∀ c ∈ Dn, ENNReal.ofReal (G * (Sc c).card) ≤ volume (Uc c) := by
    intro c hc
    have hcd : ENNReal.ofReal (δ ^ η₀ * (Sc c).card * δ ^ 2) ≤ Mc c := (Finset.mem_filter.mp hc).2
    rcases (Sc c).eq_empty_or_nonempty with hE | hne
    · rw [hE, Finset.card_empty, Nat.cast_zero, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
    have h := hC δ ρ η hδ hδ100 hδρ hρ1 hη n x v hv hball hX hK hF (Sc c) (Zc c) (y c) (w c)
      (hw c) hne (fun i => ⟨(hZc c i).1, (hZc c i).2.trans (hYT i)⟩)
      (fun i hi => by
        rw [Finset.mem_filter] at hi
        push Not at hi
        exact hi (Finset.mem_univ i))
      (fun i hi => hcar c i (Finset.mem_filter.mp hi).2) hcd
    refine le_trans (le_of_eq ?_) h
    congr 1
    rw [hGdef]; ring
  -- Step B: the overlap bound
  have hPfl : ∀ p, ((Finset.univ.filter fun c => p ∈ Uc c).card) ≤ ⌊P⌋₊ := by
    intro p
    apply Nat.le_floor
    have heq : ({c | ∃ i, p ∈ Zc c i} : Set ι) = ↑(Finset.univ.filter fun c => p ∈ Uc c) := by
      ext c; simp [Uc]
    have := hP p
    rw [heq, Set.ncard_coe_finset] at this
    exact this
  have hB : ∑ c ∈ Dn, volume (Uc c) ≤ (⌊P⌋₊ : ENNReal) * volume (⋃ i, Y i) := by
    have hW : MeasurableSet (⋃ c, Uc c) := MeasurableSet.iUnion hUmeas
    have h := WangZahlLot.Obl.wz_clustered_cover_volume_gain.sum_measure_inter_le_of_overlap
      volume Dn Uc (fun c _ => hUmeas c) (⋃ c, Uc c) hW ⌊P⌋₊
      (fun p _ => (Finset.card_le_card (Finset.monotone_filter_left _
        (Finset.subset_univ Dn))).trans (hPfl p))
    have hinter : ∀ c, (⋃ c, Uc c) ∩ Uc c = Uc c := fun c =>
      inter_eq_right.mpr (subset_iUnion Uc c)
    simp only [hinter] at h
    refine h.trans (mul_le_mul_right (measure_mono ?_) _)
    refine iUnion_subset fun c => iUnion_subset fun i => ?_
    exact (hZc c i).2.trans (subset_iUnion Y i)
  -- Step C: dense clusters carry half of the mass
  have hMc_le : ∀ c, Mc c ≤ ENNReal.ofReal (384 * δ ^ 2 * (Sc c).card) := by
    intro c
    have hsplit : Mc c = ∑ i ∈ Sc c, volume (Zc c i) := by
      simp only [Mc]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [Finset.mem_filter] at hi
      push Not at hi
      rw [hi (Finset.mem_univ i), measure_empty]
    rw [hsplit]
    calc ∑ i ∈ Sc c, volume (Zc c i) ≤ ∑ i ∈ Sc c, ENNReal.ofReal (384 * δ ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          exact (measure_mono ((hZc c i).2.trans (hYT i))).trans
            (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 (x i) (v i) (hv i))
      _ = ENNReal.ofReal (384 * δ ^ 2 * (Sc c).card) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hsumC : (∑ c, ((Sc c).card : ℝ)) ≤ C₀ * n := by
    have h1 : (∑ c, ((Sc c).card : ℝ)) =
        ∑ i : Fin n, (((Finset.univ.filter fun c => (Zc c i).Nonempty).card : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      congr 1
      simp only [Sc, Finset.card_filter]
      exact Finset.sum_comm
    rw [h1]
    calc ∑ i : Fin n, (((Finset.univ.filter fun c => (Zc c i).Nonempty).card : ℕ) : ℝ)
        ≤ ∑ _i : Fin n, C₀ := by
          apply Finset.sum_le_sum
          intro i _
          have heq : ({c | (Zc c i).Nonempty} : Set ι) =
              ↑(Finset.univ.filter fun c => (Zc c i).Nonempty) := by ext c; simp
          have := hC₀ i
          rwa [heq, Set.ncard_coe_finset] at this
      _ = C₀ * n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  set ND : ℝ := ∑ c ∈ Dn, ((Sc c).card : ℝ) with hND
  clear_value ND
  have hNDge : M * n / 768 ≤ ND := by
    set Dc := Finset.univ.filter
      (fun c => ¬ ENNReal.ofReal (δ ^ η₀ * (Sc c).card * δ ^ 2) ≤ Mc c) with hDc
    have h1 : ∑ c ∈ Dn, Mc c ≤ ENNReal.ofReal (384 * δ ^ 2 * ND) := by
      calc ∑ c ∈ Dn, Mc c ≤ ∑ c ∈ Dn, ENNReal.ofReal (384 * δ ^ 2 * (Sc c).card) :=
            Finset.sum_le_sum fun c _ => hMc_le c
        _ = ENNReal.ofReal (384 * δ ^ 2 * ND) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity), hND, Finset.mul_sum]
    have h2 : ∑ c ∈ Dc, Mc c ≤ ENNReal.ofReal (δ ^ η₀ * δ ^ 2 * (C₀ * n)) := by
      calc ∑ c ∈ Dc, Mc c ≤ ∑ c ∈ Dc, ENNReal.ofReal (δ ^ η₀ * (Sc c).card * δ ^ 2) := by
            apply Finset.sum_le_sum
            intro c hc
            exact (not_le.mp (Finset.mem_filter.mp hc).2).le
        _ = ENNReal.ofReal (∑ c ∈ Dc, δ ^ η₀ * ((Sc c).card : ℝ) * δ ^ 2) :=
            (ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)).symm
        _ ≤ ENNReal.ofReal (δ ^ η₀ * δ ^ 2 * (C₀ * n)) := by
            apply ENNReal.ofReal_le_ofReal
            calc ∑ c ∈ Dc, δ ^ η₀ * ((Sc c).card : ℝ) * δ ^ 2
                = δ ^ η₀ * δ ^ 2 * ∑ c ∈ Dc, ((Sc c).card : ℝ) := by
                  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
              _ ≤ δ ^ η₀ * δ ^ 2 * ∑ c, ((Sc c).card : ℝ) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    (fun c _ _ => Nat.cast_nonneg _)
              _ ≤ δ ^ η₀ * δ ^ 2 * (C₀ * n) := by gcongr
    have hND0 : 0 ≤ ND := by rw [hND]; exact Finset.sum_nonneg (fun c _ => Nat.cast_nonneg _)
    have hsplit : ∑ c, Mc c = ∑ c ∈ Dn, Mc c + ∑ c ∈ Dc, Mc c :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ _ Mc).symm
    have hA1 : (0 : ℝ) ≤ 384 * δ ^ 2 * ND := mul_nonneg (by positivity) hND0
    have hA2 : (0 : ℝ) ≤ δ ^ η₀ * δ ^ 2 * (C₀ * n) :=
      mul_nonneg (by positivity) (mul_nonneg hC₀0 (Nat.cast_nonneg _))
    have htot : ENNReal.ofReal (M * n * δ ^ 2) ≤
        ENNReal.ofReal (384 * δ ^ 2 * ND + δ ^ η₀ * δ ^ 2 * (C₀ * n)) := by
      have hm' : ENNReal.ofReal (M * n * δ ^ 2) ≤ ∑ c, Mc c := hmass
      calc ENNReal.ofReal (M * n * δ ^ 2) ≤ ∑ c, Mc c := hm'
        _ = ∑ c ∈ Dn, Mc c + ∑ c ∈ Dc, Mc c := hsplit
        _ ≤ ENNReal.ofReal (384 * δ ^ 2 * ND) + ENNReal.ofReal (δ ^ η₀ * δ ^ 2 * (C₀ * n)) :=
            add_le_add h1 h2
        _ = _ := (ENNReal.ofReal_add hA1 hA2).symm
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
    have hd2 : δ ^ η₀ * δ ^ 2 * (C₀ * n) ≤ M / 2 * n * δ ^ 2 := by
      have : C₀ * δ ^ η₀ ≤ M / 2 := by linarith
      have hn0 : (0 : ℝ) ≤ n * δ ^ 2 := by positivity
      nlinarith
    have hδ2 : 0 < δ ^ 2 := by positivity
    have : M * n * δ ^ 2 / 2 ≤ 384 * δ ^ 2 * ND := by linarith
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 768)]
    nlinarith
  -- Step D: combine
  have hD1 : ENNReal.ofReal (G * (M * n / 768)) ≤ (⌊P⌋₊ : ENNReal) * volume (⋃ i, Y i) := by
    calc ENNReal.ofReal (G * (M * n / 768)) ≤ ENNReal.ofReal (G * ND) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hNDge hG0)
      _ = ∑ c ∈ Dn, ENNReal.ofReal (G * (Sc c).card) := by
          rw [hND, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity)]
      _ ≤ ∑ c ∈ Dn, volume (Uc c) := Finset.sum_le_sum hA
      _ ≤ _ := hB
  have hk1 : (1 : ℝ) ≤ ⌊P⌋₊ := by
    have : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by norm_num; exact hP1)
    exact_mod_cast this
  have hkP : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hkpos : (0 : ℝ) < ⌊P⌋₊ := by linarith
  have hLHS : κC / 768 * δ ^ (ε + η) * (M / P) * (δ / ρ) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ) =
      G * (M * n / 768) / P := by
    rw [hGdef]; field_simp
  rw [hLHS]
  rcases le_or_gt (G * (M * n / 768)) 0 with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hX (by linarith))]
    exact bot_le
  calc ENNReal.ofReal (G * (M * n / 768) / P)
      ≤ ENNReal.ofReal (G * (M * n / 768) / ⌊P⌋₊) := by
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_left hX.le hkpos hkP
    _ = ENNReal.ofReal (G * (M * n / 768)) / (⌊P⌋₊ : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos hkpos, ENNReal.ofReal_natCast]
    _ ≤ volume (⋃ i, Y i) := by
        apply ENNReal.div_le_of_le_mul
        exact hD1.trans_eq (mul_comm _ _)

end WangZahlLot.Obl.wz_broad_grains_initialization.ClusterGain
