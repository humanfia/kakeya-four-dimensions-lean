-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGFibre.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSTheorem

/-!
# One fibre of the two-scale decomposition is extremal after rescaling

Prop. 4.1, Step 1 of the sticky Kakeya paper rescales one fibre of the two-scale
decomposition. Here:

* `fibre_union_volume_mul_le`: by the balanced cover (P3), the union of one fibre times the
  coarse union is at most `O(ρc² δ^(-ε))` times the fine union;
* `exists_heavy_level_fibre`: some tube of the underlying level cover carries at least the
  average mass of its fine tubes.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate enumerate enumerate_mem
  enumerate_injective enumerate_surjective enumerate_count enumerate_sum ncard_setOf)

/-- Scaling volumes by a positive constant. -/
theorem volume_smul_set_pos {c : ℝ} (hc : 0 < c) (A : Set Space) :
    volume (c • A) = ENNReal.ofReal (c ^ 3) * volume A := by
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hc 3)]

/-- By the balanced cover, one fibre times the coarse union is at most `O(ρc² δ^(-ε))`
times the fine union. -/
theorem fibre_union_volume_mul_le {ε δ ρc s θ : ℝ} {n k : ℕ} {Y Y' : Fin n → Set Space}
    {z w : Fin k → Space} {Yt : Fin k → Set Space} {a : Fin n → Fin k}
    {M : Fin k → Finset (Fin 3 → ℤ)}
    (hδ : 0 < δ) (hρc : 0 < ρc) (hρc1 : ρc ≤ 1 / 8)
    (hY'Y : ∀ i, Y' i ⊆ Y i) (hY'm : ∀ i, MeasurableSet (Y' i))
    (hw : ∀ j, ‖w j‖ = 1) (hYtT : ∀ j, Yt j ⊆ tube ρc (z j) (w j))
    (hcover : ∀ i, (1 - 4 * ρc) • Y' i ⊆ Yt (a i))
    (hs : 0 < s) (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) (_hθ : 0 < θ)
    (hP3 : ∀ j, ∀ m ∈ M j, ENNReal.ofReal θ * volume (gridCube s m) ≤
        volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ∧
      volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ≤
        ENNReal.ofReal (δ ^ (-ε) * θ) * volume (gridCube s m))
    (j : Fin k) :
    volume (⋃ i ∈ {i | a i = j}, Y' i) * volume (⋃ j, Yt j) ≤
      ENNReal.ofReal (3072 * ρc ^ 2 * δ ^ (-ε)) * volume (⋃ i, Y i) := by
  set lam : ℝ := 1 - 4 * ρc with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  have hlh : 1 / 2 ≤ lam := by rw [hlam]; linarith
  have hl1 : lam ≤ 1 := by rw [hlam]; linarith
  set E' : Set Space := ⋃ i, lam • Y' i with hE'
  have hE'm : MeasurableSet E' := MeasurableSet.iUnion fun i => (hY'm i).const_smul₀ lam
  set Mall : Finset (Fin 3 → ℤ) := Finset.univ.biUnion M with hMall
  have hcubes : (⋃ j, Yt j) = ⋃ m ∈ Mall, gridCube s m := by
    ext q
    simp only [mem_iUnion, hYt, hMall, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, m, hm, hq⟩; exact ⟨m, ⟨j, hm⟩, hq⟩
    · rintro ⟨m, ⟨j, hm⟩, hq⟩; exact ⟨j, m, hm, hq⟩
  have hdisj : (Mall : Set (Fin 3 → ℤ)).PairwiseDisjoint (gridCube s) :=
    fun m _ m' _ hmm => gridCube_disjoint hs hmm
  -- (a) the density times the coarse union is at most the fine union
  have ha : ENNReal.ofReal θ * volume (⋃ j, Yt j) ≤ volume (⋃ i, Y i) := by
    rw [hcubes, measure_biUnion_finset hdisj (fun m _ => measurableSet_gridCube s m),
      Finset.mul_sum]
    calc ∑ m ∈ Mall, ENNReal.ofReal θ * volume (gridCube s m)
        ≤ ∑ m ∈ Mall, volume (E' ∩ gridCube s m) := by
          apply Finset.sum_le_sum
          intro m hm
          obtain ⟨j, -, hmj⟩ := Finset.mem_biUnion.mp hm
          exact (hP3 j m hmj).1
      _ = volume (⋃ m ∈ Mall, E' ∩ gridCube s m) :=
          (measure_biUnion_finset (fun m _ m' _ hmm => (gridCube_disjoint hs hmm).mono
            inter_subset_right inter_subset_right)
            (fun m _ => hE'm.inter (measurableSet_gridCube s m))).symm
      _ ≤ volume E' := measure_mono (iUnion₂_subset fun m _ => inter_subset_left)
      _ = volume (lam • ⋃ i, Y' i) := by rw [hE', Set.smul_set_iUnion]
      _ = ENNReal.ofReal (lam ^ 3) * volume (⋃ i, Y' i) := volume_smul_set_pos hl0 _
      _ ≤ 1 * volume (⋃ i, Y' i) := by
          gcongr
          rw [ENNReal.ofReal_le_one]
          exact pow_le_one₀ hl0.le hl1
      _ ≤ volume (⋃ i, Y i) := by rw [one_mul]; exact measure_mono (iUnion_mono hY'Y)
  -- (b) the contracted fibre has density at most `δ^(-ε) θ` in the coarse shading
  have hb : ENNReal.ofReal (lam ^ 3) * volume (⋃ i ∈ {i | a i = j}, Y' i) ≤
      ENNReal.ofReal (δ ^ (-ε) * θ) * ENNReal.ofReal (384 * ρc ^ 2) := by
    rw [← volume_smul_set_pos hl0]
    have hsub : lam • (⋃ i ∈ {i | a i = j}, Y' i) ⊆ ⋃ m ∈ M j, E' ∩ gridCube s m := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      have h1 : lam • p ∈ Yt j := by
        rw [← (hi : a i = j)]; exact hcover i ⟨p, hpi, rfl⟩
      rw [hYt] at h1
      obtain ⟨m, hm, hpm⟩ := mem_iUnion₂.mp h1
      exact mem_iUnion₂.mpr ⟨m, hm, mem_iUnion.mpr ⟨i, p, hpi, rfl⟩, hpm⟩
    calc volume (lam • (⋃ i ∈ {i | a i = j}, Y' i))
        ≤ volume (⋃ m ∈ M j, E' ∩ gridCube s m) := measure_mono hsub
      _ ≤ ∑ m ∈ M j, volume (E' ∩ gridCube s m) := measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ M j, ENNReal.ofReal (δ ^ (-ε) * θ) * volume (gridCube s m) :=
          Finset.sum_le_sum fun m hm => (hP3 j m hm).2
      _ = ENNReal.ofReal (δ ^ (-ε) * θ) * volume (Yt j) := by
          rw [← Finset.mul_sum, hYt j, measure_biUnion_finset
            (fun m _ m' _ hmm => gridCube_disjoint hs hmm)
            (fun m _ => measurableSet_gridCube s m)]
      _ ≤ ENNReal.ofReal (δ ^ (-ε) * θ) * ENNReal.ofReal (384 * ρc ^ 2) := by
          gcongr
          exact (measure_mono (hYtT j)).trans
            (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hρc (by linarith)
              (z j) (w j) (hw j))
  -- combine
  have hl3 : ENNReal.ofReal (lam ^ 3) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hl3' : ENNReal.ofReal (lam ^ 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA : ENNReal.ofReal (δ ^ (-ε) * θ) = ENNReal.ofReal (δ ^ (-ε)) * ENNReal.ofReal θ :=
    ENNReal.ofReal_mul (by positivity)
  have hC : ENNReal.ofReal (δ ^ (-ε)) * ENNReal.ofReal (384 * ρc ^ 2) ≤
      ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (3072 * ρc ^ 2 * δ ^ (-ε)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h8 : 1 / 8 ≤ lam ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hlh 3
      norm_num at this ⊢; linarith
    have hd : 0 ≤ δ ^ (-ε) * ρc ^ 2 := by positivity
    nlinarith
  have key : ENNReal.ofReal (lam ^ 3) * (volume (⋃ i ∈ {i | a i = j}, Y' i) *
      volume (⋃ j, Yt j)) ≤ ENNReal.ofReal (lam ^ 3) *
        (ENNReal.ofReal (3072 * ρc ^ 2 * δ ^ (-ε)) * volume (⋃ i, Y i)) := by
    calc ENNReal.ofReal (lam ^ 3) * (volume (⋃ i ∈ {i | a i = j}, Y' i) *
          volume (⋃ j, Yt j))
        = (ENNReal.ofReal (lam ^ 3) * volume (⋃ i ∈ {i | a i = j}, Y' i)) *
            volume (⋃ j, Yt j) := (mul_assoc _ _ _).symm
      _ ≤ (ENNReal.ofReal (δ ^ (-ε) * θ) * ENNReal.ofReal (384 * ρc ^ 2)) *
            volume (⋃ j, Yt j) := mul_le_mul_left hb _
      _ = (ENNReal.ofReal (δ ^ (-ε)) * ENNReal.ofReal (384 * ρc ^ 2)) *
            (ENNReal.ofReal θ * volume (⋃ j, Yt j)) := by rw [hA]; ring
      _ ≤ (ENNReal.ofReal (δ ^ (-ε)) * ENNReal.ofReal (384 * ρc ^ 2)) *
            volume (⋃ i, Y i) := mul_le_mul_right ha _
      _ ≤ (ENNReal.ofReal (lam ^ 3) * ENNReal.ofReal (3072 * ρc ^ 2 * δ ^ (-ε))) *
            volume (⋃ i, Y i) := mul_le_mul_left hC _
      _ = ENNReal.ofReal (lam ^ 3) *
            (ENNReal.ofReal (3072 * ρc ^ 2 * δ ^ (-ε)) * volume (⋃ i, Y i)) := mul_assoc _ _ _
  exact (ENNReal.mul_le_mul_iff_right hl3 hl3').mp key

/-- Some tube of a level cover carries at least the average mass of its fine tubes. -/
theorem exists_heavy_level_fibre {n k0 : ℕ} (hn : 0 < n) (fl : Fin n → Fin k0)
    (ω : Fin n → ℝ) {c : ℝ} (hmass : c * n ≤ ∑ i, ω i) :
    ∃ j0, 0 < (Finset.univ.filter (fun i => fl i = j0)).card ∧
      c * (Finset.univ.filter (fun i => fl i = j0)).card ≤
        ∑ i ∈ Finset.univ.filter (fun i => fl i = j0), ω i := by
  classical
  set S := Finset.univ.filter (fun j0 => 0 < (Finset.univ.filter (fun i => fl i = j0)).card)
    with hS
  have hSne : S.Nonempty := by
    refine ⟨fl ⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.card_pos.mpr ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hzero : ∀ j0 ∈ Finset.univ, j0 ∉ S →
      (Finset.univ.filter (fun i => fl i = j0)).card = 0 := by
    intro j0 _ hj0
    by_contra h
    exact hj0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩)
  have hsum1 : ∑ j0 ∈ S, c * ((Finset.univ.filter (fun i => fl i = j0)).card : ℝ) = c * n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j0 h1 h2 => by
      rw [hzero j0 h1 h2, Nat.cast_zero])]
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (fl i))]
    simp
  have hsum2 : ∑ j0 ∈ S, ∑ i ∈ Finset.univ.filter (fun i => fl i = j0), ω i = ∑ i, ω i := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun j0 h1 h2 => by
      rw [Finset.card_eq_zero.mp (hzero j0 h1 h2), Finset.sum_empty])]
    exact Finset.sum_fiberwise Finset.univ fl ω
  have hle : ∑ j0 ∈ S, c * ((Finset.univ.filter (fun i => fl i = j0)).card : ℝ) ≤
      ∑ j0 ∈ S, ∑ i ∈ Finset.univ.filter (fun i => fl i = j0), ω i := by
    rw [hsum1, hsum2]; exact hmass
  obtain ⟨j0, hj0S, hj0⟩ := Finset.exists_le_of_sum_le hSne hle
  exact ⟨j0, (Finset.mem_filter.mp hj0S).2, hj0⟩

/-- One fibre of a two-scale decomposition, rescaled and thinned, is an extremal frozen
family: its mass comes from a heavy tube of the underlying level cover, its volume from the
balanced cover and the volume lower bound at the coarse scale. -/
theorem fibre_extremal_core {σ ε η t τ ρc ρ0 b ε' tsel θ s : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 100) (hηε : η ≤ ε) (hε : 0 < ε)
    {n : ℕ} {x v : Fin n → Space} {Y Y' : Fin n → Set Space}
    (hF : Family η τ n x v Y) (hS : Separated η τ n x v)
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (τ ^ (σ - η)))
    (hY'Y : ∀ i, Y' i ⊆ Y i) (hY'm : ∀ i, MeasurableSet (Y' i))
    (hmass' : ENNReal.ofReal (τ ^ ε * (n : ℝ) * τ ^ 2) ≤ ∑ i, volume (Y' i))
    {k : ℕ} {z w : Fin k → Space} {Yt : Fin k → Set Space} {a : Fin n → Fin k}
    {M : Fin k → Finset (Fin 3 → ℤ)}
    (hFamc : Family ε ρc k z w Yt)
    (hcover : ∀ i, (1 - 4 * ρc) • Y' i ⊆ Yt (a i))
    (hs : 0 < s) (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) (hθ : 0 < θ)
    (hP3 : ∀ j, ∀ m ∈ M j, ENNReal.ofReal θ * volume (gridCube s m) ≤
        volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ∧
      volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ≤
        ENNReal.ofReal (τ ^ (-ε) * θ) * volume (gridCube s m))
    {k0 : ℕ} {z0 w0 : Fin k0 → Space} {g : Fin k → Fin k0}
    (hτρ0 : τ ≤ ρ0) (hρ0c' : ρ0 ≤ ρc) (hg : Function.Injective g)
    (hw0 : ∀ j, ‖w0 j‖ = 1)
    (huniq0 : ∀ i, ∃! j, tube τ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j))
    (hfrost0 : ∀ j, ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (({i | tube τ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j) ∧
        tube τ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ0 ^ 2) ≤
      ENNReal.ofReal (τ ^ (-ε) *
        ({i | tube τ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j)}.ncard : ℝ)) * volume W)
    (hdil0 : ∀ i j j', tube τ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j) (w0 j) →
      tube τ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j') (w0 j') → j = j')
    (hY'0 : ∀ i, (Y' i).Nonempty → tube τ (x i) (v i) ⊆ tube ρ0 (z0 (g (a i))) (w0 (g (a i))))
    (hlowc : ENNReal.ofReal (ρc ^ t) < volume (⋃ j, Yt j))
    (hρc : ρc ≤ 1 / 1000)
    (hb : b = 1 / (1 + 144 * (1 / 100) ^ 2))
    (hδ'small : b * ((1 / 100) / ρ0) * τ ≤ 1 / 10000000)
    (hC2a : 34 * τ ^ (-(2 * ε)) ≤ (b * ((1 / 100) / ρ0) * τ) ^ (-ε'))
    (hC2b : (b * ((1 / 100) / ρ0) * τ) ^ ε' ≤ τ ^ (2 * ε) / (34 * 10 ^ 7))
    (hC2c : 2312 * τ ^ (-ε) / (1 / 100) ^ 2 / tsel ≤ (b * ((1 / 100) / ρ0) * τ) ^ (-ε'))
    (htsel : 0 < tsel)
    (hFmass : (b * ((1 / 100) / ρ0) * τ) ^ ε' ≤
      b * (τ ^ ε / ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈ε⁻¹⌉₊ + 3) -
        384 * tsel * ((⌈ε⁻¹⌉₊ + 3 : ℕ) : ℝ)))
    (hFvol : b ^ 3 * ((1 / 100) / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-ε) * τ ^ (σ - η)) ≤
      ρc ^ t * (b * ((1 / 100) / ρ0) * τ) ^ (σ - ε')) :
    ∃ (j0 : Fin k0) (m : ℕ) (ι : Fin m → Fin n), Function.Injective ι ∧
      (∀ q, tube τ (x (ι q)) (v (ι q)) ⊆ tube ρ0 (z0 j0) (w0 j0)) ∧
      (∀ q, resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b ''
          tube τ (x (ι q)) (v (ι q)) ⊆
        tube (b * ((1 / 100) / ρ0) * τ)
          (resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b
            (orStart (w0 j0) (x (ι q)) (v (ι q))))
          (ndir (w0 j0) ((1 / 100) / ρ0) (orDir (w0 j0) (v (ι q))))) ∧
      Family ε' (b * ((1 / 100) / ρ0) * τ) m
        (fun q => resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b
          (orStart (w0 j0) (x (ι q)) (v (ι q))))
        (fun q => ndir (w0 j0) ((1 / 100) / ρ0) (orDir (w0 j0) (v (ι q))))
        (fun q => resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b '' Y' (ι q)) ∧
      Separated ε' (b * ((1 / 100) / ρ0) * τ) m
        (fun q => resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b
          (orStart (w0 j0) (x (ι q)) (v (ι q))))
        (fun q => ndir (w0 j0) ((1 / 100) / ρ0) (orDir (w0 j0) (v (ι q)))) ∧
      volume (⋃ q, resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) ((1 / 100) / ρ0) b '' Y' (ι q)) ≤
        ENNReal.ofReal ((b * ((1 / 100) / ρ0) * τ) ^ (σ - ε')) := by
  classical
  obtain ⟨hn, hv, hball, hhalf, hYm, hYT, -⟩ := id hF
  obtain ⟨-, hw, -, -, -, hYtT, -⟩ := id hFamc
  have hρ0 : 0 < ρ0 := lt_of_lt_of_le hτ hτρ0
  have hτ1' : τ ≤ 1 := by linarith
  set A : ℝ := (1 / 100) / ρ0 with hA
  have hApos : 0 < A := by positivity
  have hbpos : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb, div_le_one (by positivity)]; norm_num
  set δ' : ℝ := b * A * τ with hδ'
  have hδ'pos : 0 < δ' := by positivity
  -- the level assignment
  choose fl hfl using fun i => (huniq0 i).exists
  have hflu : ∀ i j, tube τ (x i) (v i) ⊆ tube ρ0 (z0 j) (w0 j) → j = fl i :=
    fun i j h => (huniq0 i).unique h (hfl i)
  -- weights
  set ω : Fin n → ℝ := fun i => (volume (Y' i)).toReal with hω
  have hY'fin : ∀ i, volume (Y' i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hY'Y i).trans ((hYT i).trans (hball i))))
  have hω0 : ∀ i, 0 ≤ ω i := fun i => ENNReal.toReal_nonneg
  have hωM : ∀ i, ω i ≤ 384 * τ ^ 2 := by
    intro i
    have h := (measure_mono ((hY'Y i).trans (hYT i))).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hτ hτ1' (x i) (v i) (hv i))
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hmassR : τ ^ ε * τ ^ 2 * n ≤ ∑ i, ω i := by
    have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hY'fin i) hmass'
    rw [ENNReal.toReal_sum (fun i _ => hY'fin i), ENNReal.toReal_ofReal (by positivity)] at h
    linarith
  obtain ⟨j0, hj0pos, hj0⟩ := exists_heavy_level_fibre hn fl ω hmassR
  have hfib : Finset.univ.filter (fun i => Tube τ (x i) (v i) ⊆ Tube ρ0 (z0 j0) (w0 j0)) =
      Finset.univ.filter (fun i => fl i = j0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hflu i j0 h).symm
    · intro h; rw [← h]; exact hfl i
  -- the rescaled fibre
  obtain ⟨m, ι, hι, hιfib, hιgeo, hιhalf, hιsep, hιmass⟩ :=
    fibre_family (η := ε) (lam0 := 1 / 100) (a := A) (b := b) (δ' := δ') (η' := ε')
      (t := tsel) (Mw := 384 * τ ^ 2) hτ hτ1 hε hv hball hhalf
      (hS.mono_error hτ hτ1' hηε) huniq0 hfrost0 hdil0 j0 (hw0 j0) rfl hτρ0
      (hρ0c'.trans hρc |>.trans (by norm_num)) le_rfl (hρ0c'.trans hρc |>.trans (by norm_num))
      (by norm_num) rfl hb rfl hδ'small hC2a hC2b hC2c htsel ω hω0 hωM (by positivity)
  rw [hfib] at hιmass
  set F := Finset.univ.filter (fun i => fl i = j0) with hF_def
  set N0r : ℝ := ((⌈ε⁻¹⌉₊ + 3 : ℕ) : ℝ) with hN0r
  set C1 : ℝ := ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈ε⁻¹⌉₊ + 3) with hC1
  have hC1pos : 0 < C1 := by positivity
  set K : ℝ := τ ^ ε / C1 - 384 * tsel * N0r with hK
  have hKpos : 0 < K := by
    have h1 : 0 < δ' ^ ε' := by positivity
    have h2 : 0 < b * K := lt_of_lt_of_le h1 hFmass
    exact pos_of_mul_pos_right h2 hbpos.le
  have hsumq : (F.card : ℝ) * τ ^ 2 * K ≤ ∑ q, ω (ι q) := by
    refine le_trans ?_ hιmass
    have h1 : τ ^ ε * τ ^ 2 * F.card / C1 ≤ (∑ i ∈ F, ω i) / C1 :=
      div_le_div_of_nonneg_right (by linarith) hC1pos.le
    have h2 : (F.card : ℝ) * τ ^ 2 * K =
        τ ^ ε * τ ^ 2 * F.card / C1 - 384 * τ ^ 2 * tsel * (N0r * F.card) := by
      rw [hK]; field_simp
    rw [h2]
    linarith
  have hmF : (m : ℝ) ≤ F.card := by
    have h1 : (Finset.univ.image ι).card = m := by
      rw [Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
    have h2 : Finset.univ.image ι ⊆ F := by
      intro i hi
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hflu _ j0 (hιfib q)).symm⟩
    have := Finset.card_le_card h2
    rw [h1] at this
    exact_mod_cast this
  have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hj0pos
  have hm : 0 < m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    subst hm0'
    have : ∑ q : Fin 0, ω (ι q) = 0 := Finset.sum_empty
    have h3 : 0 < (F.card : ℝ) * τ ^ 2 * K := by positivity
    linarith
  -- images of the shadings
  set φ : Space → Space := resc (w0 j0) (z0 j0 + (1 / 2 : ℝ) • w0 j0) A b with hφ
  have hvolφ : ∀ S : Set Space, volume (φ '' S) = ENNReal.ofReal (b ^ 3 * A ^ 2) * volume S :=
    fun S => volume_image_resc (hw0 j0) hbpos.le S
  refine ⟨j0, m, ι, hι, hιfib, fun q => (hιgeo q).2.2, ⟨hm, fun q => (hιgeo q).1,
    fun q => (hιgeo q).2.1, hιhalf, fun q => measurableSet_image_resc (hw0 j0) hApos.ne'
      hbpos.ne' (hY'm _), fun q => (Set.image_mono ((hY'Y _).trans (hYT _))).trans
      (hιgeo q).2.2, ?_⟩, hιsep hm, ?_⟩
  · -- mass of the rescaled family
    have hsum : ∑ q, volume (φ '' Y' (ι q)) =
        ENNReal.ofReal (b ^ 3 * A ^ 2 * ∑ q, ω (ι q)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun q _ => hω0 _),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [hvolφ, hω, ENNReal.ofReal_toReal (hY'fin _)]
    rw [hsum]
    apply ENNReal.ofReal_le_ofReal
    have hδ'2 : δ' ^ 2 = b ^ 2 * A ^ 2 * τ ^ 2 := by rw [hδ']; ring
    calc δ' ^ ε' * (m : ℝ) * δ' ^ 2 ≤ (b * K) * F.card * (b ^ 2 * A ^ 2 * τ ^ 2) := by
          rw [hδ'2]
          apply mul_le_mul _ le_rfl (by positivity) (by positivity)
          exact mul_le_mul hFmass hmF (by positivity) (by positivity)
      _ = b ^ 3 * A ^ 2 * ((F.card : ℝ) * τ ^ 2 * K) := by ring
      _ ≤ b ^ 3 * A ^ 2 * ∑ q, ω (ι q) := mul_le_mul_of_nonneg_left hsumq (by positivity)
  · -- volume of the rescaled family
    rw [← Set.image_iUnion, hvolφ]
    by_cases hne : ∃ i ∈ F, (Y' i).Nonempty
    · obtain ⟨i1, hi1F, hi1⟩ := hne
      have hfl1 : fl i1 = j0 := (Finset.mem_filter.mp hi1F).2
      set j := a i1 with hj
      have hgj : g j = j0 := by rw [← hfl1]; exact hflu i1 (g j) (hY'0 i1 hi1)
      have hsub : (⋃ q, Y' (ι q)) ⊆ ⋃ i ∈ {i | a i = j}, Y' i := by
        intro p hp
        obtain ⟨q, hpq⟩ := mem_iUnion.mp hp
        have h1 : g (a (ι q)) = j0 := by
          rw [hflu _ _ (hY'0 _ ⟨p, hpq⟩)]
          exact (hflu _ j0 (hιfib q)).symm
        have h2 : a (ι q) = j := hg (h1.trans hgj.symm)
        exact mem_iUnion₂.mpr ⟨ι q, h2, hpq⟩
      have hfv := fibre_union_volume_mul_le hτ (lt_of_lt_of_le hτ (hτρ0.trans hρ0c'))
        (by linarith) hY'Y hY'm hw hYtT hcover hs hYt hθ hP3 j
      have hU : volume (⋃ i, Y i) ≤ ENNReal.ofReal (τ ^ (σ - η)) := hvol
      have hρct : ENNReal.ofReal (ρc ^ t) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.rpow_pos_of_pos (lt_of_lt_of_le hτ (hτρ0.trans hρ0c')) t
      have hρct' : ENNReal.ofReal (ρc ^ t) ≠ ⊤ := ENNReal.ofReal_ne_top
      have key : ENNReal.ofReal (ρc ^ t) *
          (ENNReal.ofReal (b ^ 3 * A ^ 2) * volume (⋃ q, Y' (ι q))) ≤
          ENNReal.ofReal (ρc ^ t) * ENNReal.ofReal (δ' ^ (σ - ε')) := by
        calc ENNReal.ofReal (ρc ^ t) *
              (ENNReal.ofReal (b ^ 3 * A ^ 2) * volume (⋃ q, Y' (ι q)))
            = ENNReal.ofReal (b ^ 3 * A ^ 2) *
                (volume (⋃ q, Y' (ι q)) * ENNReal.ofReal (ρc ^ t)) := by ring
          _ ≤ ENNReal.ofReal (b ^ 3 * A ^ 2) *
                (volume (⋃ i ∈ {i | a i = j}, Y' i) * volume (⋃ j, Yt j)) :=
              mul_le_mul_right (mul_le_mul' (measure_mono hsub) hlowc.le) _
          _ ≤ ENNReal.ofReal (b ^ 3 * A ^ 2) *
                (ENNReal.ofReal (3072 * ρc ^ 2 * τ ^ (-ε)) * ENNReal.ofReal (τ ^ (σ - η))) :=
              mul_le_mul_right (hfv.trans (mul_le_mul_right hU _)) _
          _ = ENNReal.ofReal (b ^ 3 * A ^ 2 * (3072 * ρc ^ 2 * τ ^ (-ε) * τ ^ (σ - η))) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          _ ≤ ENNReal.ofReal (ρc ^ t * δ' ^ (σ - ε')) := ENNReal.ofReal_le_ofReal hFvol
          _ = ENNReal.ofReal (ρc ^ t) * ENNReal.ofReal (δ' ^ (σ - ε')) :=
              ENNReal.ofReal_mul (Real.rpow_nonneg
                (lt_of_lt_of_le hτ (hτρ0.trans hρ0c')).le t)
      exact (ENNReal.mul_le_mul_iff_right hρct hρct').mp key
    · push Not at hne
      have hempty : (⋃ q, Y' (ι q)) = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨q, hpq⟩ := mem_iUnion.mp hp
        have hF' : ι q ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hflu _ j0 (hιfib q)).symm⟩
        have h0 := hne (ι q) hF'
        rw [h0] at hpq
        exact hpq
      rw [hempty, measure_empty, mul_zero]
      exact zero_le

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
