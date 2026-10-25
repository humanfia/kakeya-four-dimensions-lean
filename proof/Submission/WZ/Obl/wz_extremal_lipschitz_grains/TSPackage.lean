-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TSPackage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSCoarseDelete
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSInterface

/-!
# Packaging the two-scale decomposition

Given the final fine shadings (after the fibre deletion, the coarse selection, the coarse
cube deletion, the trimming of low multiplicity and the balancing) and the selected coarse
tubes, the coarse shadings are the grid cubes reached by the contracted fibres. All the
properties of `TwoScaleAt` follow from a few counting facts:

* the fine mass of a fibre is at most its size times the number of its cubes times
  `O(ρ δ²)`, which gives the coarse mass;
* a point of high fine multiplicity sees many fibres, each of which reaches its cube,
  which gives the coarse multiplicity lower bound and hence the coarse volume bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate enumerate enumerate_mem
  enumerate_injective enumerate_surjective enumerate_count enumerate_sum ncard_setOf)

theorem mem_biUnion_gridCube_iff {s : ℝ} (hs : 0 < s) {M : Finset (Fin 3 → ℤ)} {q : Space} :
    q ∈ ⋃ m ∈ M, gridCube s m ↔ cubeIndex s q ∈ M := by
  constructor
  · intro hq
    obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
    rwa [cubeIndex_eq_of_mem hs hqm]
  · intro hq
    exact mem_iUnion₂.mpr ⟨_, hq, mem_gridCube_cubeIndex hs q⟩

theorem volume_biUnion_gridCube {s : ℝ} (hs : 0 < s) (M : Finset (Fin 3 → ℤ)) :
    volume (⋃ m ∈ M, gridCube s m) = M.card * ENNReal.ofReal s ^ 3 := by
  rw [measure_biUnion_finset (fun m _ m' _ hmm => gridCube_disjoint hs hmm)
    (fun m _ => measurableSet_gridCube s m)]
  simp only [volume_gridCube hs, Finset.sum_const, nsmul_eq_mul]

theorem measurableSet_biUnion_gridCube (s : ℝ) (M : Finset (Fin 3 → ℤ)) :
    MeasurableSet (⋃ m ∈ M, gridCube s m) :=
  Finset.measurableSet_biUnion M fun m _ => measurableSet_gridCube s m

/-- The contracted fibre of shadings in the unit ball lies in the ball of radius `2`. -/
theorem smul_fibreUnion_subset_ball {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 100)
    {n k : ℕ} {Y : Fin n → Set Space} (hYball : ∀ i, Y i ⊆ ball 0 1) (fc : Fin n → Fin k)
    (j : Fin k) : (1 - 2 * (16 * ρ)) • fibreUnion fc Y j ⊆ ball 0 2 := by
  have hl0 : 0 < 1 - 2 * (16 * ρ) := by linarith
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, -, hpi⟩ := mem_fibreUnion.mp hp
  have h1 := hYball i hpi
  rw [mem_ball_zero_iff] at h1 ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hl0]
  nlinarith [norm_nonneg p]

/-- The shadings of one fibre lie in the preimages of its reached cubes, each of which
meets a fine tube in volume `O(ρ δ²)`. -/
theorem fibre_mass_le_cubes {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 100)
    {n k : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1)
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hYball : ∀ i, Y i ⊆ ball 0 1)
    (fc : Fin n → Fin k) (K : ℕ) (hK : 2 / ρ + 1 ≤ K) (j : Fin k) :
    ∑ i ∈ Finset.univ.filter (fun i => fc i = j), (volume (Y i)).toReal ≤
      ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) *
        ((reachedF ρ K ((1 - 2 * (16 * ρ)) • fibreUnion fc Y j)).card *
          (2688 * ρ * δ ^ 2)) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  set lam : ℝ := 1 - 2 * (16 * ρ) with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  set M := reachedF ρ K (lam • fibreUnion fc Y j) with hM
  have hcov := subset_iUnion_reachedF hρ0 hK (smul_fibreUnion_subset_ball hρ0.le hρ hYball fc j)
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => fc i = j),
      (volume (Y i)).toReal ≤ M.card * (2688 * ρ * δ ^ 2) := by
    intro i hi
    have hij : fc i = j := (Finset.mem_filter.mp hi).2
    have hsub : Y i ⊆ ⋃ m ∈ M, (Tube δ (x i) (v i) ∩ lam⁻¹ • gridCube ρ m) := by
      intro p hp
      have hlp : lam • p ∈ ⋃ m ∈ M, gridCube ρ m :=
        hcov ⟨p, mem_fibreUnion.mpr ⟨i, hij, hp⟩, rfl⟩
      obtain ⟨m, hm, hpm⟩ := mem_iUnion₂.mp hlp
      refine mem_iUnion₂.mpr ⟨m, hm, hYT i hp, ?_⟩
      exact ⟨lam • p, hpm, by simp only [smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]⟩
    have h1 := (measure_mono (μ := volume) hsub).trans (measure_biUnion_finset_le M _)
    have h2 : ∑ m ∈ M, volume (Tube δ (x i) (v i) ∩ lam⁻¹ • gridCube ρ m) ≤
        ∑ m ∈ M, ENNReal.ofReal (2688 * ρ * δ ^ 2) :=
      Finset.sum_le_sum fun m _ => volume_Tube_inter_cube_le hδ hδρ hρ (x i) (v i) (hv i) m
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 := h1.trans h2
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h3
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h3
  calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i => fc i = j), ((M.card : ℝ) * (2688 * ρ * δ ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Packaging: the final fine shadings and the selected coarse tubes, shaded by the grid
cubes reached by their contracted fibres, satisfy `TwoScaleAt`. -/
theorem two_scale_package {σ ε ηs δ ρ θ θc μ L R Fmax : ℝ} {K : ℕ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 10 ^ 12) (hηsε : ηs ≤ ε)
    {n : ℕ} (hn : 0 < n) {x v : Fin n → Space} {Y Y' : Fin n → Set Space}
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYball : ∀ i, Y i ⊆ ball 0 1)
    (hY'Y : ∀ i, Y' i ⊆ Y i) (hY'm : ∀ i, MeasurableSet (Y' i))
    {k : ℕ} (hk : 0 < k) {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) (fc : Fin n → Fin k)
    (hfc : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (fc i)) (w (fc i)))
    (hsepρ : ∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j)))
    (huniq : ∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j))
    (hfull : ∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j))
    (hbalρ : ∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) ≤
      δ ^ (-ε) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')}.ncard : ℝ))
    (hfrostρ : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ε) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) *
          volume W)
    (hdilρ : ∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
      Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')
    (Q : Finset (Fin k)) (hY'Q : ∀ i, fc i ∉ Q → Y' i = ∅)
    (hQball : ∀ j, ntube (8 * ρ) (16 * ρ) (z j) (w j) ⊆ ball 0 1)
    (hQhalf : ∀ j ∈ Q, ∀ j' ∈ Q, j ≠ j' →
      volume (ntube (8 * ρ) (16 * ρ) (z j) (w j) ∩ ntube (8 * ρ) (16 * ρ) (z j') (w j')) ≤
        (1 / 2 : ℝ≥0∞) * volume (ntube (8 * ρ) (16 * ρ) (z j) (w j)))
    (hQsep : Q.Nonempty → Separated ηs (8 * ρ) Q.card
      (fun a => (1 - 2 * (16 * ρ)) • z (enumerate Q a) - (16 * ρ) • w (enumerate Q a))
      (fun a => w (enumerate Q a)))
    (hFmax : ∀ j, ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) ≤ Fmax)
    (hfib : ∀ j p, ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ θ * Fmax)
    (hcoarse : ∀ m, ((Q.filter (fun j =>
      m ∈ reachedF ρ K ((1 - 2 * (16 * ρ)) • fibreUnion fc Y' j))).card : ℝ) ≤ θc * Q.card)
    (hfine : ∀ p ∈ ⋃ i, Y' i, L < incidence Y' p)
    (hbal : ∃ θb : ℝ, 0 < θb ∧ ∀ m,
      (gridCube ρ m ∩ (1 - 2 * (16 * ρ)) • ⋃ i, Y' i).Nonempty →
        ENNReal.ofReal θb * volume (gridCube ρ m) ≤
          volume (((1 - 2 * (16 * ρ)) • ⋃ i, Y' i) ∩ gridCube ρ m) ∧
        volume (((1 - 2 * (16 * ρ)) • ⋃ i, Y' i) ∩ gridCube ρ m) ≤
          ENNReal.ofReal (δ ^ (-ε) * θb) * volume (gridCube ρ m))
    (hmass : R * n * δ ^ 2 ≤ shadingMass Y')
    (hK : 2 / ρ + 1 ≤ K)
    (hRpos : 0 < R) (hRε : δ ^ ε ≤ R)
    (hFk : Fmax ≤ δ ^ (-ε) * ((n : ℝ) / k))
    (hθF : θ * Fmax ≤ (δ / (8 * ρ)) ^ (2 - σ - ε) * ((n : ℝ) / k))
    (hθFpos : 0 < θ * Fmax)
    (hLμ : (k : ℝ) * μ * (θ * Fmax) ≤ L)
    (hLfine : δ ^ (2 - σ + ε) * n ≤ L)
    (hμ : (8 * ρ) ^ (2 - σ + ε) ≤ μ) (hμpos : 0 < μ)
    (hcvol : 384 * (8 * ρ) ^ 2 / μ ≤ (8 * ρ) ^ (σ - ε))
    (hθc : θc ≤ (8 * ρ) ^ (2 - σ - ε))
    (hcmass : (8 * ρ) ^ ε * (8 * ρ) ^ 2 * k * (2688 * δ ^ 2 * Fmax) ≤
      R * n * δ ^ 2 * ρ ^ 2) :
    TwoScaleAt σ ε δ (8 * ρ) n x v Y := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hρ100 : ρ ≤ 1 / 100 := hρ.trans (by norm_num)
  set lam : ℝ := 1 - 2 * (16 * ρ) with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  have hl1 : lam ≤ 1 := by rw [hlam]; linarith
  have hlam' : (1 - 4 * (8 * ρ)) = lam := by rw [hlam]; ring
  unfold TwoScaleAt
  rw [hlam']
  -- the selected coarse tubes are not all empty
  have hmasspos : 0 < shadingMass Y' := lt_of_lt_of_le (by positivity) hmass
  have hY'ne : ∀ i, (Y' i).Nonempty → fc i ∈ Q := by
    intro i hne
    by_contra h
    rw [hY'Q i h] at hne
    exact Set.not_nonempty_empty hne
  have hQne : Q.Nonempty := by
    by_contra hQe
    rw [Finset.not_nonempty_iff_eq_empty] at hQe
    have : shadingMass Y' = 0 := by
      unfold shadingMass
      apply Finset.sum_eq_zero
      intro i _
      rw [hY'Q i (by rw [hQe]; exact Finset.notMem_empty _), measure_empty, ENNReal.toReal_zero]
    linarith
  obtain ⟨j0, hj0⟩ := hQne
  have hk'pos : 0 < Q.card := Finset.card_pos.mpr ⟨j0, hj0⟩
  have hk'k : (Q.card : ℝ) ≤ k := by
    exact_mod_cast (Finset.card_le_univ Q).trans (Fintype.card_fin k).le
  set Mc : Fin k → Finset (Fin 3 → ℤ) := fun j => reachedF ρ K (lam • fibreUnion fc Y' j)
    with hMc
  set a : Fin n → Fin Q.card := fun i => Q.equivFin ⟨if fc i ∈ Q then fc i else j0, by
    split_ifs with h
    exacts [h, hj0]⟩ with ha
  have hea : ∀ i, fc i ∈ Q → enumerate Q (a i) = fc i := by
    intro i hi
    simp [ha, WangZahlLot.Obl.wz_separated_cover_refinement.enumerate, hi]
  have hae : ∀ i j, fc i = enumerate Q j → a i = j := by
    intro i j hij
    have hi : fc i ∈ Q := hij ▸ enumerate_mem Q j
    apply enumerate_injective Q
    rw [hea i hi, hij]
  have hY'ball : ∀ i, Y' i ⊆ ball 0 1 := fun i => (hY'Y i).trans (hYball i)
  have hball2 : ∀ j, lam • fibreUnion fc Y' j ⊆ ball 0 2 :=
    smul_fibreUnion_subset_ball hρ0.le hρ100 hY'ball fc
  have hcov : ∀ j, lam • fibreUnion fc Y' j ⊆ ⋃ m ∈ Mc j, gridCube ρ m := fun j =>
    subset_iUnion_reachedF hρ0 hK (hball2 j)
  have hMc_reached : ∀ j, ∀ m ∈ Mc j, ∃ p ∈ fibreUnion fc Y' j, lam • p ∈ gridCube ρ m := by
    intro j m hm
    obtain ⟨-, q, hqm, hq⟩ := Finset.mem_filter.mp hm
    obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.mp hq
    exact ⟨p, hp, hqm⟩
  -- the coarse family
  set Yt : Fin Q.card → Set Space := fun b => ⋃ m ∈ Mc (enumerate Q b), gridCube ρ m
    with hYt
  set z' : Fin Q.card → Space := fun b => lam • z (enumerate Q b) - (16 * ρ) • w (enumerate Q b)
    with hz'
  set w' : Fin Q.card → Space := fun b => w (enumerate Q b) with hw'
  have hYtm : ∀ b, MeasurableSet (Yt b) := fun b => measurableSet_biUnion_gridCube ρ _
  have hYtsub : ∀ b, Yt b ⊆ Tube (8 * ρ) (z' b) (w' b) := by
    intro b q hq
    obtain ⟨m, hm, hqm⟩ := mem_iUnion₂.mp hq
    obtain ⟨p, hp, hpm⟩ := hMc_reached _ m hm
    obtain ⟨i, hi, hpi⟩ := mem_fibreUnion.mp hp
    have hmr : m ∈ reached ρ ((1 - 2 * (16 * ρ)) •
        Tube ρ (z (enumerate Q b)) (w (enumerate Q b))) :=
      ⟨lam • p, hpm, ⟨p, by rw [← hi]; exact hfc i (hYT i (hY'Y i hpi)), rfl⟩⟩
    exact gridCube_subset_ntube hρ0 hρ100 hmr hqm
  have hYtfin : ∀ b, volume (Yt b) ≠ ⊤ := fun b =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hYtsub b).trans (hQball (enumerate Q b))))
  -- coarse multiplicity lower bound
  have hcl : ∀ q ∈ ⋃ b, Yt b, (k : ℝ) * μ ≤ (fineMult Yt q : ℝ) := by
    intro q hq
    obtain ⟨b0, hb0⟩ := mem_iUnion.mp hq
    have hm0 : cubeIndex ρ q ∈ Mc (enumerate Q b0) := (mem_biUnion_gridCube_iff hρ0).mp hb0
    obtain ⟨p, hp, hpm⟩ := hMc_reached _ _ hm0
    obtain ⟨i0, -, hpi0⟩ := mem_fibreUnion.mp hp
    set J := Q.filter (fun j => cubeIndex ρ q ∈ Mc j) with hJ
    have hfm : fineMult Yt q = J.card := by
      unfold fineMult
      have heq : {b | q ∈ Yt b} = {b | cubeIndex ρ q ∈ Mc (enumerate Q b)} := by
        ext b; exact mem_biUnion_gridCube_iff hρ0
      rw [heq, enumerate_count Q (fun j => cubeIndex ρ q ∈ Mc j)]
    have hinc := hfine p (mem_iUnion.mpr ⟨i0, hpi0⟩)
    rw [incidence_eq_ncard] at hinc
    have hsplit : ({i | p ∈ Y' i}.ncard : ℝ) = ∑ j, ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) := by
      simp only [ncard_setOf]
      rw [← Nat.cast_sum]
      congr 1
      rw [Finset.card_eq_sum_card_fiberwise (f := fc) (t := Finset.univ)
        (fun i _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ext i
      simp [and_comm]
    have hzero : ∀ j, j ∉ J → ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) = 0 := by
      intro j hj
      have : {i | fc i = j ∧ p ∈ Y' i} = ∅ := by
        ext i
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hij hpi
        apply hj
        rw [hJ, Finset.mem_filter]
        refine ⟨hij ▸ hY'ne i ⟨p, hpi⟩, ?_⟩
        exact mem_reachedF hρ0 hK (hball2 j)
          ⟨lam • p, hpm, ⟨p, mem_fibreUnion.mpr ⟨i, hij, hpi⟩, rfl⟩⟩
      rw [this, Set.ncard_empty, Nat.cast_zero]
    have hle : ∑ j, ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ J.card * (θ * Fmax) := by
      rw [← Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => hzero j hj)]
      calc _ ≤ ∑ j ∈ J, θ * Fmax := Finset.sum_le_sum fun j _ => hfib j p
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h1 : (k : ℝ) * μ * (θ * Fmax) < J.card * (θ * Fmax) := by linarith
    have h2 := lt_of_mul_lt_mul_right h1 hθFpos.le
    rw [hfm]; exact h2.le
  refine ⟨Y', Q.card, z', w', Yt, a, ρ, fun b => Mc (enumerate Q b), hY'Y, hY'm, ?mass, ?fam,
    ?sep, ?vol, ?cover, ?dir, hρ0, fun b => rfl, ?fine, ?fib, ?cup, ?clow, ?R1, ?R2, ?P1a, ?P1b,
    ?P2, ?P3⟩
  case mass =>
    have hfin : ∀ i, volume (Y' i) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (hY'ball i))
    have h1 : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ shadingMass Y' := le_trans (by gcongr) hmass
    calc ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (shadingMass Y') :=
          ENNReal.ofReal_le_ofReal h1
      _ = ∑ i, volume (Y' i) := by
        rw [shadingMass, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_toReal (hfin i)
  case fam =>
    refine ⟨hk'pos, fun b => hw _, fun b => hQball (enumerate Q b), ?_, hYtm, hYtsub, ?_⟩
    · intro b b' hbb
      exact hQhalf _ (enumerate_mem Q b) _ (enumerate_mem Q b')
        (fun h => hbb (enumerate_injective Q h))
    · -- coarse mass: each fibre's mass is at most its size times its cubes times `O(ρ δ²)`
      have hFpos : 0 < Fmax := by
        set i0 : Fin n := ⟨0, hn⟩
        have h0 : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => fc i = fc i0)).card : ℝ) := by
          have : 0 < (Finset.univ.filter (fun i => fc i = fc i0)).card :=
            Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
          exact_mod_cast this
        linarith [hFmax (fc i0)]
      have hsplit : shadingMass Y' = ∑ j ∈ Q, ∑ i ∈ Finset.univ.filter (fun i => fc i = j),
          (volume (Y' i)).toReal := by
        rw [shadingMass, ← Finset.sum_fiberwise Finset.univ fc
          (fun i => (volume (Y' i)).toReal)]
        symm
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro j _ hj
        apply Finset.sum_eq_zero
        intro i hi
        have hiQ : fc i ∉ Q := by rw [(Finset.mem_filter.mp hi).2]; exact hj
        rw [hY'Q i hiQ, measure_empty, ENNReal.toReal_zero]
      have hbound : shadingMass Y' ≤ ∑ j ∈ Q, Fmax * ((Mc j).card * (2688 * ρ * δ ^ 2)) := by
        rw [hsplit]
        apply Finset.sum_le_sum
        intro j _
        refine (fibre_mass_le_cubes hδ hδρ hρ100 hv (fun i => (hY'Y i).trans (hYT i)) hY'ball
          fc K hK j).trans ?_
        exact mul_le_mul_of_nonneg_right (hFmax j) (by positivity)
      have hS : ∑ b, volume (Yt b) =
          ENNReal.ofReal ((∑ j ∈ Q, ((Mc j).card : ℝ)) * ρ ^ 3) := by
        have h1 : ∑ b, volume (Yt b) = ∑ j ∈ Q, volume (⋃ m ∈ Mc j, gridCube ρ m) :=
          enumerate_sum Q (fun j => volume (⋃ m ∈ Mc j, gridCube ρ m))
        rw [h1, ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _),
          ENNReal.ofReal_pow hρ0.le, ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _),
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [volume_biUnion_gridCube hρ0, ENNReal.ofReal_natCast]
      rw [hS]
      apply ENNReal.ofReal_le_ofReal
      set S := ∑ j ∈ Q, ((Mc j).card : ℝ) with hSdef
      have h1 : R * n * δ ^ 2 ≤ Fmax * (2688 * ρ * δ ^ 2) * S := by
        refine hmass.trans (hbound.trans_eq ?_)
        rw [hSdef, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hc : 0 < 2688 * δ ^ 2 * Fmax := by positivity
      have h2 : (8 * ρ) ^ ε * (8 * ρ) ^ 2 * k * (2688 * δ ^ 2 * Fmax) ≤
          (S * ρ ^ 3) * (2688 * δ ^ 2 * Fmax) := by
        calc _ ≤ R * n * δ ^ 2 * ρ ^ 2 := hcmass
          _ ≤ Fmax * (2688 * ρ * δ ^ 2) * S * ρ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (S * ρ ^ 3) * (2688 * δ ^ 2 * Fmax) := by ring
      have h3 := le_of_mul_le_mul_right h2 hc
      calc (8 * ρ) ^ ε * (Q.card : ℝ) * (8 * ρ) ^ 2
          ≤ (8 * ρ) ^ ε * (k : ℝ) * (8 * ρ) ^ 2 := by gcongr
        _ = (8 * ρ) ^ ε * (8 * ρ) ^ 2 * k := by ring
        _ ≤ S * ρ ^ 3 := h3
  case sep =>
    exact (hQsep ⟨j0, hj0⟩).mono_error (by positivity) (by linarith) hηsε
  case vol =>
    have hvolb : ∀ b, (volume (Yt b)).toReal ≤ 384 * (8 * ρ) ^ 2 := by
      intro b
      have h := (measure_mono (hYtsub b)).trans
        (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le (δ := 8 * ρ) (by positivity)
          (by linarith) (z' b) (w' b) (hw _))
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
    have hmassYt : shadingMass Yt ≤ Q.card * (384 * (8 * ρ) ^ 2) := by
      calc shadingMass Yt ≤ ∑ _b : Fin Q.card, (384 * (8 * ρ) ^ 2 : ℝ) :=
            Finset.sum_le_sum fun b _ => hvolb b
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hhi := high_incidence_volume hYtm hYtfin ((k : ℝ) * μ)
    have hUfin : volume (⋃ b, Yt b) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (iUnion_subset fun b =>
        (hYtsub b).trans (hQball (enumerate Q b))))
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hsub : (⋃ b, Yt b) ⊆ {q | (k : ℝ) * μ ≤ incidence Yt q} := by
      intro q hq
      show (k : ℝ) * μ ≤ incidence Yt q
      rw [incidence_eq_ncard]
      exact hcl q hq
    have hsub2 : {q | (k : ℝ) * μ ≤ incidence Yt q} ⊆ ⋃ b, Yt b := by
      intro q hq
      by_contra h
      have h0 := incidence_eq_zero_of_notMem Yt h
      have hq' : (k : ℝ) * μ ≤ incidence Yt q := hq
      have : 0 < (k : ℝ) * μ := by positivity
      linarith
    have heq : {q | (k : ℝ) * μ ≤ incidence Yt q} = ⋃ b, Yt b := Subset.antisymm hsub2 hsub
    rw [heq] at hhi
    have h1 : (volume (⋃ b, Yt b)).toReal ≤ 384 * (8 * ρ) ^ 2 / μ := by
      rw [le_div_iff₀ hμpos]
      have h2 : (k : ℝ) * μ * (volume (⋃ b, Yt b)).toReal ≤ k * (384 * (8 * ρ) ^ 2) := by
        calc _ ≤ shadingMass Yt := hhi
          _ ≤ Q.card * (384 * (8 * ρ) ^ 2) := hmassYt
          _ ≤ k * (384 * (8 * ρ) ^ 2) := mul_le_mul_of_nonneg_right hk'k (by positivity)
      have h3 : (k : ℝ) * ((volume (⋃ b, Yt b)).toReal * μ) ≤ k * (384 * (8 * ρ) ^ 2) := by
        linarith
      exact le_of_mul_le_mul_left h3 hk0
    rw [← ENNReal.ofReal_toReal hUfin]
    exact ENNReal.ofReal_le_ofReal (h1.trans hcvol)
  case cover =>
    intro i
    by_cases hne : (Y' i).Nonempty
    · have hi := hY'ne i hne
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.mp hq
      show lam • p ∈ ⋃ m ∈ Mc (enumerate Q (a i)), gridCube ρ m
      rw [hea i hi]
      exact hcov (fc i) ⟨p, mem_fibreUnion.mpr ⟨i, rfl, hp⟩, rfl⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.smul_set_empty]
      exact empty_subset _
  case dir =>
    intro i hne
    have hi := hY'ne i hne
    show min ‖v i - w (enumerate Q (a i))‖ ‖v i + w (enumerate Q (a i))‖ ≤ 8 * ρ / 2
    rw [hea i hi]
    have := dir_close_of_subset hδ (hv i) (hw (fc i)) (hfc i)
    linarith
  case fine =>
    intro p hp
    have h := hfine p hp
    rw [incidence_eq_ncard] at h
    unfold fineMult
    exact hLfine.trans h.le
  case fib =>
    intro b p
    have hsub : {i | a i = b ∧ p ∈ Y' i} ⊆ {i | fc i = enumerate Q b ∧ p ∈ Y' i} := by
      rintro i ⟨hab, hp⟩
      refine ⟨?_, hp⟩
      rw [← hab, hea i (hY'ne i ⟨p, hp⟩)]
    calc ({i | a i = b ∧ p ∈ Y' i}.ncard : ℝ)
        ≤ ({i | fc i = enumerate Q b ∧ p ∈ Y' i}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ θ * Fmax := hfib _ p
      _ ≤ (δ / (8 * ρ)) ^ (2 - σ - ε) * ((n : ℝ) / k) := hθF
      _ ≤ (δ / (8 * ρ)) ^ (2 - σ - ε) * ((n : ℝ) / Q.card) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hk'pos) hk'k
  case cup =>
    intro q
    unfold fineMult
    have heq : {b | q ∈ Yt b} = {b | cubeIndex ρ q ∈ Mc (enumerate Q b)} := by
      ext b; exact mem_biUnion_gridCube_iff hρ0
    rw [heq, enumerate_count Q (fun j => cubeIndex ρ q ∈ Mc j)]
    exact (hcoarse (cubeIndex ρ q)).trans (mul_le_mul_of_nonneg_right hθc (Nat.cast_nonneg _))
  case clow =>
    intro q hq
    refine le_trans ?_ (hcl q hq)
    calc (8 * ρ) ^ (2 - σ + ε) * (Q.card : ℝ) ≤ μ * Q.card :=
          mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg _)
      _ ≤ μ * k := mul_le_mul_of_nonneg_left hk'k hμpos.le
      _ = k * μ := by ring
  case R1 =>
    intro b m hm
    obtain ⟨p, hp, hpm⟩ := hMc_reached _ m hm
    obtain ⟨i, hi, hpi⟩ := mem_fibreUnion.mp hp
    exact ⟨i, hae i b hi, p, hpi, hpm⟩
  case R2 =>
    refine ⟨ρ, k, z, w, enumerate Q, hδρ, by linarith, by linarith, enumerate_injective Q, hk,
      hw, hsepρ, huniq, hfull, hbalρ, hfrostρ, hdilρ, ?_⟩
    intro i hne
    have := hea i (hY'ne i hne)
    show Tube δ (x i) (v i) ⊆ Tube ρ (z (enumerate Q (a i))) (w (enumerate Q (a i)))
    rw [this]; exact hfc i
  case P1a => linarith
  case P1b => linarith
  case P2 =>
    intro b
    have hsub : {i | a i = b ∧ (Y' i).Nonempty} ⊆ {i | fc i = enumerate Q b} := by
      rintro i ⟨hab, hne⟩
      show fc i = enumerate Q b
      rw [← hab, hea i (hY'ne i hne)]
    calc ({i | a i = b ∧ (Y' i).Nonempty}.ncard : ℝ)
        ≤ ({i | fc i = enumerate Q b}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ((Finset.univ.filter (fun i => fc i = enumerate Q b)).card : ℝ) := by
          rw [ncard_setOf]
      _ ≤ Fmax := hFmax _
      _ ≤ δ ^ (-ε) * ((n : ℝ) / k) := hFk
      _ ≤ δ ^ (-ε) * ((n : ℝ) / Q.card) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hk'pos) hk'k
  case P3 =>
    obtain ⟨θb, hθb, hb⟩ := hbal
    refine ⟨θb, hθb, fun b m hm => ?_⟩
    have hU : (⋃ i, lam • Y' i) = lam • ⋃ i, Y' i := (Set.smul_set_iUnion _ _).symm
    rw [hU]
    apply hb m
    obtain ⟨p, hp, hpm⟩ := hMc_reached _ m hm
    obtain ⟨i, -, hpi⟩ := mem_fibreUnion.mp hp
    exact ⟨lam • p, hpm, ⟨p, mem_iUnion.mpr ⟨i, hpi⟩, rfl⟩⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
