-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSAssemble.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSPackage
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSBalance

/-!
# Assembly of the two-scale decomposition

Fibre deletion, coarse selection, coarse deletion, low-multiplicity trimming and
balancing, performed in this order, produce the data of `TwoScaleAt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate enumerate enumerate_mem
  enumerate_injective enumerate_surjective enumerate_count enumerate_sum ncard_setOf)

/-- A fibre of a balanced assignment has at most `c` times the average size. -/
theorem fibre_le_avg {n k : ℕ} (hk : 0 < k) (fc : Fin n → Fin k) {c : ℝ}
    (hA : ∀ j j', ({i | fc i = j}.ncard : ℝ) ≤ c * ({i | fc i = j'}.ncard : ℝ)) (j : Fin k) :
    ({i | fc i = j}.ncard : ℝ) ≤ c * ((n : ℝ) / k) := by
  classical
  have hsum : ∑ j' : Fin k, ({i | fc i = j'}.ncard : ℝ) = n := by
    simp only [ncard_setOf]
    rw [← Nat.cast_sum]
    congr 1
    rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (fc i))]
    simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) * ({i | fc i = j}.ncard : ℝ) ≤ c * n := by
    calc (k : ℝ) * ({i | fc i = j}.ncard : ℝ) = ∑ _j' : Fin k, ({i | fc i = j}.ncard : ℝ) := by
          simp
      _ ≤ ∑ j' : Fin k, c * ({i | fc i = j'}.ncard : ℝ) :=
          Finset.sum_le_sum fun j' _ => hA j j'
      _ = c * n := by rw [← Finset.mul_sum, hsum]
  rw [mul_div_assoc', le_div_iff₀ hk']
  linarith

/-- The box of cube indices of side `ρ` around the ball of radius `2` has `O(ρ⁻³)` cubes. -/
theorem cubeBox_card_mul_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 5) :
    ((cubeBox (⌈2 / ρ⌉₊ + 1)).card : ℝ) * (8 * ρ ^ 3) ≤ 1000 := by
  have hcard : (cubeBox (⌈2 / ρ⌉₊ + 1)).card = (2 * (⌈2 / ρ⌉₊ + 1) + 1) ^ 3 := by
    simp only [cubeBox, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    omega
  rw [hcard]
  push_cast
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / ρ by positivity)
  have h5 : 2 * ((⌈2 / ρ⌉₊ : ℝ) + 1) + 1 ≤ 5 / ρ := by
    have : (2 : ℝ) * (2 / ρ + 1 + 1) + 1 ≤ 5 / ρ := by
      rw [show (2 : ℝ) * (2 / ρ + 1 + 1) + 1 = 4 / ρ + 5 by ring]
      have : 5 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
      have h4 : 4 / ρ + 5 ≤ 4 / ρ + 1 / ρ := by linarith
      calc 4 / ρ + 5 ≤ 4 / ρ + 1 / ρ := h4
        _ = 5 / ρ := by ring
    linarith
  have h0 : 0 ≤ 2 * ((⌈2 / ρ⌉₊ : ℝ) + 1) + 1 := by positivity
  calc (2 * ((⌈2 / ρ⌉₊ : ℝ) + 1) + 1) ^ 3 * (8 * ρ ^ 3) ≤ (5 / ρ) ^ 3 * (8 * ρ ^ 3) := by
        gcongr
    _ = 1000 := by field_simp; norm_num

/-- The two-scale decomposition at one scale, given the volume lower bounds at the
finer rescaled scale and at the coarse scale, and the parameter inequalities. -/
theorem two_scale_core {σ ε ε1 ε2 η ηs t δ ρ a b δ' tc tcc θ τ β : ℝ} {Lb : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) (hη : 0 < η) (hηε : η ≤ ε) (hε1 : ε1 ≤ ε) (hε2 : ε2 ≤ ε)
    (hηsε : ηs ≤ ε)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : Family η δ n x v Y) (hS : Separated η δ n x v)
    (hvol : volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)))
    {k : ℕ} {z w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1)
    (hsepρ : ∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j)))
    (huniq : ∀ i, ∃! j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j))
    (hfull : ∀ j, ∃ i, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j))
    (hbalρ : ∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) ≤
      δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')}.ncard : ℝ))
    (hfrostρ : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) *
          volume W)
    (hdilρ : ∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ (z j) (w j) →
      tube δ (x i) (v i) ⊆ dilatedTube ρ (z j') (w j') → j = j')
    (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 10 ^ 12)
    -- lower bounds
    (hlowf : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs δ' m x' v' Y' → Separated ηs δ' m x' v' →
        ENNReal.ofReal (δ' ^ t) < volume (⋃ q, Y' q))
    (hlowc : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs (8 * ρ) m x' v' Y' → Separated ηs (8 * ρ) m x' v' →
        ENNReal.ofReal ((8 * ρ) ^ t) < volume (⋃ q, Y' q))
    -- fibre rescaling parameters
    (ha : a = (1 / 100) / ρ) (hb : b = 1 / (1 + 144 * (1 / 100) ^ 2)) (hδ'def : δ' = b * a * δ)
    (hδ'small : δ' ≤ 1 / 10000000)
    (hC2a : 34 * δ ^ (-(2 * η)) ≤ δ' ^ (-ηs))
    (hC2b : δ' ^ ηs ≤ δ ^ (2 * η) / (34 * 10 ^ 7))
    (htc : tc = 2312 * δ ^ (-η) / (1 / 100) ^ 2 * δ' ^ ηs)
    (hθ : θ = (δ / (8 * ρ)) ^ (2 - σ - ε2) * δ ^ η)
    (hτ : τ = ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) *
      (2 * δ' ^ ηs + 384 * tc * ((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ)))
    (hunionf : b ^ 3 * a ^ 2 * (384 * δ ^ 2 / θ) ≤ δ' ^ t)
    -- coarse selection parameters
    (hP1a : 8 * δ ^ (-(2 * η)) ≤ (8 * ρ) ^ (-ηs))
    (hP1b : (8 * ρ) ^ ηs ≤ δ ^ (2 * η) / (4 * 10 ^ 9))
    (htcc : tcc = 32 * (δ ^ (-η)) ^ 3 * (8 * ρ) ^ ηs)
    -- coarse deletion
    (hunionc : 24576 * ρ ^ 2 / (8 * ρ) ^ (2 - σ - ε) ≤ (8 * ρ) ^ t)
    -- balancing
    (hβ : β = δ ^ ε)
    -- mass budget
    (hmass : max (δ ^ ε) (172032 * (8 * ρ) ^ ε * δ ^ (-η)) ≤
      ((((δ ^ η - τ) / ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) -
          384 * δ ^ (-η) * tcc * ((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ)) -
          172032 * (8 * ρ) ^ ηs * δ ^ (-η) - δ ^ (ε1 - η)) - 1000 * β ^ (Lb + 1) / δ ^ 2) /
        (Lb + 1))
    -- final exponents
    (hcvol : 24576 * ρ ^ 2 / ((8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2)) ≤ (8 * ρ) ^ (σ - ε))
    (hclow : (8 * ρ) ^ (2 - σ + ε) ≤ (8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2)) :
    TwoScaleAt σ ε δ (8 * ρ) n x v Y := by
  classical
  obtain ⟨hn, hv, hball, hhalf, hYm, hYT, -⟩ := id hF
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hδ1' : δ ≤ 1 := by linarith
  have hρ100 : ρ ≤ 1 / 100 := hρ.trans (by norm_num)
  have hρ1000 : ρ ≤ 1 / 1000 := hρ.trans (by norm_num)
  have h8ρ1 : 8 * ρ ≤ 1 := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- fine-to-coarse assignment
  choose fc hfc using fun i => (huniq i).exists
  have hfcu : ∀ i j, tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) → j = fc i :=
    fun i j h => (huniq i).unique h (hfc i)
  have hk : 0 < k := Fin.pos (fc ⟨0, hn⟩)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hset : ∀ j, {i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)} = {i | fc i = j} := by
    intro j; ext i
    constructor
    · intro h; exact (hfcu i j h).symm
    · intro h; show tube δ (x i) (v i) ⊆ tube ρ (z j) (w j); rw [← (h : fc i = j)]; exact hfc i
  have hbalF : ∀ j j', ({i | fc i = j}.ncard : ℝ) ≤ δ ^ (-η) * ({i | fc i = j'}.ncard : ℝ) := by
    intro j j'
    have := hbalρ j j'
    rwa [hset, hset] at this
  set Fmax : ℝ := δ ^ (-η) * ((n : ℝ) / k) with hFmax_def
  have hFmaxpos : 0 < Fmax := by positivity
  have hFmaxN : ∀ j, ({i | fc i = j}.ncard : ℝ) ≤ Fmax := fibre_le_avg hk fc hbalF
  have hFmaxF : ∀ j, ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) ≤ Fmax := by
    intro j; rw [← ncard_setOf]; exact hFmaxN j
  -- fibre deletion
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hδ'pos : 0 < δ' := by rw [hδ'def, hb, ha]; positivity
  have htcpos : 0 < tc := by rw [htc]; positivity
  have hC2c : 2312 * δ ^ (-η) / (1 / 100) ^ 2 / tc ≤ δ' ^ (-ηs) := by
    rw [htc, Real.rpow_neg hδ'pos.le]
    apply le_of_eq
    have h1 : 0 < δ ^ (-η) := by positivity
    have h2 : 0 < δ' ^ ηs := by positivity
    field_simp
  have hsmall : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => fc i = j),
      (volume (Y i ∩ {p | θ * ({i | fc i = j}.ncard : ℝ) <
        incidence (fibreShading fc Y j) p})).toReal ≤
      τ * ({i | fc i = j}.ncard : ℝ) * δ ^ 2 :=
    fun j => fibre_high_small (lam0 := 1 / 100) hδ hδ1 hη hv hball hhalf hYm hYT hS huniq
      hfrostρ hdilρ j (hw j) hδρ hρ1000 le_rfl hρ100 (by norm_num) ha hb hδ'def hδ'small hC2a
      hC2b hC2c htcpos hlowf hθpos hτ hunionf fc hfc
  have hYfin : ∀ i, volume (Y i) ≠ ⊤ := hF.shading_finite
  obtain ⟨Yb, hYbY, hYbm, hYbmass, hYbfib⟩ := fibre_deletion_all hθpos hYm hYfin fc hsmall
  -- coarse selection
  set ω : Fin k → ℝ := fun j => ∑ i ∈ Finset.univ.filter (fun i => fc i = j),
    (volume (Yb i)).toReal with hω
  have hω0 : ∀ j, 0 ≤ ω j := fun j => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hYbvol : ∀ i, (volume (Yb i)).toReal ≤ 384 * δ ^ 2 := by
    intro i
    have h := (measure_mono ((hYbY i).trans (hYT i))).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1' (x i) (v i) (hv i))
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  set Mw : ℝ := 384 * δ ^ 2 * Fmax with hMw
  have hωM : ∀ j, ω j ≤ Mw := by
    intro j
    calc ω j ≤ ∑ i ∈ Finset.univ.filter (fun i => fc i = j), (384 * δ ^ 2 : ℝ) :=
          Finset.sum_le_sum fun i _ => hYbvol i
      _ = ((Finset.univ.filter (fun i => fc i = j)).card : ℝ) * (384 * δ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fmax * (384 * δ ^ 2) := mul_le_mul_of_nonneg_right (hFmaxF j) (by positivity)
      _ = Mw := by rw [hMw]; ring
  have hMwpos : 0 < Mw := by positivity
  have htccpos : 0 < tcc := by rw [htcc]; positivity
  have hP2 : 32 * (δ ^ (-η)) ^ 3 / tcc ≤ (8 * ρ) ^ (-ηs) := by
    rw [htcc, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 8 * ρ)]
    apply le_of_eq
    have : 0 < (δ ^ (-η)) ^ 3 := by positivity
    have : 0 < (8 * ρ) ^ ηs := by positivity
    field_simp
  obtain ⟨Q, hQhalf, hQsep, hQmass⟩ := coarse_family (η' := ηs) (t := tcc) hδ hδ1 hη hv hball
    hS hw hsepρ huniq hfull hbalρ hδρ hρ hP1a hP1b hP2 htccpos ω hω0 hωM hMwpos
  have hQball : ∀ j, ntube (8 * ρ) (16 * ρ) (z j) (w j) ⊆ ball 0 1 := by
    intro j
    obtain ⟨i, hi⟩ := hfull j
    apply ntube_subset_ball (by positivity) (by linarith) (hw j) (R := 1 + 3 * ρ)
    · intro s hs
      exact cover_axis_norm_le hδ (by linarith) (by linarith) (hv i) (hw j) (hball i) hi s hs
    · nlinarith
  -- restriction to the selected coarse tubes
  set Yc : Fin n → Set Space := fun i => if fc i ∈ Q then Yb i else ∅ with hYc
  have hYcm : ∀ i, MeasurableSet (Yc i) := by
    intro i; simp only [hYc]; split_ifs
    exacts [hYbm i, MeasurableSet.empty]
  have hYcYb : ∀ i, Yc i ⊆ Yb i := by
    intro i; simp only [hYc]; split_ifs
    exacts [subset_rfl, empty_subset _]
  have hYcQ : ∀ i, fc i ∉ Q → Yc i = ∅ := by
    intro i h; simp [hYc, h]
  have hYcmass : shadingMass Yc = ∑ j ∈ Q, ω j := by
    rw [shadingMass, ← Finset.sum_fiberwise Finset.univ fc (fun i => (volume (Yc i)).toReal)]
    have h0 : ∀ j ∈ Finset.univ, j ∉ Q →
        ∑ i ∈ Finset.univ.filter (fun i => fc i = j), (volume (Yc i)).toReal = 0 := by
      intro j _ hj
      apply Finset.sum_eq_zero
      intro i hi
      have hij : fc i = j := (Finset.mem_filter.mp hi).2
      rw [hYcQ i (by rw [hij]; exact hj), measure_empty, ENNReal.toReal_zero]
    rw [← Finset.sum_subset (Finset.subset_univ Q) h0]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hω]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : fc i = j := (Finset.mem_filter.mp hi).2
    have : Yc i = Yb i := by simp [hYc, hij, hj]
    rw [this]
  -- coarse cube deletion
  set lam : ℝ := 1 - 2 * (16 * ρ) with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  set K : ℕ := ⌈2 / ρ⌉₊ + 1 with hK_def
  have hK : 2 / ρ + 1 ≤ (K : ℝ) := by
    rw [hK_def]; push_cast; linarith [Nat.le_ceil (2 / ρ)]
  set θc : ℝ := (8 * ρ) ^ (2 - σ - ε) with hθc
  have hθcpos : 0 < θc := by positivity
  have hYcT : ∀ i, Yc i ⊆ Tube δ (x i) (v i) := fun i =>
    (hYcYb i).trans ((hYbY i).trans (hYT i))
  have hYcball : ∀ i, Yc i ⊆ ball 0 1 := fun i => (hYcT i).trans (hball i)
  have hhigh := coarse_high_small (ηs := ηs) (t := t) hδ hδρ hρ1000 hv hYcm hYcT hYcball hw fc
    hfc Q hYcQ hFmaxF hQball hQhalf hQsep hlowc hθcpos hunionc hFmaxpos.le K hK
  set U : Set Space := ⋃ m ∈ highCubes ρ K fc Yc Q θc, gridCube ρ m with hU
  have hUm : MeasurableSet U := measurableSet_biUnion_gridCube ρ _
  have hlUm : MeasurableSet (lam⁻¹ • U) := hUm.const_smul₀ lam⁻¹
  set Yd : Fin n → Set Space := fun i => Yc i ∩ (lam⁻¹ • U)ᶜ with hYd
  have hYdm : ∀ i, MeasurableSet (Yd i) := fun i => (hYcm i).inter hlUm.compl
  have hYcfin : ∀ i, volume (Yc i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono ((hYcYb i).trans (hYbY i)))
  have hYdmass : shadingMass Yc - 172032 * (8 * ρ) ^ ηs * Fmax * Q.card * δ ^ 2 ≤
      shadingMass Yd := by
    have h := shadingMass_restrict_add_compl hYcfin hlUm
    have h2 : shadingMass (fun i => Yc i ∩ lam⁻¹ • U) ≤
        172032 * (8 * ρ) ^ ηs * Fmax * Q.card * δ ^ 2 := hhigh
    linarith
  -- trimming of low multiplicity
  set L : ℝ := δ ^ (2 - σ + ε1) * n with hL
  have hLpos : 0 < L := by positivity
  have hYdY : ∀ i, Yd i ⊆ Y i := fun i =>
    inter_subset_left.trans ((hYcYb i).trans (hYbY i))
  have hYdU : volume (⋃ i, Yd i) ≤ ENNReal.ofReal (δ ^ (σ - η)) :=
    (measure_mono (iUnion_mono hYdY)).trans hvol
  have hYdfin : volume (⋃ i, Yd i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hYdU
  have hinc_le : ∀ p, incidence Yd p ≤ n := by
    intro p
    rw [incidence_eq_ncard, ncard_setOf]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨Z, hZYd, hZm, hZmass, -, hZlow⟩ :=
    trim_low_incidence hYdm hYdfin hLpos.le (Nat.cast_nonneg n) hinc_le
  -- balancing
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hZY : ∀ i, Z i ⊆ Y i := fun i => (hZYd i).trans (hYdY i)
  have hZball : ∀ i, Z i ⊆ ball 0 1 := fun i => ((hZY i).trans (hYT i)).trans (hball i)
  obtain ⟨l, S, hSm, hSmass, hSbal⟩ := balanced_refinement hρ0 hρ100 hβpos hZm hZball K hK Lb
  set Y' : Fin n → Set Space := fun i => Z i ∩ S with hY'
  -- the mass budget
  set B2 : ℝ := ((bigBound + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) with hB2
  set N0r : ℝ := ((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ) with hN0r
  have hB2pos : 0 < B2 := by positivity
  have hm1 : (δ ^ η - τ) * (n * δ ^ 2) ≤ ∑ i, (volume (Yb i)).toReal := by
    have h0 := hF.mass_lower hδ
    unfold shadingMass at h0
    linarith [hYbmass]
  have hωsum : ∑ j, ω j = ∑ i, (volume (Yb i)).toReal := by
    simp only [hω]
    exact Finset.sum_fiberwise Finset.univ fc (fun i => (volume (Yb i)).toReal)
  have hMwk : Mw * tcc * (N0r * k) = 384 * δ ^ (-η) * tcc * N0r * (n * δ ^ 2) := by
    rw [hMw, hFmax_def]; field_simp
  have hm2 : ((δ ^ η - τ) / B2 - 384 * δ ^ (-η) * tcc * N0r) * (n * δ ^ 2) ≤ shadingMass Yc := by
    rw [hYcmass]
    have h1 : (δ ^ η - τ) * (n * δ ^ 2) / B2 ≤ (∑ j, ω j) / B2 :=
      div_le_div_of_nonneg_right (hωsum ▸ hm1) hB2pos.le
    have h3 : (δ ^ η - τ) / B2 * (n * δ ^ 2) = (δ ^ η - τ) * (n * δ ^ 2) / B2 := by ring
    linarith [hQmass]
  have hQk : (Q.card : ℝ) ≤ k := by
    exact_mod_cast (Finset.card_le_univ Q).trans (Fintype.card_fin k).le
  have hFQ : Fmax * Q.card ≤ δ ^ (-η) * n := by
    rw [hFmax_def]
    calc δ ^ (-η) * ((n : ℝ) / k) * Q.card ≤ δ ^ (-η) * ((n : ℝ) / k) * k :=
          mul_le_mul_of_nonneg_left hQk (by positivity)
      _ = δ ^ (-η) * n := by field_simp
  have hm3 : (((δ ^ η - τ) / B2 - 384 * δ ^ (-η) * tcc * N0r) -
      172032 * (8 * ρ) ^ ηs * δ ^ (-η)) * (n * δ ^ 2) ≤ shadingMass Yd := by
    have h1 := mul_le_mul_of_nonneg_left hFQ
      (show 0 ≤ 172032 * (8 * ρ) ^ ηs * δ ^ 2 by positivity)
    linarith [hm2, hYdmass, h1]
  have hYdvol : (volume (⋃ i, Yd i)).toReal ≤ δ ^ (σ - η) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hYdU
  have hLvol : L * (volume (⋃ i, Yd i)).toReal ≤ δ ^ (ε1 - η) * (n * δ ^ 2) := by
    have h1 : L * (volume (⋃ i, Yd i)).toReal ≤ L * δ ^ (σ - η) :=
      mul_le_mul_of_nonneg_left hYdvol hLpos.le
    have h2 : L * δ ^ (σ - η) = δ ^ (ε1 - η) * (n * δ ^ 2) := by
      rw [hL]
      have : δ ^ (2 - σ + ε1) * δ ^ (σ - η) = δ ^ (ε1 - η) * δ ^ 2 := by
        rw [← Real.rpow_add hδ, ← Real.rpow_natCast δ 2, ← Real.rpow_add hδ]
        congr 1; push_cast; ring
      calc δ ^ (2 - σ + ε1) * n * δ ^ (σ - η) = (δ ^ (2 - σ + ε1) * δ ^ (σ - η)) * n := by ring
        _ = _ := by rw [this]; ring
    linarith
  have hm4 : ((((δ ^ η - τ) / B2 - 384 * δ ^ (-η) * tcc * N0r) -
      172032 * (8 * ρ) ^ ηs * δ ^ (-η)) - δ ^ (ε1 - η)) * (n * δ ^ 2) ≤ shadingMass Z := by
    linarith [hm3, hZmass, hLvol]
  set R : ℝ := (((((δ ^ η - τ) / B2 - 384 * δ ^ (-η) * tcc * N0r) -
      172032 * (8 * ρ) ^ ηs * δ ^ (-η) - δ ^ (ε1 - η)) - 1000 * β ^ (Lb + 1) / δ ^ 2) /
        (Lb + 1)) with hR
  have hbox := cubeBox_card_mul_le hρ0 (by linarith : ρ ≤ 1 / 5)
  have hm5 : R * n * δ ^ 2 ≤ shadingMass Y' := by
    have h2 : ((cubeBox K).card : ℝ) * (n * 8 * ρ ^ 3 * β ^ (Lb + 1)) ≤
        1000 * β ^ (Lb + 1) / δ ^ 2 * (n * δ ^ 2) := by
      have e1 : 1000 * β ^ (Lb + 1) / δ ^ 2 * (n * δ ^ 2) = 1000 * (n * β ^ (Lb + 1)) := by
        field_simp
      rw [e1]
      have hb0 : 0 ≤ (n : ℝ) * β ^ (Lb + 1) := by positivity
      calc ((cubeBox K).card : ℝ) * (n * 8 * ρ ^ 3 * β ^ (Lb + 1)) =
            (((cubeBox K).card : ℝ) * (8 * ρ ^ 3)) * (n * β ^ (Lb + 1)) := by ring
        _ ≤ 1000 * (n * β ^ (Lb + 1)) := mul_le_mul_of_nonneg_right hbox hb0
    have hLb : (0 : ℝ) < Lb + 1 := by positivity
    have h3 : (shadingMass Z - ((cubeBox K).card : ℝ) * (n * 8 * ρ ^ 3 * β ^ (Lb + 1))) /
        (Lb + 1) ≤ shadingMass Y' := hSmass
    refine le_trans ?_ h3
    rw [hR, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hLb.le
    nlinarith [hm4, h2]
  -- numerology for the packaging
  set μ : ℝ := (8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2) with hμ_def
  have hμpos : 0 < μ := by positivity
  have hRε : δ ^ ε ≤ R := (le_max_left _ _).trans hmass
  have hRc : 172032 * (8 * ρ) ^ ε * δ ^ (-η) ≤ R := (le_max_right _ _).trans hmass
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRε
  have hFk : Fmax ≤ δ ^ (-ε) * ((n : ℝ) / k) := by
    rw [hFmax_def]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith)
  have hθF_eq : θ * Fmax = (δ / (8 * ρ)) ^ (2 - σ - ε2) * ((n : ℝ) / k) := by
    rw [hθ, hFmax_def]
    have h1 : δ ^ η * δ ^ (-η) = 1 := by rw [← Real.rpow_add hδ]; simp
    calc (δ / (8 * ρ)) ^ (2 - σ - ε2) * δ ^ η * (δ ^ (-η) * ((n : ℝ) / k))
        = (δ / (8 * ρ)) ^ (2 - σ - ε2) * (δ ^ η * δ ^ (-η)) * ((n : ℝ) / k) := by ring
      _ = _ := by rw [h1, mul_one]
  have hθF : θ * Fmax ≤ (δ / (8 * ρ)) ^ (2 - σ - ε) * ((n : ℝ) / k) := by
    rw [hθF_eq]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_ge (by positivity) _ (by linarith)
    rw [div_le_one (by positivity)]; linarith
  have hθFpos : 0 < θ * Fmax := by positivity
  have hLμ : (k : ℝ) * μ * (θ * Fmax) ≤ L := by
    apply le_of_eq
    rw [hθF_eq, hμ_def, hL]
    have h1 : (8 * ρ) ^ (2 - σ - ε2) * (δ / (8 * ρ)) ^ (2 - σ - ε2) = δ ^ (2 - σ - ε2) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    have h2 : δ ^ (2 - σ - ε2) * δ ^ (ε1 + ε2) = δ ^ (2 - σ + ε1) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    calc (k : ℝ) * ((8 * ρ) ^ (2 - σ - ε2) * δ ^ (ε1 + ε2)) *
          ((δ / (8 * ρ)) ^ (2 - σ - ε2) * ((n : ℝ) / k))
        = ((8 * ρ) ^ (2 - σ - ε2) * (δ / (8 * ρ)) ^ (2 - σ - ε2)) * δ ^ (ε1 + ε2) * n *
            ((k : ℝ) / k) := by ring
      _ = δ ^ (2 - σ + ε1) * n := by rw [h1, div_self hk'.ne', mul_one, h2]
  have hLfine : δ ^ (2 - σ + ε) * n ≤ L := by
    rw [hL]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith)
  have hcvol' : 384 * (8 * ρ) ^ 2 / μ ≤ (8 * ρ) ^ (σ - ε) := by
    rw [hμ_def]
    convert hcvol using 2
    ring
  have hcmass : (8 * ρ) ^ ε * (8 * ρ) ^ 2 * k * (2688 * δ ^ 2 * Fmax) ≤ R * n * δ ^ 2 * ρ ^ 2 := by
    rw [hFmax_def]
    have h1 : (8 * ρ) ^ ε * (8 * ρ) ^ 2 * k * (2688 * δ ^ 2 * (δ ^ (-η) * ((n : ℝ) / k))) =
        172032 * (8 * ρ) ^ ε * δ ^ (-η) * (n * δ ^ 2 * ρ ^ 2) := by
      field_simp; ring
    rw [h1]
    have := mul_le_mul_of_nonneg_right hRc (show 0 ≤ (n : ℝ) * δ ^ 2 * ρ ^ 2 by positivity)
    linarith
  -- the final fine shadings
  have hY'Yb : ∀ i, Y' i ⊆ Yb i := fun i =>
    inter_subset_left.trans ((hZYd i).trans (inter_subset_left.trans (hYcYb i)))
  have hY'Y : ∀ i, Y' i ⊆ Y i := fun i => (hY'Yb i).trans (hYbY i)
  have hY'm : ∀ i, MeasurableSet (Y' i) := fun i => (hZm i).inter hSm
  have hY'Q : ∀ i, fc i ∉ Q → Y' i = ∅ := by
    intro i h
    apply Set.eq_empty_of_subset_empty
    calc Y' i ⊆ Z i := inter_subset_left
      _ ⊆ Yd i := hZYd i
      _ ⊆ Yc i := inter_subset_left
      _ = ∅ := hYcQ i h
  have hfib : ∀ j p, ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ θ * Fmax := by
    intro j p
    have hsub : {i | fc i = j ∧ p ∈ Y' i} ⊆ {i | fc i = j ∧ p ∈ Yb i} :=
      fun i ⟨h1, h2⟩ => ⟨h1, hY'Yb i h2⟩
    calc ({i | fc i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤ ({i | fc i = j ∧ p ∈ Yb i}.ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ θ * ({i | fc i = j}.ncard : ℝ) := hYbfib j p
      _ ≤ θ * Fmax := mul_le_mul_of_nonneg_left (hFmaxN j) hθpos.le
  have hcoarse : ∀ m, ((Q.filter (fun j =>
      m ∈ reachedF ρ K (lam • fibreUnion fc Y' j))).card : ℝ) ≤ θc * Q.card := by
    intro m
    by_cases hm : m ∈ highCubes ρ K fc Yc Q θc
    · -- no fibre of the final shadings reaches a deleted cube
      have : Q.filter (fun j => m ∈ reachedF ρ K (lam • fibreUnion fc Y' j)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _ hj
        obtain ⟨-, q, hqm, hq⟩ := Finset.mem_filter.mp hj
        obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.mp hq
        obtain ⟨i, -, hpi⟩ := mem_fibreUnion.mp hp
        have hpd : p ∈ Yd i := hZYd i hpi.1
        apply hpd.2
        refine ⟨lam • p, mem_iUnion₂.mpr ⟨m, hm, hqm⟩, ?_⟩
        simp only [smul_smul, inv_mul_cancel₀ hl0.ne', one_smul]
      rw [this, Finset.card_empty, Nat.cast_zero]
      positivity
    · have hle : (Q.filter (fun j => m ∈ reachedF ρ K (lam • fibreUnion fc Y' j))).card ≤
          cubeMult ρ K fc Yc Q m := by
        apply Finset.card_le_card
        intro j hj
        obtain ⟨hjQ, hjm⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨hjQ, ?_⟩
        refine reachedF_mono (Set.smul_set_mono ?_) hjm
        intro p hp
        obtain ⟨i, hij, hpi⟩ := mem_fibreUnion.mp hp
        exact mem_fibreUnion.mpr ⟨i, hij, (hZYd i hpi.1).1⟩
      have hmult : (cubeMult ρ K fc Yc Q m : ℝ) ≤ θc * Q.card := by
        by_contra hcon
        push Not at hcon
        apply hm
        refine Finset.mem_filter.mpr ⟨?_, hcon⟩
        have hpos : 0 < cubeMult ρ K fc Yc Q m := by
          have : (0 : ℝ) < cubeMult ρ K fc Yc Q m := lt_of_le_of_lt (by positivity) hcon
          exact_mod_cast this
        obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
        obtain ⟨hjQ, hjm⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_biUnion.mpr ⟨j, hjQ, hjm⟩
      calc _ ≤ (cubeMult ρ K fc Yc Q m : ℝ) := by exact_mod_cast hle
        _ ≤ θc * Q.card := hmult
  have hfine : ∀ p ∈ ⋃ i, Y' i, L < incidence Y' p := by
    intro p hp
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    have h1 : incidence Y' p = incidence Z p := by
      have := incidence_restrict Z S p
      rw [Set.indicator_of_mem hpi.2] at this
      exact this
    rw [h1]
    exact hZlow p (mem_iUnion.mpr ⟨i, hpi.1⟩)
  have hbal : ∃ θb : ℝ, 0 < θb ∧ ∀ m,
      (gridCube ρ m ∩ (1 - 2 * (16 * ρ)) • ⋃ i, Y' i).Nonempty →
        ENNReal.ofReal θb * volume (gridCube ρ m) ≤
          volume (((1 - 2 * (16 * ρ)) • ⋃ i, Y' i) ∩ gridCube ρ m) ∧
        volume (((1 - 2 * (16 * ρ)) • ⋃ i, Y' i) ∩ gridCube ρ m) ≤
          ENNReal.ofReal (δ ^ (-ε) * θb) * volume (gridCube ρ m) := by
    refine ⟨β ^ (l + 1), by positivity, fun m hm => ?_⟩
    have hβinv : β⁻¹ = δ ^ (-ε) := by rw [hβ, Real.rpow_neg hδ.le]
    rw [← hβinv]
    exact hSbal m hm
  have hηε' : δ ^ (-η) ≤ δ ^ (-ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1' (by linarith)
  have hbalε : ∀ j j', ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ) ≤
      δ ^ (-ε) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j') (w j')}.ncard : ℝ) := fun j j' =>
    (hbalρ j j').trans (mul_le_mul_of_nonneg_right hηε' (Nat.cast_nonneg _))
  have hfrostε : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ε) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) *
          volume W := fun j W hW =>
    (hfrostρ j W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hηε' (Nat.cast_nonneg _))) le_rfl)
  exact two_scale_package (θ := θ) (θc := θc) (μ := μ) (L := L) (R := R) (Fmax := Fmax)
    (K := K) hδ hδρ hρ hηsε hn hv hYT (fun i => (hYT i).trans (hball i)) hY'Y hY'm hk hw fc hfc
    hsepρ huniq hfull hbalε hfrostε hdilρ Q hY'Q hQball hQhalf
    hQsep hFmaxF hfib hcoarse hfine hbal hm5 hK hRpos hRε hFk hθF hθFpos hLμ hLfine hclow hμpos
    hcvol' le_rfl hcmass

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
