-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Window.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Rows

/-!
# One application of the slab lemma (sticky Lemma 5.4, one window)

In a window of `L` grid rows of side `s` (total height at most `√s`), away from the height `0`
and inside `[-1, 1]`, with enough fine mass, the slab lemma applies to the coarse set built at
representative heights in a plank piece of the kept shadings. Its output is an affine function
fitting the slope with error `4 s` on a set of rows of the window carrying a `s ^ ε / 4` share
of the mass of the window.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

/-- The arithmetic of the volume lower bound. -/
lemma volume_chain {s θ δ N NP NPb L n Mw KM PMr kc S2 SM : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hδ : 0 < δ) (hN : 0 < N) (hL : 0 < L) (hn : 0 < n)
    (hMw : 0 ≤ Mw) (hPM : 0 ≤ PMr) (hNP : NP ≤ NPb) (hNPb : 0 < NPb)
    (h1 : θ ^ 2 / (48 * δ ^ 2 * (L * s)) * S2 ≤ KM) (h2 : SM ^ 2 ≤ n * S2)
    (h3 : 3 * Mw / 4 ≤ SM) (h4 : KM ≤ NP * PMr)
    (h5 : 1 / (2 * s) * PMr ≤ kc * (N * (24 * δ ^ 2 / θ ^ 2))) :
    9 * s * θ ^ 4 * Mw ^ 2 / (16 * 2304 * N * δ ^ 4 * NPb * L * n) ≤ kc * s ^ 3 := by
  have hSM : 9 / 16 * Mw ^ 2 ≤ SM ^ 2 := by
    have : 0 ≤ 3 * Mw / 4 := by positivity
    nlinarith
  have hA : 9 / 16 * Mw ^ 2 / n ≤ S2 := by
    rw [div_le_iff₀ hn]; nlinarith
  have hB : θ ^ 2 / (48 * δ ^ 2 * (L * s)) * (9 / 16 * Mw ^ 2 / n) ≤ KM :=
    le_trans (mul_le_mul_of_nonneg_left hA (by positivity)) h1
  have hC : KM / NPb ≤ PMr := by
    rw [div_le_iff₀ hNPb]
    calc KM ≤ NP * PMr := h4
      _ ≤ NPb * PMr := mul_le_mul_of_nonneg_right hNP hPM
      _ = PMr * NPb := by ring
  have hD : PMr * θ ^ 2 / (48 * s * N * δ ^ 2) ≤ kc := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (2 * s) * PMr * (48 * s * N * δ ^ 2 / θ ^ 2) ≤
        kc * (N * (24 * δ ^ 2 / θ ^ 2)) * (48 * s * N * δ ^ 2 / θ ^ 2) :=
      mul_le_mul_of_nonneg_right h5 (by positivity)
    have e1 : 1 / (2 * s) * PMr * (48 * s * N * δ ^ 2 / θ ^ 2) = PMr * (24 * N * δ ^ 2 / θ ^ 2) := by
      field_simp; ring
    have e2 : kc * (N * (24 * δ ^ 2 / θ ^ 2)) * (48 * s * N * δ ^ 2 / θ ^ 2) =
        kc * (48 * s * N * δ ^ 2) * (N * (24 * δ ^ 2 / θ ^ 2) / θ ^ 2) := by
      field_simp
    have hpos : 0 < N * (24 * δ ^ 2 / θ ^ 2) / θ ^ 2 := by positivity
    have : PMr * (24 * N * δ ^ 2 / θ ^ 2) ≤
        kc * (48 * s * N * δ ^ 2) * (N * (24 * δ ^ 2 / θ ^ 2) / θ ^ 2) := by
      rw [← e1, ← e2]; exact this
    have e3 : PMr * (24 * N * δ ^ 2 / θ ^ 2) = PMr * θ ^ 2 * (N * (24 * δ ^ 2 / θ ^ 2) / θ ^ 2) := by
      field_simp
    rw [e3] at this
    exact le_of_mul_le_mul_right this hpos
  calc 9 * s * θ ^ 4 * Mw ^ 2 / (16 * 2304 * N * δ ^ 4 * NPb * L * n)
      = (θ ^ 2 / (48 * δ ^ 2 * (L * s)) * (9 / 16 * Mw ^ 2 / n)) / NPb * θ ^ 2 /
          (48 * s * N * δ ^ 2) * s ^ 3 := by
        field_simp
        ring
    _ ≤ KM / NPb * θ ^ 2 / (48 * s * N * δ ^ 2) * s ^ 3 := by gcongr
    _ ≤ PMr * θ ^ 2 / (48 * s * N * δ ^ 2) * s ^ 3 := by gcongr
    _ ≤ kc * s ^ 3 := by gcongr

section

variable {σ δ s θ K N : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
  {Eo : Set Space} {f : ℝ → ℝ} {P : Space → Space}

/-- The number of plank pieces. -/
noncomputable def pieceBound (σ δ s θ K H : ℝ) : ℝ :=
  10 * (K * (8 / Real.sqrt s) ^ (1 - σ)) *
    (2 * (Real.sqrt s + (4 * ((H + 2 * δ) / θ + 2 * δ) + H)) / Real.sqrt s + 2)

lemma pieceBound_pos {σ δ s θ K H : ℝ} (hs : 0 < s) (hK : 0 < K) (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hH : 0 ≤ H) : 0 < pieceBound σ δ s θ K H := by
  unfold pieceBound
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  positivity

/-- The window lemma. -/
theorem window_fit (hS : FineSetup σ δ s θ K N x v Y Eo f P)
    {εl ηl ρ₀ : ℝ} (hspec : SlabSpec σ εl ηl ρ₀) (hsρ : s ≤ ρ₀)
    (hs8 : 8 * s ≤ s ^ ((1 : ℝ) / 2 + εl))
    (hK : 162 * K ≤ s ^ (-ηl)) (hθη : s ^ ηl ≤ (θ - δ) / 2 - 8 * s)
    (hN : 0 < N) (hn : 0 < n)
    (m₀ : ℤ) (L : ℕ) (hL : 1 ≤ L) (hLs : (L : ℝ) * s ≤ Real.sqrt s)
    (hpos1 : -1 ≤ s * m₀) (hpos2 : s * m₀ + Real.sqrt s ≤ 1)
    (hfar : ∀ m ∈ Finset.Ico m₀ (m₀ + L), ∀ z ∈ row s m, 2 * Real.sqrt s ≤ |z|)
    (hvol : s ^ (1 + σ / 2 + ηl) ≤
      9 * s * θ ^ 4 * (heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L)))).toReal ^ 2 /
        (16 * 2304 * N * δ ^ 4 * pieceBound σ δ s θ K (L * s) * L * n)) :
    ∃ (a b : ℝ) (G : Finset ℤ), G ⊆ Finset.Ico m₀ (m₀ + L) ∧
      (∀ m ∈ G, ∀ z ∈ row s m, |f z - (a + b * z)| ≤ 4 * s) ∧
      ENNReal.ofReal (s ^ εl *
          (heightMass Y (rowUnion s (Finset.Ico m₀ (m₀ + L)))).toReal / 4) ≤
        heightMass Y (rowUnion s G) := by
  classical
  have hs := s_pos hS
  have hb := sqrt_s_bounds hS
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hδ := hS.δ_pos
  have hθ := hS.θ_pos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hS.K_one
  have hYb : ∀ i, Y i ⊆ ball (0 : Space) 1 := fun i => (hS.sub_Eo i).trans hS.Eo_ball
  set W := Finset.Ico m₀ (m₀ + L) with hW
  set z₀ := s * m₀ with hz₀
  set Mw := (heightMass Y (rowUnion s W)).toReal with hMw
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hWcard : (W.card : ℝ) = L := by simp [hW]
  -- rows of the window lie in `[z₀, z₀ + L s)`
  have hrowW : ∀ m ∈ W, ∀ z ∈ row s m, z₀ ≤ z ∧ z < z₀ + L * s := by
    intro m hm z hz
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    have h1 : (m₀ : ℝ) ≤ m := by exact_mod_cast hm1
    have h2 : (m : ℝ) + 1 ≤ m₀ + L := by
      have : m + 1 ≤ m₀ + L := hm2
      exact_mod_cast this
    obtain ⟨hz1, hz2⟩ := hz
    constructor <;> nlinarith
  have hrowI : ∀ m ∈ W, ∀ z ∈ row s m, z ∈ Icc (-1 : ℝ) 1 := by
    intro m hm z hz
    obtain ⟨h1, h2⟩ := hrowW m hm z hz
    constructor <;> linarith
  have hz₀I : z₀ ∈ Icc (-1 : ℝ) 1 := ⟨hpos1, by linarith⟩
  -- Mw is positive
  have hMw0 : 0 < Mw := by
    have hl : 0 < s ^ (1 + σ / 2 + ηl) := Real.rpow_pos_of_pos hs _
    by_contra h
    push Not at h
    have hMw' : Mw = 0 := le_antisymm h ENNReal.toReal_nonneg
    rw [hMw', sq, zero_mul, mul_zero, zero_div] at hvol
    linarith
  -- Step 1: heavy rows
  set R := W.filter fun m => Mw / (4 * L) ≤ (heightMass Y (row s m)).toReal with hR
  have hheavy : 3 * Mw / 4 ≤ (heightMass Y (rowUnion s R)).toReal :=
    heavy_rows hS.meas hYb hs W (le_of_eq hWcard) (by omega)
  have hRW : R ⊆ W := Finset.filter_subset _ _
  set ZR := rowUnion s R with hZR
  have hZRm : MeasurableSet ZR :=
    Finset.measurableSet_biUnion _ fun m _ => measurableSet_row s m
  have hZRsub : ∀ z ∈ ZR, z₀ ≤ z ∧ z < z₀ + L * s := by
    intro z hz
    obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hz
    exact hrowW m (hRW hm) z hzm
  have hZRvol : volume ZR ≤ ENNReal.ofReal (L * s) := by
    calc volume ZR ≤ volume (Ico z₀ (z₀ + L * s)) :=
          measure_mono fun z hz => ⟨(hZRsub z hz).1, (hZRsub z hz).2⟩
      _ = ENNReal.ofReal (L * s) := by rw [Real.volume_Ico]; congr 1; ring
  -- `R` is nonempty
  have hRne : R.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : heightMass Y (rowUnion s R) = 0 := by
      rw [heightMass_rowUnion hS.meas hs, h, Finset.sum_empty]
    rw [this, ENNReal.toReal_zero] at hheavy
    linarith
  obtain ⟨m₁, hm₁⟩ := hRne
  have hz₁ : s * m₁ ∈ ZR := mem_iUnion₂.mpr ⟨m₁, hm₁, le_rfl, by nlinarith⟩
  -- Step 2: the kept height
  obtain ⟨zs, hzsZ, hkept⟩ := exists_kept_height hS hZRm (by positivity) hZRvol hz₁
  have hzsW := hZRsub zs hzsZ
  have hzsI : zs ∈ Icc (-1 : ℝ) 1 := by
    obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp hzsZ
    exact hrowI m (hRW hm) zs hzm
  set Sk := keptAt Y zs with hSk
  -- Step 3: the plank piece
  have hZRp : ∀ z ∈ ZR, |z - zs| ≤ L * s ∧ z₀ ≤ z ∧ z ≤ z₀ + Real.sqrt s := by
    intro z hz
    obtain ⟨h1, h2⟩ := hZRsub z hz
    refine ⟨abs_le.mpr ⟨by linarith [hzsW.1, hzsW.2], by linarith [hzsW.1, hzsW.2]⟩, h1,
      by linarith⟩
  have hzz : |z₀ - zs| ≤ L * s := abs_le.mpr ⟨by linarith [hzsW.2], by linarith [hzsW.1]⟩
  obtain ⟨c, y₀, NP, hNP, hpiece⟩ := exists_plank_piece hS hz₀I hzsI (by positivity) hzz hZRp
  set PR := plankRegion f z₀ c y₀ s with hPR
  have hPRm : MeasurableSet PR := measurableSet_plankRegion f z₀ c y₀ s
  -- Step 4: representative heights
  have hrep := fun m => exists_rep_height hS Sk hPRm m
  choose zrep hzrep_mem hzrep using hrep
  set Kb : ℕ := ⌈2 / s + 1⌉₊ with hKb
  have hKb' : 2 / s + 1 ≤ Kb := Nat.le_ceil _
  set Kc := cubeSet s Kb Y Sk PR R zrep with hKc
  set pc := plankCentre f z₀ c y₀ s with hpc
  have hC : CoarseConfig s Y f R zrep Kc PR z₀ c pc := by
    refine ⟨fun m _ => hzrep_mem m, ?_, ?_, ?_, ?_, ?_, hz₀I⟩
    · intro m hm z hz
      exact ⟨hfar m (hRW hm) z hz, hrowI m (hRW hm) z hz⟩
    · intro k hk
      obtain ⟨m, hm, hk'⟩ := Finset.mem_biUnion.mp hk
      rw [reached_row hs (hzrep_mem m) hk']
      exact hm
    · intro k hk
      obtain ⟨m, hm, hk'⟩ := Finset.mem_biUnion.mp hk
      have hk2 := reached_row hs (hzrep_mem m) hk'
      unfold Coarse.reachedF at hk'
      obtain ⟨-, q, hqk, hqF, hq2⟩ := Finset.mem_filter.mp hk'
      obtain ⟨i, hi, hqY, hqPR⟩ := mem_iUnion₂.mp hqF
      exact ⟨i, q, hqY, hqPR, by rw [hk2]; exact hq2, hqk⟩
    · intro q hq
      exact hq.1
    · intro q hq
      exact dist_plankCentre_le (hS.f_bound z₀ hz₀I) hs.le hb.2 hq
  -- Step 5: the volume of the coarse set
  set E := cubeUnion s Kc with hE
  have hEvol : ENNReal.ofReal (s ^ (1 + σ / 2 + ηl)) ≤ volume E := by
    have hmassc := mass_le_card_cubeSet hS Sk hPRm
      (R := R) (zrep := zrep) (fun m _ => ⟨hzrep_mem m, hzrep m⟩) hKb'
    rw [hE, volume_cubeUnion hs Kc]
    -- conversion to reals
    set mr : Fin n → ℝ := fun i => (volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR)).toReal
    have hmt : ∀ i, volume (Y i ∩ (fun p : Space => p 2) ⁻¹' ZR) ≠ ∞ := fun i =>
      ne_of_lt ((measure_mono (inter_subset_left.trans (hYb i))).trans_lt measure_ball_lt_top)
    have hmtPR : ∀ i, volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' ZR) ≠ ∞ := fun i =>
      ne_of_lt ((measure_mono (inter_subset_left.trans (inter_subset_left.trans (hYb i)))).trans_lt
        measure_ball_lt_top)
    set KM := ∑ i ∈ Sk, mr i
    set PMr := (∑ i ∈ Sk, volume (Y i ∩ PR ∩ (fun p : Space => p 2) ⁻¹' ZR)).toReal
    set S2 := ∑ i, mr i ^ 2
    set SM := ∑ i, mr i
    have h1 : θ ^ 2 / (48 * δ ^ 2 * (L * s)) * S2 ≤ KM := by
      have := ENNReal.toReal_mono (by
        apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro i _
        exact lt_top_iff_ne_top.mpr (hmt i)) hkept
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_sum (fun i _ => ENNReal.pow_ne_top (hmt i)),
        ENNReal.toReal_sum (fun i _ => hmt i)] at this
      simpa [mr, S2, KM, ENNReal.toReal_pow] using this
    have h2 : SM ^ 2 ≤ n * S2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := mr)
      simpa [SM, S2] using this
    have h3 : 3 * Mw / 4 ≤ SM := by
      have e : (heightMass Y (rowUnion s R)).toReal = SM := by
        simp only [heightMass, SM, mr, hZR]
        rw [ENNReal.toReal_sum (fun i _ => hmt i)]
      rw [← e]; exact hheavy
    have h4 : KM ≤ NP * PMr := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top NP)
        (by apply ne_of_lt; apply ENNReal.sum_lt_top.mpr; intro i _
            exact lt_top_iff_ne_top.mpr (hmtPR i))) hpiece
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_sum (fun i _ => hmt i)] at this
      simpa [KM, mr, PMr] using this
    have h5 : 1 / (2 * s) * PMr ≤ (Kc.card : ℝ) * (N * (24 * δ ^ 2 / θ ^ 2)) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top) hmassc
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at this
      simpa [PMr, hZR] using this
    have hPMr : 0 ≤ PMr := ENNReal.toReal_nonneg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hchain := volume_chain hs hθ hδ hN hLpos hnpos hMw0.le hPMr hNP
      (pieceBound_pos hs hK0 hθ hδ.le (by positivity)) h1 h2 h3 h4 h5
    have hfin : ENNReal.ofReal (s ^ (1 + σ / 2 + ηl)) ≤ ENNReal.ofReal ((Kc.card : ℝ) * s ^ 3) :=
      ENNReal.ofReal_le_ofReal (hvol.trans (by simpa [pieceBound] using hchain))
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow hs.le] at hfin
    exact hfin
  -- Step 6: apply the slab lemma
  have hVhyp := hyp_V hS hC hθη
  have hfz4 : ∀ z ∈ Icc z₀ (z₀ + Real.sqrt s), |f z| ≤ 4 := by
    intro z hz
    have := hS.f_bound z ⟨by linarith [hz.1], by linarith [hz.2]⟩
    linarith
  have hflip : ∀ z ∈ Icc z₀ (z₀ + Real.sqrt s), ∀ z' ∈ Icc z₀ (z₀ + Real.sqrt s),
      |f z - f z'| ≤ |z - z'| := by
    intro z _ z' _
    have := hS.f_lip.dist_le_mul z z'
    simpa [Real.dist_eq] using this
  have hZRI : ZR ⊆ Icc z₀ (z₀ + Real.sqrt s) := fun z hz =>
    ⟨(hZRsub z hz).1, by linarith [(hZRsub z hz).2]⟩
  obtain ⟨Zl, hZl, hZlvol, a, b, hfit⟩ := hspec s hs hsρ z₀ c ZR f Kc (unitField P pc s)
    hpos1 hpos2 hZRI hflip hfz4
    (hyp_box hS hC)
    hEvol
    hVhyp.1
    hVhyp.2
    (fun z hz => ((hyp_slice hS hC) z hz).mono_constant hs (by linarith))
    (fun p hp => (hyp_local hS hC p hp).trans (ENNReal.ofReal_le_ofReal (by
      rw [show (1 + σ) / 2 - ηl = (1 + σ) / 2 + (-ηl) by ring,
        Real.rpow_add hs]
      have hpow : 0 ≤ s ^ ((1 + σ) / 2) := Real.rpow_nonneg hs.le _
      nlinarith)))
  -- Step 7: the output
  have hT : 0 < s ^ ((1 : ℝ) / 2 + εl) := Real.rpow_pos_of_pos hs _
  have hbound := slope_le_two hS.f_lip hT hs.le hs8 hZlvol hfit
  set G := R.filter fun m => (Zl ∩ row s m).Nonempty with hG
  refine ⟨a, b, G, (Finset.filter_subset _ _).trans hRW, ?_, ?_⟩
  · intro m hm z hz
    obtain ⟨z₁, hz₁Zl, hz₁m⟩ := (Finset.mem_filter.mp hm).2
    exact rows_fit hS.f_lip hbound hz₁m (hfit z₁ hz₁Zl) z hz
  · -- the mass of the good rows
    have hZlG : Zl ⊆ rowUnion s G := by
      intro z hz
      obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp (hZl hz)
      exact mem_iUnion₂.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, z, hz, hzm⟩, hzm⟩
    have hcard : ENNReal.ofReal (s ^ ((1 : ℝ) / 2 + εl)) ≤ (G.card : ℝ≥0∞) * ENNReal.ofReal s := by
      calc ENNReal.ofReal (s ^ ((1 : ℝ) / 2 + εl)) ≤ volume Zl := hZlvol
        _ ≤ volume (rowUnion s G) := measure_mono hZlG
        _ ≤ ∑ m ∈ G, volume (row s m) := measure_biUnion_finset_le _ _
        _ = (G.card : ℝ≥0∞) * ENNReal.ofReal s := by
            simp only [volume_row hs, Finset.sum_const, nsmul_eq_mul]
    have hcard' : s ^ ((1 : ℝ) / 2 + εl) ≤ G.card * s := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        ENNReal.ofReal_ne_top) hcard
      rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg hs.le _), ENNReal.toReal_mul,
        ENNReal.toReal_natCast, ENNReal.toReal_ofReal hs.le] at this
    have hrows : ∀ m ∈ G, ENNReal.ofReal (Mw / (4 * L)) ≤ heightMass Y (row s m) := by
      intro m hm
      have hmR := (Finset.mem_filter.mp hm).1
      have h := (Finset.mem_filter.mp hmR).2
      rw [← ENNReal.ofReal_toReal (heightMass_ne_top hYb (row s m))]
      exact ENNReal.ofReal_le_ofReal h
    rw [heightMass_rowUnion hS.meas hs]
    calc ENNReal.ofReal (s ^ εl * Mw / 4)
        ≤ ENNReal.ofReal (G.card * (Mw / (4 * L))) := by
          apply ENNReal.ofReal_le_ofReal
          -- `s ^ εl * Mw / 4 ≤ #G * Mw / (4 L)` since `L s ^ εl ≤ #G`
          have hsq : Real.sqrt s = s ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow s
          have hA : Real.sqrt s * s ^ εl ≤ G.card * s := by
            rw [hsq, ← Real.rpow_add hs]; exact hcard'
          have hB : L * s * s ^ εl ≤ Real.sqrt s * s ^ εl :=
            mul_le_mul_of_nonneg_right hLs (Real.rpow_nonneg hs.le _)
          have hC : (L * s ^ εl) * s ≤ G.card * s := by nlinarith
          have hD : L * s ^ εl ≤ G.card := le_of_mul_le_mul_right hC hs
          calc s ^ εl * Mw / 4 = (L * s ^ εl) * (Mw / (4 * L)) := by
                field_simp
            _ ≤ G.card * (Mw / (4 * L)) :=
                mul_le_mul_of_nonneg_right hD (by positivity)
      _ = ∑ _m ∈ G, ENNReal.ofReal (Mw / (4 * L)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ∑ m ∈ G, heightMass Y (row s m) := Finset.sum_le_sum hrows

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
