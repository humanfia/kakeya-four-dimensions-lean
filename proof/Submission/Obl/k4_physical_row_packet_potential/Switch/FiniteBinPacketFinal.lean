-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/FiniteBinPacketFinal.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- The switching arithmetic below is adapted from this LOT tree, o287,
session x1037, commit e68660a1, Switch/PacketFinal.lean. This version
retains actual velocities and consumes singleton caps of the original
velocity-code law, with an arbitrary finer admissible velocity mesh. -/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketFinal

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_physical_row_packet_potential.Switch
open Set MeasureTheory
open Submission.Obl.k4_physical_row_packet_potential.PotentialFits
open scoped ENNReal
noncomputable section

/-- Singleton caps on a countable code law imply caps on every union of codes. -/
theorem countable_code_palette_cap {Ω V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) (code : Ω → V) (hcode : Measurable code) (π : Measure V)
    (C : ℝ≥0∞) (hcap : ∀ b, μ (code ⁻¹' {b}) ≤ C * π {b})
    (B : Set V) : μ (code ⁻¹' B) ≤ C * π B := by
  calc
    μ (code ⁻¹' B) = ∑' b : B, μ (code ⁻¹' {(b : V)}) :=
      (tsum_measure_preimage_singleton (to_countable B)
        (fun b _ => hcode (measurableSet_singleton b))).symm
    _ ≤ ∑' b : B, C * π {(b : V)} := ENNReal.tsum_le_tsum (fun b => hcap b)
    _ = C * ∑' b : B, π {(b : V)} := ENNReal.tsum_mul_left
    _ = C * π B := by
      congr 1
      simpa only [preimage_id] using
        (tsum_measure_preimage_singleton (μ := π) (f := id) (to_countable B)
          (fun b _ => measurableSet_singleton b))

namespace PacketSwitching

set_option maxHeartbeats 2000000 in
/-- The frozen packet from singleton velocity-bin domination. The velocity mesh
may be any positive width below the explicit switching bound. -/
theorem frozen_packet_final_of_velocity_bins (D : ℕ) : ∃ cNorm cCurl : ℕ,
    ∀ (q : ℕ) (precision loss Nk L d₁ gain κ : ℝ) (ν : Measure Ln) [IsProbabilityMeasure ν]
      (B r : ℝ) (T j : ℕ) (c u : P2) (P : Po) (hP : P.totalDegree ≤ 2)
      (A : Set Ln) (hA : MeasurableSet A) (F H : Set Ev)
      (K ε : ℝ) (S : Set Ev)
      (hε : 0 < ε) (hεζ : ε ≤ δ Nk (precision * gain * L))
      (hεa : ε ≤ (δ Nk r / ((2:ℝ)^T)⁻¹) * δ Nk (precision * gain * L))
      (ha : 0 < δ Nk r) (haK : δ Nk r ≤ K * ((2:ℝ)^T)⁻¹)
      (hhζ : ((2:ℝ)^T)⁻¹ ≤ δ Nk (precision * gain * L))
      (hK2 : 2 ≤ K) (hκK : κ ≤ K) (hKN : K ≤ Nk ^ (loss * gain * L))
      (hS : MeasurableSet S) (hSHF : S ⊆ H ∩ F) (hSA : S ⊆ A ×ˢ univ)
      (hSunit : S ⊆ univ ×ˢ Icc (0 : ℝ) 1)
      (htime : ∀ z ∈ S, z.2 ∈ Icc (start T j) (start T j + clock T))
      (href : 0 < ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A)
      (hmass : ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A / ENNReal.ofReal K ≤
        ((ν.prod volume).restrict S) univ)
      (hpts : ∀ p ∈ S, ‖packetBase T j c u p‖ ≤ K ∧ ‖v p.1‖ ≤ K ∧
        (∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (xp p.1 t) P| ≤ K ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 P)| ≤ K * B ∧
          |MvPolynomial.eval (xp p.1 t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 P))| ≤
            K * B ^ 2) ∧
        B / K ≤ |MvPolynomial.eval (xp p.1 p.2) (MvPolynomial.pderiv 3 P)|)
      (hstrip : ∀ k : (Fin 3 → ℤ) × ℤ, ∀ n : P2, ∀ t : ℝ, ‖n‖ = 1 →
        ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k ∧
              |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S)
            {p | physicalCode (packetBase T j c u) (fun p => packetSignal P p / δ Nk r) ε p = k})
      (hceil : ∀ U : Set P3, MeasurableSet U →
        ((ν.prod volume).restrict S) {p | packetBase T j c u p ∈ U} ≤
          ENNReal.ofReal K * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hband : ∀ (w : ℝ), ε ≤ w → w ≤ 1 → ∀ (U : Set P3), MeasurableSet U →
        ∀ f : P3 → ℝ, Measurable f →
        ((ν.prod volume).restrict S)
            {p | packetBase T j c u p ∈ U ∧ |packetSignal P p / δ Nk r - f (packetBase T j c u p)| ≤ w} ≤
          ENNReal.ofReal (K * w ^ d₁) * (ENNReal.ofReal ((2:ℝ)^T)⁻¹ * ν A) * volume U)
      (hcount : ∀ p w : ℝ, ε ≤ p → p ≤ 1 → ε ≤ w → w ≤ 1 →
        K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * p ≤ δ Nk r * w →
        Set.Finite {k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k} ∧
        (({k : (Fin 3 → ℤ) × ℤ | ∃ e ∈ S,
          (fun e => (fun i : Fin 3 => ⌊packetBase T j c u e i / p⌋,
            ⌊packetSignal P e / δ Nk r / w⌋)) e = k}).ncard : ℝ) ≤ K / (p ^ (3 : ℕ) * w ^ d₁))
      {σ : Type*} [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
      [StandardBorelSpace σ] (st : Ev → σ) (hstm : Measurable st)
      (hrefine : ∀ z z', st z = st z' →
        packetState T j c u P (δ Nk r) ε z = packetState T j c u P (δ Nk r) ε z')
      (hstripSt : ∀ k (n : P2) (t : ℝ), ‖n‖ = 1 →
        ((ν.prod volume).restrict S) {p | st p = k ∧ |inner ℝ n (v p.1) - t| ≤ K ^ (-100 : ℝ)} ≤
          (1 / 1000000000000 : ENNReal) * ((ν.prod volume).restrict S) {p | st p = k})
      (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] (Kr : ℝ) (hKr : 1 ≤ Kr)
      (Tf : Fin 3 → MvPolynomial (Fin 3) ℝ) (hT : ∀ i, (Tf i).totalDegree ≤ D) (hDq : D + 1 ≤ q)
      (AT : ℝ) (hAT : 0 ≤ AT) (hcoeffT : ∀ i m, |(Tf i).coeff m| ≤ AT)
      (hcoeffBudget : ((D + 1 : ℕ) : ℝ) * 3 * AT ≤ K)
      (pv : ℝ) (hpv : 0 < pv)
      (hpvBound : pv ≤ binWidth D cNorm cCurl K Kr (δ Nk r) (clock T)
        (δ Nk (precision * gain * L)) d₁ AT)
      (hbin : ∀ k β,
        (ν.prod volume) ({z | st z = k ∧ velBin pv z.1 = β} ∩ S) ≤
          ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S) * π {β})
      (times : Ln → Set ℝ) (η err : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (herr0 : 0 ≤ err)
      (htimes : ∀ z ∈ S, times z.1 ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (times z.1))
      (hfitL : ∀ z ∈ S, ∀ s ∈ times z.1,
        |ParentSignal.rate P z.1 (start T j + clock T * s) - ∑ i : Fin 3,
          direction z.1 i * MvPolynomial.eval
            (fun i => packetBase T j c u (z.1, start T j + clock T * s) i) (Tf i)| ≤ err)
      (hd₁ : d₁ < 1)
      (hεsmall : ε ≤ packetEpsBound D cNorm cCurl K Kr (δ Nk r) (clock T)
        (δ Nk (precision * gain * L)) d₁ AT)
      (herrsmall : err ≤ packetErrBound D cNorm cCurl K Kr (δ Nk r) (clock T)
        (δ Nk (precision * gain * L)) d₁ η),
      PhysicalPotentialPacket q precision loss Nk L d₁ gain κ ν B r T j c u P A F H := by
  obtain ⟨cNorm, cCurl, hfp⟩ := frozen_packet D
  refine ⟨cNorm, cCurl, ?_⟩
  intro q precision loss Nk L d₁ gain κ ν _ B r T j c u P hP A hA F H K ε S hε hεζ hεa ha haK hhζ
    hK2 hκK hKN hS hSHF hSA hSunit htime href hmass hpts hstrip hceil hband hcount σ _ _ _ _ st hstm
    hrefine hstripSt π _ Kr hKr Tf hT hDq AT hAT hcoeffT hcoeffBudget pv hpv hpvBound hbin times η err hη hη1 herr0 htimes hfitL hd₁
    hεsmall herrsmall
  -- scales
  set a := δ Nk r with ha_def
  set h := clock T with hh_def
  set ζ := δ Nk (precision * gain * L) with hζ_def
  have hh0 : 0 < h := clock_pos T
  have hh2 : h = ((2:ℝ)^T)⁻¹ := rfl
  have hζ0 : 0 < ζ := hh0.trans_le (by rw [hh2]; exact hhζ)
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hah : 0 < a / h := div_pos ha hh0
  -- the pencil radius
  set rp := pencilRadius K with hrp_def
  have hKpow : 0 < K ^ (-100 : ℝ) := Real.rpow_pos_of_pos hK0 _
  have hKpow1 : K ^ (-100 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by norm_num)
  have hrp : 0 < rp := by simp only [rp, pencilRadius]; positivity
  have hrp1 : rp ≤ 1 := by
    simp only [rp, pencilRadius]
    rw [div_le_one (by positivity)]
    linarith
  -- the census meshes
  have hG : 0 ≤ curlWeight D (2 * K) K := by unfold curlWeight; positivity
  set C' := censusConstant D cNorm cCurl K Kr (2 * K) K 1 with hC'_def
  have hC' : 0 < C' := by
    simp only [C', censusConstant]
    have : 0 < max 1 (K + 1) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity
  set wc := censusHeight D cNorm cCurl K Kr ζ d₁ with hwc_def
  have hX0 : 0 < ζ * rp ^ 9 / C' := by positivity
  have hwc : 0 < wc := by
    simp only [wc, censusHeight]
    exact lt_min zero_lt_one (Real.rpow_pos_of_pos hX0 _)
  have hwc1 : wc ≤ 1 := min_le_left _ _
  have hd : 0 < 1 - d₁ := by linarith
  have hwcpow : wc ^ (1 - d₁) ≤ ζ * rp ^ 9 / C' := by
    have h1 : wc ≤ (ζ * rp ^ 9 / C') ^ (1 / (1 - d₁)) := min_le_right _ _
    calc wc ^ (1 - d₁) ≤ ((ζ * rp ^ 9 / C') ^ (1 / (1 - d₁))) ^ (1 - d₁) :=
          Real.rpow_le_rpow hwc.le h1 hd.le
      _ = ζ * rp ^ 9 / C' := by
          rw [one_div, Real.rpow_inv_rpow hX0.le hd.ne']
  set pc := censusBase D cNorm cCurl K Kr a h ζ d₁ with hpc_def
  have hpc : 0 < pc := by simp only [pc, censusBase]; positivity
  have hpc_eq : pc = a * wc / (K ^ (100 : ℕ) * h) := rfl
  have hpw : K ^ (100 : ℕ) * ((2:ℝ)^T)⁻¹ * pc ≤ a * wc := by
    rw [← hh2, hpc_eq]
    apply le_of_eq
    field_simp
  have hpc1 : pc ≤ 1 := by
    rw [hpc_eq, div_le_one (by positivity)]
    have hK100 : K ≤ K ^ (100 : ℕ) := by
      calc K = K ^ (1 : ℕ) := (pow_one K).symm
        _ ≤ K ^ (100 : ℕ) := pow_le_pow_right₀ hK1 (by norm_num)
    have h1 : a * wc ≤ K * h * 1 := by
      have := mul_le_mul haK hwc1 hwc.le (by positivity)
      rw [← hh2] at this
      linarith
    nlinarith [hK100, hh0]
  -- the bin width
  set Bst := fieldBound D K AT with hB_def
  set Ast := fieldLip D K AT with hA_def
  have hB0 : 0 ≤ Bst := by simp only [Bst, fieldBound]; positivity
  have hA0 : 0 ≤ Ast := by simp only [Ast, fieldLip]; positivity
  have hpv_le_rp : pv ≤ rp := hpvBound.trans (min_le_left _ _)
  have hpv_le_pc : pv ≤ pc / 48 :=
    hpvBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpv_le_B : pv ≤ a / h * wc / (90 * (Bst + 1)) :=
    hpvBound.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hpv_le_A : pv ≤ a / h * wc / (1260 * (K + 1) * (Ast + 1)) :=
    hpvBound.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hpv1 : pv ≤ 1 := hpv_le_rp.trans hrp1
  -- the packet mesh
  have hε1 : ε ≤ 1 := hεsmall.trans (min_le_left _ _)
  have hε_pc : ε ≤ pc / (24 * (1 + K)) := hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε_K : ε ≤ a / h * wc / (2400 * K) :=
    hεsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε_A : ε ≤ a / h * wc / (2520 * (K + 1) * (Ast + 1) * (1 + K)) :=
    hεsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hε_wc : ε ≤ wc / 60 :=
    hεsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hpc0 : ε ≤ pc := hε_pc.trans (div_le_self hpc.le (by linarith))
  have hwc0 : ε ≤ wc := hε_wc.trans (by linarith)
  -- the fit error
  have hR8 : 0 < (8 * ((D : ℝ) + 2) / η) ^ (D + 1) := by positivity
  have herr1 : err ≤ a * ζ / (2 * h * (8 * ((D : ℝ) + 2) / η) ^ (D + 1)) :=
    herrsmall.trans (min_le_left _ _)
  have herr2 : err ≤ a / h * wc /
      (60 * (384 * K * ((D : ℝ) + 2)) ^ (D + 1) * (8 * ((D : ℝ) + 2) / η) ^ (D + 1)) :=
    herrsmall.trans (min_le_right _ _)
  -- the lines of `S`
  set Lines := Prod.fst '' S with hLines_def
  have hLines : ∀ z ∈ S, z.1 ∈ Lines := fun z hz => ⟨z, hz, rfl⟩
  have hdir : ∀ z ∈ S, ∀ i, |direction z.1 i| ≤ K := by
    intro z hz i
    have hv := (hpts z hz).2.1
    fin_cases i
    · simp [direction]; exact hK1
    · have := (PiLp.norm_apply_le (v z.1) 0).trans hv
      simpa [direction, v_apply_zero] using this
    · have := (PiLp.norm_apply_le (v z.1) 1).trans hv
      simpa [direction, v_apply_one] using this
  have hbaseL : ∀ l ∈ Lines, ∀ t ∈ Icc (start T j) (start T j + clock T), ∀ i,
      |packetBase T j c u (l, t) i| ≤ 2 * K := by
    rintro l ⟨z, hz, rfl⟩ t ht i
    have hzt := htime z hz
    have hshift := startBase_shift T j c u z
    have hnorm := packetBase_normalized T j c u z.1 ((t - start T j) / clock T)
    have ht' : start T j + clock T * ((t - start T j) / clock T) = t := by
      have hc := (clock_pos T).ne'
      field_simp
      ring
    rw [ht'] at hnorm
    have heq : packetBase T j c u (z.1, t) i =
        packetBase T j c u z i + ((t - z.2) / clock T) * direction z.1 i := by
      have h1 := congrFun hnorm i
      have h2 := congrFun hshift i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
      rw [h1, ← h2]
      have hc := (clock_pos T).ne'
      simp only [startBase]
      field_simp
      ring
    rw [heq]
    have hbz : |packetBase T j c u z i| ≤ K :=
      (PiLp.norm_apply_le _ i).trans (hpts z hz).1
    have hts : |(t - z.2) / clock T| ≤ 1 := by
      rw [abs_div, abs_of_pos hh0, div_le_one hh0, abs_le]
      constructor <;> linarith [ht.1, ht.2, hzt.1, hzt.2]
    calc
      _ ≤ |packetBase T j c u z i| + |(t - z.2) / clock T * direction z.1 i| := abs_add_le _ _
      _ = |packetBase T j c u z i| + |(t - z.2) / clock T| * |direction z.1 i| := by
        rw [abs_mul]
      _ ≤ K + 1 * K := by gcongr; exact hdir z hz i
      _ = 2 * K := by ring
  have hvelL : ∀ l ∈ Lines, ∀ i, |direction l i| ≤ K := by
    rintro l ⟨z, hz, rfl⟩ i
    exact hdir z hz i
  -- A countable code law needs only singleton caps.
  have hrect : ∀ k (Aw : Set (Fin 2 → ℤ)), MeasurableSet Aw →
      (ν.prod volume) ({z | st z = k ∧ velBin pv z.1 ∈ Aw} ∩ S) ≤
        ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S) * π Aw := by
    intro k Aw _hAw
    have hstS : MeasurableSet (st ⁻¹' {k} ∩ S) :=
      (hstm (measurableSet_singleton k)).inter hS
    have hvel : Measurable (fun z : Ev => velBin pv z.1) := by
      exact (measurable_binOf pv).comp (by unfold v; fun_prop)
    have hsingle (β : Fin 2 → ℤ) :
        ((ν.prod volume).restrict (st ⁻¹' {k} ∩ S))
            ((fun z : Ev => velBin pv z.1) ⁻¹' {β}) ≤
          (ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S)) * π {β} := by
      rw [Measure.restrict_apply' hstS]
      convert hbin k β using 2
      ext z
      simp [and_assoc,and_left_comm]
    have hh := countable_code_palette_cap
      ((ν.prod volume).restrict (st ⁻¹' {k} ∩ S))
      (fun z : Ev => velBin pv z.1) hvel π
      (ENNReal.ofReal Kr * (ν.prod volume) (st ⁻¹' {k} ∩ S)) hsingle Aw
    rw [Measure.restrict_apply' hstS] at hh
    convert hh using 2
    ext z
    simp [and_assoc,and_left_comm]
  -- the width conditions
  have hRf : K + K + 7 * (ε + ε * K + pv / 2) ≤ fieldRadius K := by
    unfold fieldRadius
    have h1 : ε * K ≤ 1 * K := mul_le_mul_of_nonneg_right hε1 hK0.le
    linarith
  have hmaxRf : max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2))) ≤ max 1 (3 * fieldRadius K) :=
    max_le_max le_rfl (by linarith)
  have hBle : ((D + 1 : ℕ) : ℝ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D * AT ≤
      Bst := by
    simp only [Bst, fieldBound]
    gcongr
  have hAle : 3 * (((D + 1 : ℕ) : ℝ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D *
      ((D : ℝ) * AT)) ≤ Ast := by
    simp only [Ast, fieldLip]
    gcongr
  have hU' : max 1 (K + pv) ≤ K + 1 := max_le (by linarith) (by linarith)
  have hU'0 : 0 ≤ max 1 (K + pv) := le_trans zero_le_one (le_max_left _ _)
  set X := a / h * wc with hX_def
  have hX : 0 < X := by positivity
  have hwidthH : simHeightError D (48 * K) ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err)
      (ε + ε * K) (pv / 2) (a / h * ε + ε * (40 * K))
      ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D * AT)
      (max 1 (K + pv))
      (3 * ((D + 1 : ℕ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D *
        ((D : ℝ) * AT))) ≤ X / 2 := by
    unfold simHeightError
    set Bε := ((D + 1 : ℕ) : ℝ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D * AT
    set Aε := 3 * (((D + 1 : ℕ) : ℝ) * (max 1 (3 * (K + K + 7 * (ε + ε * K + pv / 2)))) ^ D *
      ((D : ℝ) * AT))
    have hBε0 : 0 ≤ Bε := by positivity
    have hAε0 : 0 ≤ Aε := by positivity
    have t1 : a / h * ε ≤ X / 60 := by
      have := mul_le_mul_of_nonneg_left hε_wc hah.le
      simp only [X]; linarith
    have t2 : ε * (40 * K) ≤ X / 60 := by
      rw [le_div_iff₀ (by positivity)] at hε_K
      nlinarith
    have t3 : (8 * ((D : ℝ) + 2) * (48 * K)) ^ (D + 1) *
        ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err) ≤ X / 60 := by
      have hpos : 0 < 60 * (384 * K * ((D : ℝ) + 2)) ^ (D + 1) * (8 * ((D : ℝ) + 2) / η) ^ (D + 1) :=
        by positivity
      rw [le_div_iff₀ hpos] at herr2
      have he : (8 * ((D : ℝ) + 2) * (48 * K)) = 384 * K * ((D : ℝ) + 2) := by ring
      rw [he]
      nlinarith
    have t4 : 3 * Bε * (pv / 2) ≤ X / 60 := by
      rw [le_div_iff₀ (by positivity)] at hpv_le_B
      have h1 : Bε * pv ≤ Bst * pv := mul_le_mul_of_nonneg_right hBle hpv.le
      have h2 : Bst * pv ≤ (Bst + 1) * pv := by nlinarith
      nlinarith
    have t5 : 3 * max 1 (K + pv) * Aε * (ε + ε * K + pv / 2) +
        3 * max 1 (K + pv) * Aε * (6 * (ε + ε * K + pv / 2)) ≤ X / 60 := by
      have hsum : ε + ε * K + pv / 2 ≤ 2 * (X / (2520 * (K + 1) * (Ast + 1))) := by
        have h1 : ε * (1 + K) ≤ X / (2520 * (K + 1) * (Ast + 1)) := by
          rw [le_div_iff₀ (by positivity)] at hε_A
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        have h2 : pv / 2 ≤ X / (2520 * (K + 1) * (Ast + 1)) := by
          rw [le_div_iff₀ (by positivity)] at hpv_le_A
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith
      have hUA : max 1 (K + pv) * Aε ≤ (K + 1) * Ast :=
        mul_le_mul hU' hAle hAε0 (by linarith)
      have hfin : 21 * ((K + 1) * Ast) * (2 * (X / (2520 * (K + 1) * (Ast + 1)))) ≤ X / 60 := by
        rw [show 21 * ((K + 1) * Ast) * (2 * (X / (2520 * (K + 1) * (Ast + 1)))) =
          X / 60 * (Ast / (Ast + 1)) by field_simp; ring]
        apply mul_le_of_le_one_right (by positivity)
        rw [div_le_one (by positivity)]
        linarith
      have hsum0 : 0 ≤ ε + ε * K + pv / 2 := by positivity
      calc
        _ = 21 * (max 1 (K + pv) * Aε) * (ε + ε * K + pv / 2) := by ring
        _ ≤ 21 * ((K + 1) * Ast) * (2 * (X / (2520 * (K + 1) * (Ast + 1)))) := by
          gcongr
        _ ≤ X / 60 := hfin
    linarith [t1, t2, t3, t4, t5]
  have hwidthB : 6 * (ε + ε * K + pv / 2) ≤ pc / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε_pc
    linarith [hpv_le_pc]
  have hsmall : wc ^ (1 - d₁) * censusConstant D cNorm cCurl K Kr (2 * K) K pv ≤ ζ * rp ^ 9 := by
    have hmono := censusConstant_mono D cNorm cCurl (K := K) (Kr := Kr) (U := 2 * K) (V := K)
      (pv := pv) hK0.le (by linarith) (by linarith) hK0.le hpv1
    have hwp : 0 ≤ wc ^ (1 - d₁) := Real.rpow_nonneg hwc.le _
    calc
      _ ≤ wc ^ (1 - d₁) * C' := mul_le_mul_of_nonneg_left hmono hwp
      _ ≤ ζ * rp ^ 9 / C' * C' := mul_le_mul_of_nonneg_right hwcpow hC'.le
      _ = ζ * rp ^ 9 := by field_simp
  have herr : clock T * ((8 * ((D : ℝ) + 2) / η) ^ (D + 1) * err) ≤ a * ζ / 2 := by
    rw [le_div_iff₀ (by positivity)] at herr1
    rw [← hh_def]
    linarith [herr1]
  have hrw : 2 * (K + 1) * (rp + pv) ≤ K ^ (-100 : ℝ) := by
    have h1 : rp + pv ≤ 2 * rp := by linarith
    have h2 : 2 * (K + 1) * (2 * rp) = K ^ (-100 : ℝ) / 2 := by
      simp only [rp, pencilRadius]
      field_simp
      ring
    calc 2 * (K + 1) * (rp + pv) ≤ 2 * (K + 1) * (2 * rp) := by gcongr
      _ = K ^ (-100 : ℝ) / 2 := h2
      _ ≤ K ^ (-100 : ℝ) := by linarith [hKpow]
  have hr4 : rp + pv ≤ 1 / 4 := by
    have h1 : rp ≤ 1 / 8 := by
      rw [hrp_def, pencilRadius, div_le_iff₀ (by positivity)]
      linarith [hKpow1]
    linarith
  exact hfp q precision loss Nk L d₁ gain κ ν B r T j c u P hP A hA F H K ε S hε hεζ hεa ha haK
    hhζ hK2 hκK hKN hS hSHF hSA hSunit htime href hmass hpts hstrip hceil hband hcount st hstm
    hrefine hstripSt pv hpv π Kr hKr hrect rp hrp hrw hr4 pc wc hpc0 hpc1 hwc0 hwc1 hpw Tf hT hDq AT
    hAT hcoeffT hcoeffBudget Lines hLines times η err hη hη1 herr0
    (by rintro l ⟨z, hz, rfl⟩; exact htimes z hz)
    (by rintro l ⟨z, hz, rfl⟩; exact hfitL z hz)
    (2 * K) K (by linarith) hK0.le hbaseL hvelL hwidthH hwidthB hd₁ hsmall herr

end PacketSwitching

end

end Submission.Obl.k4_physical_row_packet_potential.Switch
