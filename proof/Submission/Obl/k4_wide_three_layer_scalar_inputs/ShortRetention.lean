import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.PairComparison
import Submission.Obl.k4_wide_three_layer_scalar_inputs.EntryBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortCore
import Submission.Obl.k4_wide_three_layer_scalar_inputs.BoundedKeys
import Submission.Obl.k4_wide_three_layer_scalar_inputs.LayerBridge

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Finset
open scoped ENNReal
open Inherited.Native Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ}

/-- One common exceptional set for the original three compared layers. -/
def ComparedLayers.shortException {σ R χ D s u : ℝ} {depth : Fin 3 → ℝ}
    (L : ComparedLayers cfg k σ R χ D depth s u) (η ξ : ℝ) : Set (α × ℝ) :=
  let q := slotLen cfg.comparisonData k s
  let m := q * cfg.N k ^ (-cfg.κ * s)
  shortBad cfg.comparisonData k s L.comparisonDatum m (cfg.N k ^ (10 * η)) (cfg.N k ^ ξ)
    (boundedKeys χ m (4 * cfg.N k ^ η))

/-- The actual table budgets and comparison numerics pay the entire short
exception. No bound on the universal key box's cardinality is used. -/
theorem ComparedLayers.shortException_le {buffer σ η ξ ηmatch R₀ R Rcap : ℝ}
    (p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer)
    (L : ComparedLayers cfg k σ R (cfg.N k ^ (-p.M)) (cfg.N k ^ (-2 * cfg.κ * p.s₀))
      ![p.s, p.s + p.u, p.s + p.v] p.s p.u)
    (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    [IsProbabilityMeasure (cfg.ν k)] [IsProbabilityMeasure (cfg.π k)]
    [IsFiniteMeasure (cfg.μ k)] (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hB : BlocksAt cfg.comparisonData k p.s Rcap)
    (hPC : PairComparison α cfg.d ηmatch R₀)
    (cn : ComparisonNumerics (cfg.N k) (cfg.K k) cfg.d cfg.κ p.s₀ p.s p.u p.v p.M cfg.e₀
      σ η ξ ηmatch R₀ (slotLen cfg.comparisonData k p.s))
    (hcap : ∀ sp : ℝ, 0 ≤ sp → sp ≤ p.s + p.u →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d (2 * p.M) sp p.M)
    (hnull : L.ρs (horizSet (cfg.b k) (cfg.N k ^ (-cfg.e₀)))ᶜ = 0) :
    L.ρs (L.shortException η ξ) ≤ ENNReal.ofReal (cfg.N k ^ (-η)) := by
  classical
  let N := cfg.N k
  let K := cfg.K k
  let q := slotLen cfg.comparisonData k p.s
  let g := N ^ (-cfg.κ * p.s)
  let χ := N ^ (-p.M)
  let D := N ^ (-2 * cfg.κ * p.s₀)
  let m := q * g
  let H := N ^ η
  let KB := boundedKeys χ m (4 * H)
  let LD := L.comparisonDatum
  have hNp : 0 < N := by dsimp [N]; linarith
  have hKp : 0 < K := by dsimp [K]; linarith
  have hq : 0 < q := slotLen_pos cfg.comparisonData k p.s
  have hg : 0 < g := Real.rpow_pos_of_pos hNp _
  have hχ : 0 < χ := Real.rpow_pos_of_pos hNp _
  have hD : 0 < D := Real.rpow_pos_of_pos hNp _
  have hm : 0 < m := mul_pos hq hg
  have hH : 1 ≤ H := by dsimp [H, N]; linarith [cn.input_one, cn.input_budget]
  have hρsμ : L.ρs ≤ cfg.μ k := L.le_rho.trans hρμ
  let : IsFiniteMeasure L.ρs := isFiniteMeasure_of_le (cfg.μ k) hρsμ
  have hr : RawShortBudget (N ^ p.s₀) H K q (N ^ (-p.s)) g D χ (N ^ (-cfg.e₀)) (N ^ σ) := by
    simpa only [Matrix.cons_val_zero] using cn.raw 0
  have hpow10 : (N ^ p.s₀) ^ 10 = N ^ (10 * p.s₀) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  have hnum : ∀ jj : Fin (2 ^ cfg.T k p.s), ∀ key ∈ KB,
      KeyNum N K cfg.d (2 * p.M) p.M p.s (p.s - 2 * η)
        (slotStart cfg.comparisonData k p.s jj) q m (N ^ (-cfg.e₀)) (4 * H)
        (N ^ (-p.s)) (2 * H) (N ^ (10 * η)) (N ^ (10 * p.s₀))
        (rawBlockError H K q (N ^ (-p.s)) χ (N ^ (-cfg.e₀)))
        (rawSheetError (N ^ σ) q (N ^ (-p.s)) D χ (N ^ (-cfg.e₀)))
        (4 * H) (N ^ ξ) (N ^ (20 * η)) (N ^ (-p.M / 4)) ηmatch R₀ key := by
    intro jj key hk
    obtain ⟨hk0, hk1, -⟩ := boundedKeys_bound hk
    simpa only [Matrix.cons_val_zero] using
      cn.keys 0 (slotStart cfg.comparisonData k p.s jj) key (slot_unit cfg.comparisonData k p.s jj)
        hk0 hk1 _ _ hr.block_tolerance.1 hr.block_tolerance.2 hr.sheet_tolerance.1 hr.sheet_tolerance.2
  have hbad := short_bad_le cfg.comparisonData hPC k p.s LD rfl hB hb inferInstance hρsμ KB
    (r := 2 * p.M) (v' := p.M) (Rc := p.s) (s₁ := p.s - 2 * η)
    (ζ := N ^ (-cfg.e₀)) (Lv := 4 * H) (Xb := 2 * H) (B := N ^ (10 * p.s₀))
    (δ := 4 * H) (A := N ^ (20 * η)) (w := N ^ (-p.M / 4))
    rfl hNp (fun sp hsp0 hsp1 => hcap sp hsp0 (by linarith [p.u_pos]))
    (by simpa only [rawBlockError, rawBlockBound, rawSheetError, Matrix.cons_val_zero] using hnum)
    (fun key hk => boundedKeys_bound hk) hnull hχ hD hm hK
    (by dsimp [H, N]; linarith [cn.input_budget]) (by linarith)
    cn.native_accuracy cn.strip_drift cn.whole_key_strip
    (by simpa only [rawBlockBound, hpow10] using hr.block_coeff)
    (by simpa only [hpow10] using hr.sheet_coeff)
  let b := blockSum cfg.comparisonData k p.s LD m KB
  let pp := fun h : Fin 3 => pieceSum cfg.comparisonData k p.s LD m KB h
  have hb0 : 0 ≤ b := by
    unfold b blockSum
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro key _
    exact shortBound_keyRef_nonneg cfg.comparisonData k hχ.le hm.le hq.le
      (Real.rpow_nonneg hNp.le _) key
  have hp0 : ∀ h, 0 ≤ pp h := by
    intro h
    unfold pp pieceSum
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro jj _
    apply Finset.sum_nonneg
    intro key _
    exact shortBound_keyRef_nonneg cfg.comparisonData k hχ.le hm.le hq.le
      (Real.rpow_nonneg hNp.le _) key
  have hbK : b ≤ 140 * K ^ 3 :=
    blockSum_le cfg.comparisonData k p.s LD hB hNp hK hχ hm cn.short.chi_q cn.short.chi_m le_rfl KB
  have hpN : ∀ h, pp h ≤ 6 * N ^ (2 * σ) := by
    intro h
    have hh := pieceSum_le cfg.comparisonData k p.s LD hNp cn.input_one hχ hD hm cn.short.m_D KB h
    convert hh using 1
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 2
    ring
  have htab := cn.table_loss b pp hb0 hbK hp0 hpN
  have hK₁ : 0 ≤ N ^ (10 * η) := Real.rpow_nonneg hNp.le _
  have hsum : 0 ≤ ∑ h : Fin 3, pp h / N ^ (10 * η) :=
    Finset.sum_nonneg fun h _ => div_nonneg (hp0 h) hK₁
  have hpp0 : 0 ≤ pp 0 := hp0 0
  have hterm : 0 ≤ N ^ (20 * η) * (N ^ ξ / (4 * H)) ^ (-ηmatch) * (b + pp 0) := by positivity
  calc L.ρs (L.shortException η ξ)
      ≤ ENNReal.ofReal (b / N ^ (10 * η)) + ∑ h : Fin 3, ENNReal.ofReal (pp h / N ^ (10 * η)) +
        ENNReal.ofReal (N ^ (20 * η) * (N ^ ξ / (4 * H)) ^ (-ηmatch) * (b + pp 0)) := hbad
    _ = ENNReal.ofReal (b / N ^ (10 * η) + (∑ h : Fin 3, pp h / N ^ (10 * η)) +
        N ^ (20 * η) * (N ^ ξ / (4 * H)) ^ (-ηmatch) * (b + pp 0)) := by
        rw [ENNReal.ofReal_add (add_nonneg (div_nonneg hb0 hK₁) hsum) hterm,
          ENNReal.ofReal_add (div_nonneg hb0 hK₁) hsum,
          ENNReal.ofReal_sum_of_nonneg (fun h _ => div_nonneg (hp0 h) hK₁)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal htab.1

/-- Delete the short exception once and choose a dense ORIGINAL true block.
The resulting mass floor uses the full assignment prior, with all three
projected labels still belonging to the same original retained law. -/
theorem exists_short_retained_block {buffer σ η ξ ηmatch R₀ R Rcap : ℝ}
    (p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer)
    (L : ComparedLayers cfg k σ R (cfg.N k ^ (-p.M)) (cfg.N k ^ (-2 * cfg.κ * p.s₀))
      ![p.s, p.s + p.u, p.s + p.v] p.s p.u)
    (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    [IsProbabilityMeasure (cfg.ν k)] [IsProbabilityMeasure (cfg.π k)]
    [IsFiniteMeasure (cfg.μ k)] (hb : Measurable (cfg.b k)) (hρμ : cfg.ρ k ≤ cfg.μ k)
    (hB : BlocksAt cfg.comparisonData k p.s Rcap)
    (hPC : PairComparison α cfg.d ηmatch R₀)
    (cn : ComparisonNumerics (cfg.N k) (cfg.K k) cfg.d cfg.κ p.s₀ p.s p.u p.v p.M cfg.e₀
      σ η ξ ηmatch R₀ (slotLen cfg.comparisonData k p.s))
    (hcap : ∀ sp : ℝ, 0 ≤ sp → sp ≤ p.s + p.u →
      JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d (2 * p.M) sp p.M)
    (hnull : L.ρs (horizSet (cfg.b k) (cfg.N k ^ (-cfg.e₀)))ᶜ = 0) :
    ∃ (i : Fin (cfg.n k p.s)) (lam : Measure (α × ℝ)),
      lam ≤ L.ρs ∧ lam ≤ cfg.ρ k ∧
      (∀ᵐ z ∂lam, z.1 ∈ cfg.B k p.s i ∧ z.2 ∈ cfg.comparisonData.I (cfg.T k p.s) (cfg.j k p.s i)) ∧
      ENNReal.ofReal (cfg.N k ^ (-η)) *
        (ENNReal.ofReal (slotLen cfg.comparisonData k p.s) * cfg.ν k (cfg.A k p.s i)) ≤ lam univ ∧
      0 < lam univ ∧ ∀ᵐ z ∂lam, z ∉ L.shortException η ξ := by
  have hNp : 0 < cfg.N k := by linarith
  have hKp : 0 < cfg.K k := by linarith
  have hbad := ComparedLayers.shortException_le p L hN hK hb hρμ hB hPC cn hcap hnull
  have hBm := measurableSet_shortBad cfg.comparisonData k p.s L.comparisonDatum hB hb
    (boundedKeys (cfg.N k ^ (-p.M))
      (slotLen cfg.comparisonData k p.s * cfg.N k ^ (-cfg.κ * p.s)) (4 * cfg.N k ^ η))
      (m := slotLen cfg.comparisonData k p.s * cfg.N k ^ (-cfg.κ * p.s))
      (K₁ := cfg.N k ^ (10 * η)) (Mst := cfg.N k ^ ξ)
  let τ := L.ρs.restrict (L.shortException η ξ)ᶜ
  have hτ : τ ≤ L.ρs := Measure.restrict_le_self
  have hkeep := (cn.table_loss 0 (fun _ => 0) (by norm_num) (by positivity)
    (by simp) (by intro h; positivity)).2
  have hmass : ENNReal.ofReal (cfg.N k ^ (-η)) ≤ τ univ :=
    restrict_compl_mass L.ρs _ hBm (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
      L.mass hbad hkeep
  obtain ⟨i, lam, hLamTau, hsupp, hLamMass⟩ := exists_dense_original_block cfg.comparisonData k p.s hB
    τ (hτ.trans (L.le_rho.trans hρμ)) (Real.rpow_pos_of_pos hNp _) hmass
  refine ⟨i, lam, hLamTau.trans hτ, (hLamTau.trans hτ).trans L.le_rho, hsupp, hLamMass, ?_, ?_⟩
  · have hq := slotLen_pos cfg.comparisonData k p.s
    have hfloor : 0 < ENNReal.ofReal ((cfg.N k ^ (-p.s)) ^ cfg.d *
        (slotLen cfg.comparisonData k p.s) ^ 2 * cfg.N k ^ (-cfg.κ * p.s) / cfg.K k) := by
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos
        (Real.rpow_pos_of_pos hNp _) _) (by positivity)) (Real.rpow_pos_of_pos hNp _)) hKp
    have hprior : 0 < cfg.ν k (cfg.A k p.s i) := hfloor.trans_le (hB.nu_lo i)
    have hpref : ENNReal.ofReal (cfg.N k ^ (-η)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNp _)).ne'
    have hqref : ENNReal.ofReal (slotLen cfg.comparisonData k p.s) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hq).ne'
    have hpos : 0 < ENNReal.ofReal (cfg.N k ^ (-η)) *
        (ENNReal.ofReal (slotLen cfg.comparisonData k p.s) * cfg.ν k (cfg.A k p.s i)) :=
      bot_lt_iff_ne_bot.mpr (mul_ne_zero hpref (mul_ne_zero hqref hprior.ne'))
    exact hpos.trans_le hLamMass
  · exact ae_mono hLamTau (ae_restrict_mem hBm.compl)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
