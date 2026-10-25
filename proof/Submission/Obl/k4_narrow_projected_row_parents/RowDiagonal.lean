/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowDiagonal.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowApply
import Submission.Obl.k4_narrow_projected_row_parents.RowParents
import Submission.Lib.K4ModelReduction.Diagonal

/-!
# Row parents from frequently row-ready parents

`rowParents_of_rowReady`: if row-ready parents at one depth `r` occur
frequently, with mesh `N^(-aξ)`, row accuracy `N^(-e)` (`e < aξ`) and a
subpower size `M`, then `RowParents cfg r` holds.  The Row loss `ε` is sent to
zero along the sequence by a diagonal choice, so the row-parent size stays
subpower; the palette interval bounds needed by Row come from the original
palette bin caps.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers Submission.Obl.k4_general_parent_projected_layers.PreparedModel Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Row parents are monotone in the error and the size bound. -/
def RowParent.weaken {p : Parameters} {a : PreparedModel α} {k : ℕ} {r E M E' M' : ℝ}
    (R : RowParent p a k r E M) (hE : E ≤ E') (hM0 : 0 < M) (hM : M ≤ M') :
    RowParent p a k r E' M' where
  Q := R.Q
  B := R.B
  lam := R.lam
  G := R.G
  measurable_G := R.measurable_G
  G_sub := R.G_sub
  mass := by
    refine le_trans ?_ R.mass
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (q_pos a k r).le hM0 hM)) _
  B_le := R.B_le.trans hM
  lam_le := R.lam_le.trans hM
  row := fun z hz => (R.row z hz).trans hE

/-- A diagonal index: from eventually-true statements for every `j`, an index
sequence tending to infinity along which they eventually hold. -/
theorem exists_diagonal {P : ℕ → ℕ → Prop} (h : ∀ j, ∀ᶠ k in atTop, P j k) :
    ∃ J : ℕ → ℕ, Tendsto J atTop atTop ∧ ∀ᶠ k in atTop, P (J k) k := by
  obtain ⟨J, _, hJ, _, hgood⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal P h
  exact ⟨J, hJ, hgood.mono fun k hk => hk (J k) le_rfl⟩

/-- Palette interval bounds from the palette bin caps: for every `η > 0`,
eventually every interval of radius `r' ∈ [N^(-aξ), 1]` has palette mass at
most `N^η r'^S`. -/
theorem palette_interval_eventually (cfg : Model α) (hv : Model.Valid cfg) {aξ η : ℝ}
    (haξ : 0 < aξ) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ x r' : ℝ, cfg.N k ^ (-aξ) ≤ r' → r' ≤ 1 →
      cfg.π k (Icc (x - r') (x + r')) ≤ ENNReal.ofReal (cfg.N k ^ η * r' ^ cfg.S) := by
  have hS := hv.palette_pos
  set R : ℝ := max (aξ + 1) (2 * cfg.S / η + 1) + 1 with hR
  have hR1 : 1 < R := by
    have : 0 < max (aξ + 1) (2 * cfg.S / η + 1) := lt_of_lt_of_le (by linarith)
      (le_max_left _ _)
    linarith
  have hRa : aξ ≤ R := by
    have := le_max_left (aξ + 1) (2 * cfg.S / η + 1); linarith
  have hRS : 2 * cfg.S / η ≤ R := by
    have := le_max_right (aξ + 1) (2 * cfg.S / η + 1); linarith
  have hNlim := hv.scale_limit
  have hK := hv.subpower.2 (η / 2) (by linarith)
  have hNbig : ∀ᶠ k in atTop, 2 ^ (cfg.S + 1) ≤ cfg.N k ^ (η / 2) ∧
      2 ≤ cfg.N k ^ (η / (2 * cfg.S)) := by
    have h1 : Tendsto (fun k => cfg.N k ^ (η / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hNlim
    have h2 : Tendsto (fun k => cfg.N k ^ (η / (2 * cfg.S))) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp hNlim
    exact (h1.eventually_ge_atTop _).and (h2.eventually_ge_atTop _)
  filter_upwards [hv.caps R hR1, hK, hNbig] with k hcap hKk hNk
  intro x r' hr'lo hr'1
  have hN2 := hv.scale k
  have hNpos : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hr'pos : 0 < r' := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos _) hr'lo
  haveI := (hv.basic k).2.2.1
  by_cases hbig : cfg.N k ^ (-η / cfg.S) ≤ r'
  · -- the bound is at least one
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (cfg.N k ^ (-η / cfg.S)) ^ cfg.S ≤ r' ^ cfg.S :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hbig hS.le
    rw [← Real.rpow_mul hNpos.le, div_mul_cancel₀ _ hS.ne'] at h1
    calc (1 : ℝ) = cfg.N k ^ η * cfg.N k ^ (-η) := by
          rw [← Real.rpow_add hNpos]; simp
      _ ≤ cfg.N k ^ η * r' ^ cfg.S :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNpos.le _)
  · push Not at hbig
    -- the scale `N^(-v) = 2 r'`
    set v : ℝ := Real.logb (cfg.N k) (1 / (2 * r')) with hvdef
    have h2r : 0 < 2 * r' := by linarith
    have hNv : cfg.N k ^ (-v) = 2 * r' := by
      rw [Real.rpow_neg hNpos.le, hvdef,
        Real.rpow_logb hNpos (by linarith) (by positivity)]
      field_simp
    have hlogN : 0 < Real.log (cfg.N k) := Real.log_pos (by linarith)
    have hvle : v ≤ R := by
      have : v ≤ aξ := by
        have h3 : 1 / (2 * r') ≤ cfg.N k ^ aξ := by
          rw [div_le_iff₀ h2r]
          have : cfg.N k ^ aξ * cfg.N k ^ (-aξ) = 1 := by
            rw [← Real.rpow_add hNpos]; simp
          nlinarith [Real.rpow_pos_of_pos hNpos aξ]
        calc v = Real.logb (cfg.N k) (1 / (2 * r')) := rfl
          _ ≤ Real.logb (cfg.N k) (cfg.N k ^ aξ) :=
              Real.logb_le_logb_of_le (by linarith) (by positivity) h3
          _ = aξ := Real.logb_rpow hNpos (by linarith)
      linarith
    have hvge : R⁻¹ ≤ v := by
      have h4 : cfg.N k ^ (η / (2 * cfg.S)) ≤ 1 / (2 * r') := by
        rw [le_div_iff₀ h2r]
        have h5 : cfg.N k ^ (η / (2 * cfg.S)) * cfg.N k ^ (-η / cfg.S) =
            cfg.N k ^ (-(η / (2 * cfg.S))) := by
          rw [← Real.rpow_add hNpos]; congr 1; field_simp; ring
        have h6 : cfg.N k ^ (-(η / (2 * cfg.S))) ≤ 1 / 2 := by
          rw [Real.rpow_neg hNpos.le]
          rw [inv_le_comm₀ (Real.rpow_pos_of_pos hNpos _) (by norm_num)]
          linarith [hNk.2]
        nlinarith [Real.rpow_pos_of_pos hNpos (η / (2 * cfg.S))]
      have h7 : η / (2 * cfg.S) ≤ v := by
        calc η / (2 * cfg.S) = Real.logb (cfg.N k) (cfg.N k ^ (η / (2 * cfg.S))) :=
              (Real.logb_rpow hNpos (by linarith)).symm
          _ ≤ v := Real.logb_le_logb_of_le (by linarith)
              (Real.rpow_pos_of_pos hNpos _) h4
      have h8 : R⁻¹ ≤ η / (2 * cfg.S) := by
        rw [inv_le_comm₀ (by linarith) (by positivity)]
        calc (η / (2 * cfg.S))⁻¹ = 2 * cfg.S / η := by rw [inv_div]
          _ ≤ R := hRS
      linarith
    obtain ⟨hπbin, -, -⟩ := hcap 1 0 v (by rw [inv_le_one₀ (by linarith)]; linarith)
      (by linarith) le_rfl (by linarith) hvge hvle
    -- two bins cover the interval
    set j : ℤ := ⌊(x - r') / cfg.N k ^ (-v)⌋ with hj
    have hcover : Icc (x - r') (x + r') ⊆
        {w | ⌊w / cfg.N k ^ (-v)⌋ = j} ∪ {w | ⌊w / cfg.N k ^ (-v)⌋ = j + 1} := by
      intro w hw
      have hw1 := hw.1
      have hw2 := hw.2
      rw [hNv] at hj ⊢
      have hlo : ⌊(x - r') / (2 * r')⌋ ≤ ⌊w / (2 * r')⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right hw1 h2r.le)
      have hhi : ⌊w / (2 * r')⌋ ≤ ⌊(x - r') / (2 * r')⌋ + 1 := by
        have : w / (2 * r') ≤ (x - r') / (2 * r') + 1 := by
          rw [div_add_one h2r.ne', div_le_div_iff_of_pos_right h2r]; linarith
        calc ⌊w / (2 * r')⌋ ≤ ⌊(x - r') / (2 * r') + 1⌋ := Int.floor_mono this
          _ = ⌊(x - r') / (2 * r')⌋ + 1 := Int.floor_add_one _
      rcases eq_or_lt_of_le hlo with h | h
      · left; show ⌊w / (2 * r')⌋ = j; rw [hj]; exact h.symm
      · right; show ⌊w / (2 * r')⌋ = j + 1; rw [hj]; omega
    have hbinS : cfg.N k ^ (-cfg.S * v) = (2 * r') ^ cfg.S := by
      rw [← hNv, ← Real.rpow_mul hNpos.le]; ring_nf
    calc cfg.π k (Icc (x - r') (x + r'))
        ≤ cfg.π k ({w | ⌊w / cfg.N k ^ (-v)⌋ = j} ∪ {w | ⌊w / cfg.N k ^ (-v)⌋ = j + 1}) :=
          measure_mono hcover
      _ ≤ cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j} +
            cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j + 1} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v)) +
            ENNReal.ofReal (cfg.K k * cfg.N k ^ (-cfg.S * v)) := add_le_add (hπbin j) (hπbin _)
      _ = ENNReal.ofReal (2 * (cfg.K k * cfg.N k ^ (-cfg.S * v))) := by
          have h0 : 0 ≤ cfg.K k * cfg.N k ^ (-cfg.S * v) :=
            mul_nonneg (by linarith [hv.subpower.1 k]) (Real.rpow_nonneg hNpos.le _)
          rw [← ENNReal.ofReal_add h0 h0]; ring_nf
      _ ≤ ENNReal.ofReal (cfg.N k ^ η * r' ^ cfg.S) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hbinS, Real.mul_rpow (by norm_num) hr'pos.le]
          have hK1 : 1 ≤ cfg.K k := hv.subpower.1 k
          have h2S : (2 : ℝ) ^ cfg.S * 2 = 2 ^ (cfg.S + 1) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_one]
          have hsplit : cfg.N k ^ η = cfg.N k ^ (η / 2) * cfg.N k ^ (η / 2) := by
            rw [← Real.rpow_add hNpos]; ring_nf
          have hr'S : 0 ≤ r' ^ cfg.S := Real.rpow_nonneg hr'pos.le _
          have hKN : 2 ^ (cfg.S + 1) * cfg.K k ≤ cfg.N k ^ η := by
            rw [hsplit]
            exact mul_le_mul hNk.1 hKk (by linarith) (Real.rpow_nonneg hNpos.le _)
          calc 2 * (cfg.K k * (2 ^ cfg.S * r' ^ cfg.S))
              = (2 ^ cfg.S * 2) * cfg.K k * r' ^ cfg.S := by ring
            _ = 2 ^ (cfg.S + 1) * cfg.K k * r' ^ cfg.S := by rw [h2S]
            _ ≤ cfg.N k ^ η * r' ^ cfg.S := mul_le_mul_of_nonneg_right hKN hr'S

/-- **Row parents from row-ready parents.** -/
theorem rowParents_of_rowReady (hRow : Row) (cfg : Model α) (hv : Model.Valid cfg)
    {r e aξ : ℝ} (he : 0 < e) (heξ : e < aξ) (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k)
    (hMsub : Model.Subpow cfg.N M)
    (hfreq : ∃ᶠ k in atTop, Nonempty (RowReady (Model.parameters cfg) (Model.prepared cfg) k r
      (cfg.N k ^ (-aξ)) (cfg.N k ^ (-e)) (M k))) :
    RowParents cfg r := by
  have haξ : 0 < aξ := he.trans heξ
  -- Row losses tending to zero
  let εj : ℕ → ℝ := fun j => e / (4 * ((j : ℝ) + 1))
  have hεpos : ∀ j, 0 < εj j := fun j => by positivity
  have hεle : ∀ j, εj j ≤ e / 4 := fun j => by
    simp only [εj]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hεlim : Tendsto εj atTop (nhds 0) := by
    have h1 : Tendsto (fun j : ℕ => 4 * ((j : ℝ) + 1)) atTop atTop := by
      refine Tendsto.const_mul_atTop (by norm_num) ?_
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [εj] using (tendsto_const_nhds (x := e)).div_atTop h1
  have hrow : ∀ j, ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ (p : Parameters) (a : PreparedModel α) (k : ℕ) (r E M : ℝ),
        N₀ ≤ p.N k → 1 ≤ M → 2 * M ≤ p.N k ^ η → p.K k ≤ p.N k ^ η →
        p.N k ^ (-aξ) ≤ E → E ≤ 1 →
        Measurable (a.b k) → IsProbabilityMeasure (a.nu k) → IsProbabilityMeasure (a.pi k) →
        a.mu k ≤ ENNReal.ofReal (p.K k) • (a.nu k).prod volume → a.rho k ≤ a.mu k →
        (∀ x r' : ℝ, p.N k ^ (-aξ) ≤ r' → r' ≤ 1 →
          a.pi k (Icc (x - r') (x + r')) ≤ ENNReal.ofReal (p.N k ^ η * r' ^ cfg.S)) →
        RowReady p a k r (p.N k ^ (-aξ)) E M →
        Nonempty (RowParent p a k r ((M + p.N k ^ εj j * (1 + M)) * E)
          (max M (p.N k ^ εj j))) := by
    intro j
    obtain ⟨η, hη, N₀, hN₀, h⟩ :=
      rowParent_of_rowReady_at (α := α) hRow hv.palette_pos haξ (hεpos j)
    exact ⟨η, hη, N₀, hN₀, fun p a k r E M h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =>
      h p a k r E M h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13⟩
  choose η hη N₀ hN₀ hrowj using hrow
  -- the conditions at index `k` for the loss `εj j`
  let good : ℕ → ℕ → Prop := fun j k =>
    N₀ j ≤ cfg.N k ∧ 2 * M k ≤ cfg.N k ^ η j ∧ cfg.K k ≤ cfg.N k ^ η j ∧
    (∀ x r' : ℝ, cfg.N k ^ (-aξ) ≤ r' → r' ≤ 1 →
      cfg.π k (Icc (x - r') (x + r')) ≤ ENNReal.ofReal (cfg.N k ^ η j * r' ^ cfg.S)) ∧
    (M k + cfg.N k ^ εj j * (1 + M k)) * cfg.N k ^ (-e) ≤ cfg.N k ^ (-(e / 2))
  have hgood : ∀ j, ∀ᶠ k in atTop, good j k := by
    intro j
    have hNlim := hv.scale_limit
    have hA : ∀ᶠ k in atTop, N₀ j ≤ cfg.N k := hNlim.eventually_ge_atTop _
    have hB : ∀ᶠ k in atTop, 2 * M k ≤ cfg.N k ^ η j := by
      have h1 := hMsub (η j / 2) (by linarith [hη j])
      have h2 : ∀ᶠ k in atTop, 2 ≤ cfg.N k ^ (η j / 2) :=
        ((tendsto_rpow_atTop (by linarith [hη j])).comp hNlim).eventually_ge_atTop _
      filter_upwards [h1, h2] with k hk1 hk2
      have hN := hv.scale k
      calc 2 * M k ≤ cfg.N k ^ (η j / 2) * cfg.N k ^ (η j / 2) :=
            mul_le_mul hk2 hk1 (by linarith [hM1 k]) (Real.rpow_nonneg (by linarith) _)
        _ = cfg.N k ^ η j := by rw [← Real.rpow_add (by linarith)]; ring_nf
    have hC : ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ η j := hv.subpower.2 _ (hη j)
    have hD := palette_interval_eventually cfg hv haξ (hη j)
    have hE : ∀ᶠ k in atTop,
        (M k + cfg.N k ^ εj j * (1 + M k)) * cfg.N k ^ (-e) ≤ cfg.N k ^ (-(e / 2)) := by
      have h1 := hMsub (e / 8) (by linarith)
      have h2 : ∀ᶠ k in atTop, 3 ≤ cfg.N k ^ (e / 8) :=
        ((tendsto_rpow_atTop (by linarith)).comp hNlim).eventually_ge_atTop _
      filter_upwards [h1, h2] with k hk1 hk2
      have hN := hv.scale k
      have hNpos : 0 < cfg.N k := by linarith
      have hN1 : 1 ≤ cfg.N k := by linarith
      have hε4 : cfg.N k ^ εj j ≤ cfg.N k ^ (e / 4) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (hεle j)
      have hpos8 : 0 < cfg.N k ^ (e / 8) := Real.rpow_pos_of_pos hNpos _
      have hM1k := hM1 k
      -- (M + N^ε (1 + M)) ≤ 3 N^(3e/8)
      have hsum : M k + cfg.N k ^ εj j * (1 + M k) ≤ 3 * cfg.N k ^ (3 * e / 8) := by
        have h38 : cfg.N k ^ (3 * e / 8) = cfg.N k ^ (e / 4) * cfg.N k ^ (e / 8) := by
          rw [← Real.rpow_add hNpos]; ring_nf
        have hge1 : 1 ≤ cfg.N k ^ (e / 8) := Real.one_le_rpow hN1 (by linarith)
        have hge1' : 1 ≤ cfg.N k ^ (e / 4) := Real.one_le_rpow hN1 (by linarith)
        have hMk : 1 + M k ≤ 2 * cfg.N k ^ (e / 8) := by linarith
        have h1' : M k ≤ cfg.N k ^ (e / 4) * cfg.N k ^ (e / 8) := by nlinarith
        have h2' : cfg.N k ^ εj j * (1 + M k) ≤ cfg.N k ^ (e / 4) * (2 * cfg.N k ^ (e / 8)) :=
          mul_le_mul hε4 hMk (by linarith) (by linarith)
        rw [h38]; nlinarith
      have hNe : 0 < cfg.N k ^ (-e) := Real.rpow_pos_of_pos hNpos _
      calc (M k + cfg.N k ^ εj j * (1 + M k)) * cfg.N k ^ (-e)
          ≤ 3 * cfg.N k ^ (3 * e / 8) * cfg.N k ^ (-e) := mul_le_mul_of_nonneg_right hsum hNe.le
        _ = 3 * cfg.N k ^ (-(e / 8)) * cfg.N k ^ (-(e / 2)) := by
            rw [mul_assoc, mul_assoc, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; ring_nf
        _ ≤ 1 * cfg.N k ^ (-(e / 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
            rw [Real.rpow_neg hNpos.le]
            rw [← div_eq_mul_inv, div_le_one hpos8]
            exact hk2
        _ = cfg.N k ^ (-(e / 2)) := one_mul _
    filter_upwards [hA, hB, hC, hD, hE] with k h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨J, hJ, hJgood⟩ := exists_diagonal hgood
  -- the size bound
  let M' : ℕ → ℝ := fun k => max (M k) (cfg.N k ^ εj (J k))
  refine ⟨e / 2, by linarith, M', fun k => le_trans (hM1 k) (le_max_left _ _), ?_, ?_⟩
  · intro ε' hε'
    have h1 := hMsub ε' hε'
    have h2 : ∀ᶠ k in atTop, εj (J k) ≤ ε' :=
      (hεlim.comp hJ).eventually (ge_mem_nhds hε')
    filter_upwards [h1, h2] with k hk1 hk2
    refine max_le hk1 ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hv.scale k]) hk2
  · refine (hfreq.and_eventually hJgood).mono ?_
    rintro k ⟨⟨R⟩, h1, h2, h3, h4, h5⟩
    have hb := hv.basic k
    have hN := hv.scale k
    have hNpos : 0 < cfg.N k := by linarith
    have hE1 : cfg.N k ^ (-e) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hξE : cfg.N k ^ (-aξ) ≤ cfg.N k ^ (-e) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    obtain ⟨RP⟩ := hrowj (J k) (Model.parameters cfg) (Model.prepared cfg) k r (cfg.N k ^ (-e))
      (M k) h1 (hM1 k) h2 h3 hξE hE1 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 h4 R
    exact ⟨RP.weaken h5 (lt_of_lt_of_le one_pos (le_max_of_le_left (hM1 k))) le_rfl⟩

end

end Submission.Obl.k4_narrow_projected_row_parents
