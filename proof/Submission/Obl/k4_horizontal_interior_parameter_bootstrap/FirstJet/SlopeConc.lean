import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Concentrate

/-!
# A heavy slope interval in every good group

Paper Proposition 5.4, "Concentrating the residual slopes": in a good group, some interval of
slopes of width `≍ p₀^γ` carries a fixed fraction of the group. Quantitatively
(`exists_heavy_slope_interval`): if the labeled incidences of the retained lines `G` follow
lines `z + u k` up to `e`, every time meets at most `C₁` scalar bins of width `p`, every
(cell, bin) at a time has mass at most `C₂`, slopes vary by at most `V` inside a cell, and
every cell meeting `G` has mass at least `f`, then some slope interval of radius `w + V`
carries `G`-mass at least `m` as soon as `C₁ C₂ (m/f + 1) ≤ M₀/2` and the far-slope term
`C₁ (2(p+2e)/w) ν(Ω)²` is below `M₀²/2`, where `M₀` bounds the labeled incidence mass from
below.

The proof applies `slope_concentration_ineq` (x0763) with the cell map `cellOf` sending
lines outside `G` to the junk cell `none`: if every slope interval were light, the lines with
slopes `w`-close to any given slope would meet fewer than `m/f` cells.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- The cell of a retained line, `none` outside `G`. -/
def cellOf {Ω ι : Type*} (G : Set Ω) (cell : Ω → ι) (l : Ω) : Option ι := by
  classical
  exact if l ∈ G then some (cell l) else none

theorem exists_heavy_slope_interval {Ω ι : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    (hE01 : ∀ q ∈ E, q.2 ∈ Icc (0:ℝ) 1) {G : Set Ω} (hG : MeasurableSet G)
    (hEG : ∀ q ∈ E, q.1 ∈ G) {z k : Ω → ℝ} (hk : Measurable k) {L : Ω → ℝ → ℝ}
    (hL : Measurable (fun q : Ω × ℝ => L q.1 q.2)) (cell : Ω → ι)
    (hcellm : ∀ γ, MeasurableSet {l | cell l = γ})
    {p e w C₁ C₂ V f m M₀ : ℝ} (hp : 0 < p) (hw : 0 < w) (hV : 0 ≤ V) (hf : 0 < f)
    (hm : 0 ≤ m) (hM₀ : 0 < M₀)
    (hmodel : ∀ q ∈ E, |L q.1 q.2 - (z q.1 + q.2 * k q.1)| ≤ e)
    (hcount : ∀ u, ∃ B : Finset ℤ, (B.card : ℝ) ≤ C₁ ∧ ∀ l, (l, u) ∈ E → ⌊L l u / p⌋ ∈ B)
    (hcap : ∀ (u : ℝ) (γ : ι) (b : ℤ),
      ν {l | (l, u) ∈ E ∧ cell l = γ ∧ ⌊L l u / p⌋ = b} ≤ ENNReal.ofReal C₂)
    (hvar : ∀ l ∈ G, ∀ l' ∈ G, cell l = cell l' → |k l - k l'| ≤ V)
    (hfloor : ∀ l ∈ G, ENNReal.ofReal f ≤ ν (G ∩ {l' | cell l' = cell l}))
    (hmass : ENNReal.ofReal M₀ ≤ (ν.prod volume) E)
    (hC : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hbudget : C₁ * C₂ * (m / f + 2) ≤ M₀ / 2)
    (hfar : ENNReal.ofReal C₁ * (ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2) <
      ENNReal.ofReal (M₀ ^ 2 / 2)) :
    ∃ κ₀ : ℝ, ENNReal.ofReal m ≤ ν (G ∩ {l | |k l - κ₀| ≤ w + V}) := by
  classical
  by_contra hcon
  push Not at hcon
  -- the number of cells met by `w`-close slopes
  set Nc : ℕ := ⌊m / f⌋₊ + 2 with hNc
  have hcells : ∀ l, ∃ Γ : Finset (Option ι), Γ.card ≤ Nc ∧
      ∀ l', |k l' - k l| ≤ w → cellOf G cell l' ∈ Γ := by
    intro l
    -- the cells of `G`-lines with slopes `w`-close to `k l`
    set S : Set Ω := G ∩ {l' | |k l' - k l| ≤ w} with hS
    set T : Set ι := cell '' S with hT
    -- every cell in `T` lies in the slope window of radius `w + V`
    have hwin : ∀ γ ∈ T, G ∩ {l' | cell l' = γ} ⊆ G ∩ {l' | |k l' - k l| ≤ w + V} := by
      rintro γ ⟨l₀, ⟨hl₀G, hl₀k⟩, rfl⟩ l' ⟨hl'G, hl'c⟩
      refine ⟨hl'G, ?_⟩
      have := hvar l' hl'G l₀ hl₀G hl'c
      simp only [mem_ofPred_eq] at hl₀k ⊢
      calc |k l' - k l| = |(k l' - k l₀) + (k l₀ - k l)| := by ring_nf
        _ ≤ |k l' - k l₀| + |k l₀ - k l| := abs_add_le _ _
        _ ≤ V + w := add_le_add this hl₀k
        _ = w + V := by ring
    -- `T` is finite with fewer than `m / f + 1` elements
    have hfinite : ∀ F : Finset ι, (↑F : Set ι) ⊆ T → (F.card : ℝ) * f ≤ m := by
      intro F hF
      have hdisj : Set.PairwiseDisjoint (↑F : Set ι) (fun γ => G ∩ {l' | cell l' = γ}) := by
        intro γ _ γ' _ hγ
        refine Set.disjoint_left.mpr ?_
        rintro l' ⟨-, h1⟩ ⟨-, h2⟩
        exact hγ (h1.symm.trans h2)
      have hunion : ⋃ γ ∈ F, G ∩ {l' | cell l' = γ} ⊆ G ∩ {l' | |k l' - k l| ≤ w + V} :=
        iUnion₂_subset (fun γ hγ => hwin γ (hF hγ))
      have hmeas : ∀ γ ∈ F, MeasurableSet (G ∩ {l' | cell l' = γ}) := fun γ _ =>
        hG.inter (hcellm γ)
      have hsum : ∑ γ ∈ F, ν (G ∩ {l' | cell l' = γ}) ≤ ν (G ∩ {l' | |k l' - k l| ≤ w + V}) := by
        rw [← measure_biUnion_finset hdisj hmeas]
        exact measure_mono hunion
      have hlow : (F.card : ENNReal) * ENNReal.ofReal f ≤ ∑ γ ∈ F, ν (G ∩ {l' | cell l' = γ}) := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_le_sum
        intro γ hγ
        obtain ⟨l₀, ⟨hl₀G, -⟩, hl₀c⟩ := hF hγ
        rw [← hl₀c]
        exact hfloor l₀ hl₀G
      have hlt := hcon (k l)
      have : (F.card : ENNReal) * ENNReal.ofReal f < ENNReal.ofReal m :=
        (hlow.trans hsum).trans_lt hlt
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at this
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp this)
    have hTfin : T.Finite := by
      by_contra hinf
      obtain ⟨F, hFT, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊m / f⌋₊ + 1)
      have := hfinite F hFT
      rw [hFcard] at this
      push_cast at this
      have h1 : m / f < (⌊m / f⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊m / f⌋₊ : ℝ) + 1) * f ≤ m := this
      have h3 : m / f * f = m := div_mul_cancel₀ m hf.ne'
      nlinarith
    refine ⟨insert none (hTfin.toFinset.image some), ?_, ?_⟩
    · have hcardT : (hTfin.toFinset.card : ℝ) * f ≤ m :=
        hfinite hTfin.toFinset (by simp)
      have hcardT' : hTfin.toFinset.card ≤ ⌊m / f⌋₊ := by
        apply Nat.le_floor
        rw [le_div_iff₀ hf]; exact hcardT
      calc (insert none (hTfin.toFinset.image some)).card
          ≤ (hTfin.toFinset.image some).card + 1 := Finset.card_insert_le _ _
        _ ≤ hTfin.toFinset.card + 1 := by
            gcongr; exact Finset.card_image_le
        _ ≤ Nc := by rw [hNc]; omega
    · intro l' hl'
      by_cases hl'G : l' ∈ G
      · have : cellOf G cell l' = some (cell l') := by simp [cellOf, hl'G]
        rw [this]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨cell l', hTfin.mem_toFinset.mpr ⟨l', ⟨hl'G, hl'⟩, rfl⟩, rfl⟩
      · have : cellOf G cell l' = none := by simp [cellOf, hl'G]
        rw [this]
        exact Finset.mem_insert_self _ _
  -- the cap for the cell map with the junk cell
  have hcap' : ∀ (u : ℝ) (γ : Option ι) (b : ℤ),
      ν {l | (l, u) ∈ E ∧ cellOf G cell l = γ ∧ ⌊L l u / p⌋ = b} ≤ ENNReal.ofReal C₂ := by
    intro u γ b
    cases γ with
    | none =>
      have : {l | (l, u) ∈ E ∧ cellOf G cell l = none ∧ ⌊L l u / p⌋ = b} = ∅ := by
        ext l
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hl hc
        have hlG := hEG _ hl
        simp [cellOf, hlG] at hc
      rw [this, measure_empty]; exact bot_le
    | some γ =>
      refine le_trans (measure_mono ?_) (hcap u γ b)
      intro l ⟨hl, hc, hb⟩
      have hlG := hEG _ hl
      simp only [cellOf, hlG, if_true, Option.some.injEq] at hc
      exact ⟨hl, hc, hb⟩
  have hineq := slope_concentration_ineq ν hE hE01 hk hL (cellOf G cell) hp hw Nc hmodel hcount
    hcap' hcells
  -- compare with the budget
  set Mm := (ν.prod volume) E with hMm
  have hMfin : Mm ≠ ⊤ := by
    have : (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0:ℝ) 1) :=
      measure_mono (fun q hq => ⟨trivial, hE01 q hq⟩)
    rw [Measure.prod_prod, Real.volume_Icc] at this
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top ν univ) ENNReal.ofReal_ne_top)
      this
  set M := Mm.toReal with hM
  have hMeq : Mm = ENNReal.ofReal M := (ENNReal.ofReal_toReal hMfin).symm
  have hM0 : M₀ ≤ M := by
    rw [hMeq] at hmass
    exact (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).mp hmass
  have hNcR : (Nc : ℝ) ≤ m / f + 2 := by
    rw [hNc]; push_cast
    have := Nat.floor_le (div_nonneg hm hf.le)
    linarith
  have hfirst : ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ * Nc * Mm) ≤ ENNReal.ofReal (M ^ 2 / 2) := by
    rw [hMeq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul
      (by positivity), ← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hM0' : 0 ≤ M := ENNReal.toReal_nonneg
    calc C₁ * (C₂ * Nc * M) = C₁ * C₂ * Nc * M := by ring
      _ ≤ C₁ * C₂ * (m / f + 2) * M := by
          gcongr
      _ ≤ M₀ / 2 * M := by gcongr
      _ ≤ M / 2 * M := by gcongr
      _ = M ^ 2 / 2 := by ring
  have hsecond : ENNReal.ofReal C₁ * (ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2) <
      ENNReal.ofReal (M ^ 2 / 2) := by
    refine hfar.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have : M₀ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₀.le hM0 2
    linarith
  have htotal : Mm ^ 2 < ENNReal.ofReal (M ^ 2 / 2) + ENNReal.ofReal (M ^ 2 / 2) := by
    calc Mm ^ 2 ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ * Nc * Mm +
          ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2) := hineq
      _ = ENNReal.ofReal C₁ * (ENNReal.ofReal C₂ * Nc * Mm) +
          ENNReal.ofReal C₁ * (ENNReal.ofReal (2 * (p + 2 * e) / w) * ν univ ^ 2) := mul_add _ _ _
      _ < ENNReal.ofReal (M ^ 2 / 2) + ENNReal.ofReal (M ^ 2 / 2) :=
          ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfirst) hfirst hsecond
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), hMeq, ← ENNReal.ofReal_pow
    ENNReal.toReal_nonneg] at htotal
  have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp htotal
  linarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
