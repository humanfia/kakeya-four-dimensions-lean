import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Labels

/-!
# Labels keep half of their incidences in the good set

For a label of level `d` and a time of its block, a line of the label is good at that time
unless, at some deeper level `d'' ≥ d`, its relative position in its cell falls into the margin
of relative size `3β + 2/r` (`FailF`). Periodicity of the relative position bounds each margin
by `3 (3β + 2/r)` times the label's mass, which with `30 (D+1) ≤ 2^B` leaves at least half of
the label's mass good (`good_floor`). Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

namespace Synth

variable (S : Synth)

/-- Dyadic blocks nest. -/
theorem floor_two_pow_anc (A B' : ℕ) (hAB : A ≤ B') {t : ℝ} (ht : 0 ≤ t) :
    ⌊t * 2 ^ A⌋₊ = ⌊t * 2 ^ B'⌋₊ / 2 ^ (B' - A) := by
  have e : t * 2 ^ A = t * 2 ^ B' / ((2 ^ (B' - A) : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ B' = 2 ^ A * 2 ^ (B' - A) := by
      rw [← pow_add, Nat.add_sub_cancel' hAB]
    rw [Nat.cast_pow, Nat.cast_ofNat, h2]
    field_simp
  rw [e, Nat.floor_div_natCast]

theorem blk_anc {a b : ℕ} (hab : a ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    S.blk a t = S.blk b t / 2 ^ (S.T b - S.T a) :=
  floor_two_pow_anc _ _ (S.T_mono hab) ht

theorem blk_eq_of_mem {d : ℕ} {t : ℝ} {j : ℕ}
    (ht : t ∈ Ico ((j : ℝ) / 2 ^ S.T d) (((j : ℝ) + 1) / 2 ^ S.T d)) : S.blk d t = j := by
  unfold blk
  have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
  rw [Nat.floor_eq_iff (by have : (0 : ℝ) ≤ j / 2 ^ S.T d := by positivity
                           nlinarith [ht.1])]
  constructor
  · have := ht.1; rw [div_le_iff₀ hp] at this; exact this
  · have := ht.2; rw [lt_div_iff₀ hp] at this; exact this

/-- The block start moves forward by less than one coarse mesh. -/
theorem τ_succ_sub (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ S.τ (d + 1) t - S.τ d t ∧ S.τ (d + 1) t - S.τ d t < S.q d := by
  have hab := S.blk_anc (Nat.le_succ d) ht
  set R := 2 ^ (S.T (d + 1) - S.T d) with hR
  have hRpos : 0 < R := by positivity
  have hTd := S.hT d
  have e2 : (2 : ℝ) ^ S.T (d + 1) = 2 ^ S.T d * R := by
    rw [hR, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, Nat.add_sub_cancel' (by omega)]
  unfold τ
  rw [hab]
  set b := S.blk (d + 1) t
  have h1 : ((b / R : ℕ) : ℝ) * R ≤ b := by exact_mod_cast Nat.div_mul_le_self b R
  have h2 : (b : ℝ) < ((b / R : ℕ) : ℝ) * R + R := by
    have := Nat.lt_div_mul_add (a := b) hRpos
    exact_mod_cast this
  have hpk : (0 : ℝ) < 2 ^ S.T d := by positivity
  have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hd : (b : ℝ) / 2 ^ S.T (d + 1) - ((b / R : ℕ) : ℝ) / 2 ^ S.T d =
      ((b : ℝ) - ((b / R : ℕ) : ℝ) * R) / (2 ^ S.T d * R) := by
    rw [e2]; field_simp
  rw [hd]
  constructor
  · apply div_nonneg (by linarith); positivity
  · rw [div_lt_iff₀ (by positivity)]
    unfold Grid.q
    field_simp
    linarith

/-- The margin event of level `d''`. -/
def FailF (d'' : ℕ) (p : Ω × ℝ) : Prop :=
  Int.fract ((S.X d'' p - S.β) / S.q d'') < S.β + 1 / S.r d'' ∨
    1 - 2 * S.β - 1 / S.r d'' ≤ Int.fract ((S.X d'' p - S.β) / S.q d'')

/-- Offset of a point in its cell. -/
theorem sub_cpos_cellOf (d : ℕ) {x : ℝ} (hx : S.β ≤ x) :
    x - S.cpos d (S.cellOf d x) = S.q d * Int.fract ((x - S.β) / S.q d) := by
  unfold Grid.cpos Grid.cellOf
  have hq := S.q_pos d
  have h0 : 0 ≤ (x - S.β) / S.q d := div_nonneg (by linarith) hq.le
  rw [Int.fract, ← Int.natCast_floor_eq_floor h0]
  push_cast
  field_simp
  ring

/-- **Levels at or above the label.** -/
theorem levels_le (d : ℕ) (L : S.Label d) {ω : Ω} (hω : emb ω ∈ S.sA d L) {t : ℝ}
    (ht : 0 ≤ t) (htb : S.blk d t = L.1) (d' : ℕ) (hd' : d' ≤ d) :
    S.β ≤ S.X d' (ω, t) ∧ S.valid d' (S.cellOf d' (S.X d' (ω, t))) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = d' + k := ⟨d - d', by omega⟩
  obtain ⟨hx, hu3, -, -, -, -⟩ := hω
  simp only [emb_snd0, emb_snd3] at hx hu3
  have hw0 : 0 ≤ S.β * ω.2.1.2 := mul_nonneg S.β_pos.le hu3.1
  have hw : S.β * ω.2.1.2 ≤ S.β := by have := S.β_pos; nlinarith [hu3.2]
  have hpos := S.pos_anc d' k L.1 L.2.1.1 L.2.1.2 ω.2.1.1 (S.β * ω.2.1.2) hw0 hw hx
  have hτ : S.τ d' t = ((L.1 / 2 ^ (S.T (d' + k) - S.T d') : ℕ) : ℝ) / 2 ^ S.T d' := by
    unfold τ
    rw [S.blk_anc (show d' ≤ d' + k by omega) ht, htb]
  have hX : S.X d' (ω, t) = ω.2.1.1 +
      ((L.1 / 2 ^ (S.T (d' + k) - S.T d') : ℕ) : ℝ) / 2 ^ S.T d' * (S.β * ω.2.1.2) := by
    unfold X; rw [hτ]
  rw [hX]
  have hv := S.valid_anc d' k _ L.2.1.2
  have hcell := S.cellOf_eq d' _ hpos
  rw [hcell]
  exact ⟨(S.valid_bounds d' _ hv).1.trans hpos.1, hv⟩

/-- **Levels below the label.** -/
theorem levels_gt (d : ℕ) {ω : Ω} {t : ℝ} (ht : 0 ≤ t) (hu3 : ω.2.1.2 ∈ Icc (0 : ℝ) 1)
    (h0 : S.β ≤ S.X d (ω, t) ∧ S.valid d (S.cellOf d (S.X d (ω, t)))) (k : ℕ)
    (hnf : ∀ d'', d ≤ d'' → d'' < d + k → ¬ S.FailF d'' (ω, t)) :
    S.β ≤ S.X (d + k) (ω, t) ∧ S.valid (d + k) (S.cellOf (d + k) (S.X (d + k) (ω, t))) := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    obtain ⟨hβ, hv⟩ := ih (fun d'' h1 h2 => hnf d'' h1 (by omega))
    rw [show d + (k + 1) = d + k + 1 by ring]
    set x := S.X (d + k) (ω, t)
    set c := S.cellOf (d + k) x
    have hmem := S.mem_cellOf (d + k) hβ
    have hτ := S.τ_succ_sub (d + k) ht
    set s := (S.τ (d + k + 1) t - S.τ (d + k) t) * (S.β * ω.2.1.2) with hs
    have hβp := S.β_pos
    have hs0 : 0 ≤ s := mul_nonneg hτ.1 (mul_nonneg hβp.le hu3.1)
    have hs1 : s < S.β * S.q (d + k) := by
      have h1 : S.β * ω.2.1.2 ≤ S.β := by nlinarith [hu3.2]
      calc s ≤ (S.τ (d + k + 1) t - S.τ (d + k) t) * S.β := by
            rw [hs]; exact mul_le_mul_of_nonneg_left h1 hτ.1
        _ < S.q (d + k) * S.β := by nlinarith [hτ.2]
        _ = S.β * S.q (d + k) := by ring
    have hX : S.X (d + k + 1) (ω, t) = x + s := by
      simp only [x, hs, X]; ring
    have hnot := hnf (d + k) (by omega) (by omega)
    simp only [FailF, not_or, not_lt, not_le] at hnot
    have hoff := S.sub_cpos_cellOf (d + k) hβ
    have hq := S.q_pos (d + k)
    have hf1 : (S.β + 1 / S.r (d + k)) * S.q (d + k) ≤ x - S.cpos (d + k) c := by
      rw [hoff]; nlinarith [hnot.1]
    have hf2 : x - S.cpos (d + k) c < (1 - 2 * S.β - 1 / S.r (d + k)) * S.q (d + k) := by
      rw [hoff]; nlinarith [hnot.2]
    have hst := S.step (d + k) c hv hmem hs0 hs1 hf1 hf2
    rw [hX]
    exact ⟨(S.valid_bounds _ _ hst.1).1.trans hst.2.1, hst.1⟩

/-- A line of a label, at a time of its block, is good unless it hits a deeper margin. -/
theorem good_of_sA (d : ℕ) (L : S.Label d) {ω : Ω} (hω : emb ω ∈ S.sA d L)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (htb : S.blk d t = L.1)
    (hnf : ∀ d'', d ≤ d'' → d'' < S.D → ¬ S.FailF d'' (ω, t)) : (ω, t) ∈ S.Good := by
  have hω' := hω
  obtain ⟨-, hu3, hb1, hu2, hi, -⟩ := hω'
  simp only [emb_snd3, emb_snd2, emb_fst] at hu3 hu2 hi
  have hUp : (0 : ℝ) < 2 ^ S.Ux d := by positivity
  have hb1' : ω.2.2 ∈ Ico (0 : ℝ) 1 := by
    simp only [emb_snd1] at hb1
    have hi2 := L.2.2.1.2
    refine ⟨le_trans (by positivity) hb1.1, lt_of_lt_of_le hb1.2 ?_⟩
    rw [div_le_one hUp]
    have : (L.2.2.1 : ℕ) + 1 ≤ 2 ^ S.Ux d := hi2
    exact_mod_cast this
  refine ⟨ht, hi, hu2, hu3, hb1', fun d' hd' => ?_⟩
  by_cases hle : d' ≤ d
  · exact S.levels_le d L hω ht.1 htb d' hle
  · obtain ⟨k, rfl⟩ : ∃ k, d' = d + k := ⟨d' - d, by omega⟩
    exact S.levels_gt d ht.1 hu3 (S.levels_le d L hω ht.1 htb d le_rfl) k
      (fun d'' h1 h2 => hnf d'' h1 (by omega))

/-- The sample sets of a label. -/
def Aidx (d : ℕ) (L : S.Label d) : Set (ℕ × ℝ) :=
  {p | p.1 < S.M ∧ pre S.e₁ S.G (S.Gh d) p.1 = (L.2.2.2 : ℕ) ∧ p.2 ∈ Icc (0 : ℝ) 1}

def Apos (d : ℕ) (L : S.Label d) : Set (ℝ × ℝ) :=
  {p | p.1 + ((L.1 : ℕ) : ℝ) / 2 ^ S.T d * S.β * p.2 ∈
      Ico (S.cpos d L.2.1.1) (S.cpos d L.2.1.1 + S.q d) ∧ p.2 ∈ Icc (0 : ℝ) 1}

def Ax2 (d : ℕ) (L : S.Label d) : Set ℝ :=
  Ico (((L.2.2.1 : ℕ) : ℝ) / 2 ^ S.Ux d) ((((L.2.2.1 : ℕ) : ℝ) + 1) / 2 ^ S.Ux d)

theorem emb_preimage_sA (d : ℕ) (L : S.Label d) :
    emb ⁻¹' S.sA d L = S.Aidx d L ×ˢ (S.Apos d L ×ˢ S.Ax2 d L) := by
  ext ω
  simp only [mem_preimage, Synth.sA, Aidx, Apos, Ax2, mem_prod, mem_ofPred_eq, emb_fst,
    emb_snd0, emb_snd1, emb_snd2, emb_snd3]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨h5, h6, h4⟩, ⟨by rw [← mul_assoc] at h1; exact h1, h2⟩, h3⟩
  · rintro ⟨⟨h5, h6, h4⟩, ⟨h1, h2⟩, h3⟩
    exact ⟨by rw [← mul_assoc]; exact h1, h2, h3, h4, h5, h6⟩

theorem UU_Apos (d : ℕ) (hd : d ≤ S.D) (L : S.Label d) :
    (U.prod U) (S.Apos d L) = ENNReal.ofReal (S.q d) := by
  have hb := S.valid_bounds d _ L.2.1.2
  have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
  have hτ0 : (0 : ℝ) ≤ ((L.1 : ℕ) : ℝ) / 2 ^ S.T d := by positivity
  have hτ1 : ((L.1 : ℕ) : ℝ) / 2 ^ S.T d ≤ 1 := by
    rw [div_le_one hp]; exact_mod_cast L.1.2.le
  exact UU_shear_eq _ S.β (S.cpos d L.2.1.1) (S.q d) hτ0 hτ1 S.β_pos.le hb.1 hb.2

theorem P_sA (d : ℕ) (hd : d ≤ S.D) (L : S.Label d) :
    P S.M (emb ⁻¹' S.sA d L) =
      ((idx S.M).prod U) (S.Aidx d L) * (ENNReal.ofReal (S.q d) * U (S.Ax2 d L)) := by
  rw [S.emb_preimage_sA, P_prod_prod, S.UU_Apos d hd]

/-- The margin mass inside a label. -/
theorem P_fail_le (d d'' : ℕ) (hd : d ≤ d'') (L : S.Label d) (t : ℝ) :
    P S.M {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} ≤
      ((idx S.M).prod U) (S.Aidx d L) *
        (ENNReal.ofReal (3 * (3 * S.β + 2 / S.r d'') * S.q d) * U (S.Ax2 d L)) := by
  set τ'' := S.τ d'' t
  set x₁ := S.β + 1 / S.r d''
  set x₂ := 2 * S.β + 1 / S.r d''
  set Af : Set (ℝ × ℝ) := {p | p ∈ S.Apos d L ∧ (Int.fract ((p.1 + τ'' * (S.β * p.2) - S.β) /
      S.q d'') < x₁ ∨ 1 - x₂ ≤ Int.fract ((p.1 + τ'' * (S.β * p.2) - S.β) / S.q d''))}
  have hsub : {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} ⊆
      S.Aidx d L ×ˢ (Af ×ˢ S.Ax2 d L) := by
    intro ω hω
    obtain ⟨hA, hF⟩ := hω
    rw [← mem_preimage, S.emb_preimage_sA] at hA
    obtain ⟨h1, h2, h3⟩ := hA
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    unfold FailF X at hF
    rcases hF with h | h
    · left; exact h
    · right; simp only [x₂]; linarith
  have hr := S.r_pos d''
  have hr' : (0 : ℝ) < S.r d'' := by exact_mod_cast hr
  have hβ := S.β_pos
  have hx₁ : 0 ≤ x₁ := by positivity
  have hx₂ : 0 ≤ x₂ := by positivity
  have hmono : S.T d ≤ S.T d'' := S.T_mono hd
  set N := 2 ^ (S.T d'' - S.T d) with hN
  have hqN : S.q d = N * S.q d'' := by
    unfold Grid.q
    rw [hN]
    push_cast
    have : (2 : ℝ) ^ S.T d'' = 2 ^ S.T d * 2 ^ (S.T d'' - S.T d) := by
      rw [← pow_add, Nat.add_sub_cancel' hmono]
    rw [this]; field_simp
  have hq'' := S.q_pos d''
  have hqle : S.q d'' ≤ S.q d := by
    rw [hqN]
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_two_pow
    nlinarith
  have hAf : (U.prod U) Af ≤ ENNReal.ofReal ((N + 2) * ((x₁ + x₂) * S.q d'')) := by
    have hAfm : MeasurableSet Af := by
      apply MeasurableSet.inter
      · exact ((measurable_fst.add (((measurable_const_mul _).comp measurable_snd)))
          measurableSet_Ico).inter (measurable_snd measurableSet_Icc)
      · apply MeasurableSet.union
        · have hm : Measurable (fun p : ℝ × ℝ => (p.1 + τ'' * (S.β * p.2) - S.β) / S.q d'') := by
            fun_prop
          exact measurableSet_lt (measurable_fract.comp hm) measurable_const
        · have hm : Measurable (fun p : ℝ × ℝ => (p.1 + τ'' * (S.β * p.2) - S.β) / S.q d'') := by
            fun_prop
          exact measurableSet_le measurable_const (measurable_fract.comp hm)
    calc (U.prod U) Af ≤ ENNReal.ofReal ((N + 2) * ((x₁ + x₂) * S.q d'')) * U (Icc 0 1) := by
          refine UU_apply_le Af hAfm _ (Icc 0 1) ?_ ?_ measurableSet_Icc
          · intro u hu
            set a := S.cpos d L.2.1.1 - ((L.1 : ℕ) : ℝ) / 2 ^ S.T d * S.β * u
            have hsec : {b | (b, u) ∈ Af} ⊆ {b ∈ Ico a (a + N * S.q d'') |
                Int.fract ((b + (τ'' * (S.β * u) - S.β)) / S.q d'') < x₁ ∨
                1 - x₂ ≤ Int.fract ((b + (τ'' * (S.β * u) - S.β)) / S.q d'')} := by
              intro b hb
              obtain ⟨⟨h1, -⟩, h2⟩ := hb
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · simp only [a]; linarith [h1.1]
              · simp only [a]; rw [← hqN]; linarith [h1.2]
              · convert h2 using 3 <;> ring
            calc U {b | (b, u) ∈ Af} ≤ volume {b | (b, u) ∈ Af} := U_le_volume _
              _ ≤ _ := measure_mono hsec
              _ ≤ _ := vol_fract_bad_le _ _ a hq'' N x₁ x₂ hx₁ hx₂
          · intro u hu
            ext b
            simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
            intro hb
            exact hu hb.1.2
      _ = ENNReal.ofReal ((N + 2) * ((x₁ + x₂) * S.q d'')) := by simp [U]
  calc P S.M {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)}
      ≤ ((idx S.M).prod U) (S.Aidx d L) * ((U.prod U) Af * U (S.Ax2 d L)) :=
        P_mono_prod S.M hsub
    _ ≤ ((idx S.M).prod U) (S.Aidx d L) *
        (ENNReal.ofReal (3 * (3 * S.β + 2 / S.r d'') * S.q d) * U (S.Ax2 d L)) := by
        gcongr
        refine hAf.trans (ENNReal.ofReal_le_ofReal ?_)
        have : (N + 2 : ℝ) * S.q d'' ≤ 3 * S.q d := by rw [hqN]; nlinarith
        have hx : x₁ + x₂ = 3 * S.β + 2 / S.r d'' := by simp only [x₁, x₂]; ring
        rw [hx]
        have : 0 ≤ 3 * S.β + 2 / (S.r d'' : ℝ) := by positivity
        nlinarith

/-- `1 / r ≤ β`. -/
theorem inv_r_le (d : ℕ) : 1 / (S.r d : ℝ) ≤ S.β := by
  unfold Grid.r Grid.β
  have h := S.hT d
  rw [one_div_le_one_div (by positivity) (by positivity)]
  push_cast
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **Good floor.** At a time of its block, a label keeps at least half of its mass good. -/
theorem good_floor (hBD : 30 * (S.D + 1) ≤ 2 ^ S.B) (d : ℕ) (hd : d ≤ S.D) (L : S.Label d)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (htb : S.blk d t = L.1) :
    (1 / 2 : ENNReal) * P S.M (emb ⁻¹' S.sA d L) ≤
      P S.M {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} := by
  set Pa := P S.M (emb ⁻¹' S.sA d L)
  set I := ((idx S.M).prod U) (S.Aidx d L)
  set X2 := U (S.Ax2 d L)
  have hcover : emb ⁻¹' S.sA d L ⊆ {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} ∪
      ⋃ d'' ∈ Finset.Ico d S.D, {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} := by
    intro ω hω
    by_cases hf : ∃ d'', d ≤ d'' ∧ d'' < S.D ∧ S.FailF d'' (ω, t)
    · obtain ⟨d'', h1, h2, h3⟩ := hf
      right
      simp only [mem_iUnion, Finset.mem_Ico, exists_prop]
      exact ⟨d'', ⟨h1, h2⟩, hω, h3⟩
    · left
      push Not at hf
      exact ⟨S.good_of_sA d L hω ht htb (fun d'' h1 h2 => hf d'' h1 h2), hω⟩
  have hβ := S.β_pos
  have hfail : ∀ d'' ∈ Finset.Ico d S.D,
      P S.M {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} ≤ ENNReal.ofReal (15 * S.β) * Pa := by
    intro d'' hd''
    rw [Finset.mem_Ico] at hd''
    refine (S.P_fail_le d d'' hd''.1 L t).trans ?_
    rw [show Pa = I * (ENNReal.ofReal (S.q d) * X2) from S.P_sA d hd L]
    have hr := S.inv_r_le d''
    have hq := S.q_pos d
    have : 3 * (3 * S.β + 2 / (S.r d'' : ℝ)) * S.q d ≤ 15 * S.β * S.q d := by
      have : 2 / (S.r d'' : ℝ) ≤ 2 * S.β := by
        rw [div_eq_mul_one_div]; linarith
      nlinarith
    calc I * (ENNReal.ofReal (3 * (3 * S.β + 2 / S.r d'') * S.q d) * X2)
        ≤ I * (ENNReal.ofReal (15 * S.β * S.q d) * X2) := by
          gcongr
      _ = ENNReal.ofReal (15 * S.β) * (I * (ENNReal.ofReal (S.q d) * X2)) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
  have hsum : ∑ d'' ∈ Finset.Ico d S.D, P S.M {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} ≤
      (1 / 2 : ENNReal) * Pa := by
    calc _ ≤ ∑ _d'' ∈ Finset.Ico d S.D, ENNReal.ofReal (15 * S.β) * Pa :=
          Finset.sum_le_sum hfail
      _ = (Finset.Ico d S.D).card * (ENNReal.ofReal (15 * S.β) * Pa) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.D : ENNReal) * (ENNReal.ofReal (15 * S.β) * Pa) := by
          gcongr; simp
      _ ≤ (1 / 2 : ENNReal) * Pa := by
          rw [← mul_assoc]
          gcongr
          have hB : (30 : ℝ) * (S.D + 1) ≤ 2 ^ S.B := by exact_mod_cast hBD
          have hβe : S.β = 1 / 2 ^ S.B := rfl
          have : (S.D : ℝ) * (15 * S.β) ≤ 1 / 2 := by
            rw [hβe]
            rw [mul_one_div, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
          calc (S.D : ENNReal) * ENNReal.ofReal (15 * S.β)
              = ENNReal.ofReal (S.D * (15 * S.β)) := by
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal this
            _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hPa : Pa ≠ ⊤ := by
    have := P_isProb S.M (by unfold M; positivity)
    exact measure_ne_top _ _
  have h1 : Pa ≤ P S.M {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} + (1 / 2 : ENNReal) * Pa := by
    calc Pa ≤ P S.M ({ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} ∪
          ⋃ d'' ∈ Finset.Ico d S.D, {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)}) :=
          measure_mono hcover
      _ ≤ P S.M {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} +
          P S.M (⋃ d'' ∈ Finset.Ico d S.D, {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)}) :=
          measure_union_le _ _
      _ ≤ P S.M {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} +
          ∑ d'' ∈ Finset.Ico d S.D, P S.M {ω | emb ω ∈ S.sA d L ∧ S.FailF d'' (ω, t)} := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ _ := by gcongr
  have hhalf : Pa = (1 / 2 : ENNReal) * Pa + (1 / 2 : ENNReal) * Pa := by
    rw [← add_mul, ENNReal.add_halves, one_mul]
  have hfin : (1 / 2 : ENNReal) * Pa ≠ ⊤ := ENNReal.mul_ne_top (by simp) hPa
  have h2 : (1 / 2 : ENNReal) * Pa + (1 / 2 : ENNReal) * Pa ≤
      P S.M {ω | (ω, t) ∈ S.Good ∧ emb ω ∈ S.sA d L} + (1 / 2 : ENNReal) * Pa := by
    calc (1 / 2 : ENNReal) * Pa + (1 / 2 : ENNReal) * Pa = Pa := hhalf.symm
      _ ≤ _ := h1
  exact (ENNReal.add_le_add_iff_right hfin).mp h2

end Synth

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
