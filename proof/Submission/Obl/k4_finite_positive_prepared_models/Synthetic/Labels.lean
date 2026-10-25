import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Chain
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Hidden
import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.Slope

/-!
# The true labels of the synthetic model

A label of level `d` is a dyadic time block, a valid position cell (position of the line at the
left end of the block), a dyadic transverse cell and a hidden prefix. Labels of one block are
disjoint, labels nest across levels (`sA_anc`), and every good incidence lies in a label of every
level (`good_cover`). Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

open MeasureTheory Set

noncomputable section

/-- The data of the synthetic model. -/
structure Synth extends Grid where
  Ux : ℕ → ℕ
  hUx : ∀ d, Ux d ≤ Ux (d + 1)
  e : ℕ
  e₁ : ℕ
  he : e₁ ≤ e
  G : ℕ
  Gh : ℕ → ℕ
  hGh : ∀ d, Gh d ≤ Gh (d + 1)
  hGhG : ∀ d ≤ D, Gh d ≤ G

namespace Synth

variable (S : Synth)

/-- The number of hidden indices. -/
def M : ℕ := 2 ^ (S.e₁ * S.G)

/-- The block of a time at level `d`. -/
def blk (d : ℕ) (t : ℝ) : ℕ := ⌊t * 2 ^ S.T d⌋₊

/-- The left end of the block of a time. -/
def τ (d : ℕ) (t : ℝ) : ℝ := (S.blk d t : ℝ) / 2 ^ S.T d

/-- The position of a sample at the left end of the level-`d` block of time `t`. -/
def X (d : ℕ) (p : Ω × ℝ) : ℝ := p.1.2.1.1 + S.τ d p.2 * (S.β * p.1.2.1.2)

/-- Good incidences: every level sees a valid cell. -/
def Good : Set (Ω × ℝ) :=
  {p | p.2 ∈ Ico (0 : ℝ) 1 ∧ p.1.1.1 < S.M ∧ p.1.1.2 ∈ Icc (0 : ℝ) 1 ∧
    p.1.2.1.2 ∈ Icc (0 : ℝ) 1 ∧ p.1.2.2 ∈ Ico (0 : ℝ) 1 ∧
    ∀ d ≤ S.D, S.β ≤ S.X d p ∧ S.valid d (S.cellOf d (S.X d p))}

/-- The labels of level `d`. -/
abbrev Label (d : ℕ) :=
  Fin (2 ^ S.T d) × {c : Fin (2 ^ S.T d) // S.valid d c} × Fin (2 ^ S.Ux d) ×
    Fin (2 ^ (S.e₁ * S.Gh d))

/-- The lines of a label. -/
def sA (d : ℕ) (L : S.Label d) : Set (ℕ × (Fin 6 → ℝ)) :=
  {l | l.2 0 + ((L.1 : ℕ) : ℝ) / 2 ^ S.T d * (S.β * l.2 3) ∈
      Ico (S.cpos d L.2.1.1) (S.cpos d L.2.1.1 + S.q d) ∧
    l.2 3 ∈ Icc (0 : ℝ) 1 ∧
    l.2 1 ∈ Ico (((L.2.2.1 : ℕ) : ℝ) / 2 ^ S.Ux d) ((((L.2.2.1 : ℕ) : ℝ) + 1) / 2 ^ S.Ux d) ∧
    l.2 2 ∈ Icc (0 : ℝ) 1 ∧ l.1 < S.M ∧ pre S.e₁ S.G (S.Gh d) l.1 = (L.2.2.2 : ℕ)}

/-- The time block of a label. -/
def blockI (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

theorem blk_lt (d : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : S.blk d t < 2 ^ S.T d := by
  unfold blk
  have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
  have h1 : t * 2 ^ S.T d < 2 ^ S.T d := by nlinarith [ht.2]
  rw [Nat.floor_lt (by nlinarith [ht.1])]
  exact_mod_cast h1

theorem mem_blockI (d : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    t ∈ blockI (S.T d) ⟨S.blk d t, S.blk_lt d ht⟩ := by
  unfold blockI blk
  have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
  have h0 : 0 ≤ t * 2 ^ S.T d := by nlinarith [ht.1]
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (t * 2 ^ S.T d)
  simp only [mem_Icc]
  constructor
  · rw [div_le_iff₀ hp]; exact h1
  · rw [le_div_iff₀ hp]; exact h2.le

theorem τ_le (d : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : 0 ≤ S.τ d t ∧ S.τ d t ≤ 1 := by
  unfold τ
  have hp : (0 : ℝ) < 2 ^ S.T d := by positivity
  have := S.blk_lt d ht
  constructor
  · positivity
  · rw [div_le_one hp]
    exact_mod_cast this.le

/-- **Coverage.** A good incidence lies in a label of every level. -/
theorem good_cover {p : Ω × ℝ} (hp : p ∈ S.Good) {d : ℕ} (hd : d ≤ S.D) :
    ∃ L : S.Label d, emb p.1 ∈ S.sA d L ∧ p.2 ∈ blockI (S.T d) L.1 := by
  obtain ⟨ht, hi, hu2, hu3, hb1, hall⟩ := hp
  obtain ⟨hβ, hv⟩ := hall d hd
  have hmem := S.mem_cellOf d hβ
  have hc : S.cellOf d (S.X d p) < 2 ^ S.T d := S.valid_lt d _ hv
  have hUp : (0 : ℝ) < 2 ^ S.Ux d := by positivity
  have hb10 : 0 ≤ p.1.2.2 * 2 ^ S.Ux d := by nlinarith [hb1.1]
  have hb1lt : ⌊p.1.2.2 * 2 ^ S.Ux d⌋₊ < 2 ^ S.Ux d := by
    rw [Nat.floor_lt hb10]
    have : p.1.2.2 * 2 ^ S.Ux d < 2 ^ S.Ux d := by nlinarith [hb1.2]
    exact_mod_cast this
  have hpre : pre S.e₁ S.G (S.Gh d) p.1.1.1 < 2 ^ (S.e₁ * S.Gh d) :=
    pre_lt (S.hGhG d hd) hi
  refine ⟨(⟨S.blk d p.2, S.blk_lt d ht⟩, ⟨⟨S.cellOf d (S.X d p), hc⟩, hv⟩,
    ⟨⌊p.1.2.2 * 2 ^ S.Ux d⌋₊, hb1lt⟩, ⟨pre S.e₁ S.G (S.Gh d) p.1.1.1, hpre⟩), ?_, ?_⟩
  · refine ⟨?_, hu3, ?_, hu2, hi, rfl⟩
    · exact hmem
    · simp only [emb_snd1, mem_Ico]
      have h1 := Nat.floor_le hb10
      have h2 := Nat.lt_floor_add_one (p.1.2.2 * 2 ^ S.Ux d)
      constructor
      · rw [div_le_iff₀ hUp]; exact h1
      · rw [lt_div_iff₀ hUp]; exact h2
  · exact S.mem_blockI d ht

theorem Ux_mono {d d' : ℕ} (h : d ≤ d') : S.Ux d ≤ S.Ux d' := by
  obtain ⟨k, rfl⟩ : ∃ k, d' = d + k := ⟨d' - d, by omega⟩
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [show d + (k + 1) = d + k + 1 by ring]; exact ih.trans (S.hUx _)

theorem Gh_mono {d d' : ℕ} (h : d ≤ d') : S.Gh d ≤ S.Gh d' := by
  obtain ⟨k, rfl⟩ : ∃ k, d' = d + k := ⟨d' - d, by omega⟩
  clear h
  induction k with
  | zero => simp
  | succ k ih => rw [show d + (k + 1) = d + k + 1 by ring]; exact ih.trans (S.hGh _)

/-- Dyadic coarsening of an interval index. -/
theorem dyadic_anc (a b j : ℕ) (hab : a ≤ b) {x : ℝ}
    (hx : (j : ℝ) / 2 ^ b ≤ x ∧ x < ((j : ℝ) + 1) / 2 ^ b) :
    ((j / 2 ^ (b - a) : ℕ) : ℝ) / 2 ^ a ≤ x ∧ x < (((j / 2 ^ (b - a) : ℕ) : ℝ) + 1) / 2 ^ a := by
  set R := 2 ^ (b - a) with hR
  have hRpos : 0 < R := by positivity
  have e : (2 : ℝ) ^ b = 2 ^ a * R := by
    rw [hR, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, Nat.add_sub_cancel' hab]
  have h1 : (j / R : ℕ) * R ≤ j := Nat.div_mul_le_self j R
  have h2 : j + 1 ≤ (j / R + 1) * R := by
    have := Nat.lt_div_mul_add (a := j) hRpos
    linarith
  have h1' : ((j / R : ℕ) : ℝ) * R ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) + 1 ≤ (((j / R : ℕ) : ℝ) + 1) * R := by exact_mod_cast h2
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
  rw [e] at hx
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · calc ((j / R : ℕ) : ℝ) / 2 ^ a = ((j / R : ℕ) : ℝ) * R / (2 ^ a * R) := by
          field_simp
      _ ≤ (j : ℝ) / (2 ^ a * R) := by gcongr
      _ ≤ x := hx1
  · calc x < ((j : ℝ) + 1) / (2 ^ a * R) := hx2
      _ ≤ (((j / R : ℕ) : ℝ) + 1) * R / (2 ^ a * R) := by gcongr
      _ = (((j / R : ℕ) : ℝ) + 1) / 2 ^ a := by field_simp

/-- Dyadic coarsening of a closed interval index. -/
theorem dyadic_anc_Icc (a b j : ℕ) (hab : a ≤ b) {x : ℝ}
    (hx : x ∈ Icc ((j : ℝ) / 2 ^ b) (((j : ℝ) + 1) / 2 ^ b)) :
    x ∈ Icc (((j / 2 ^ (b - a) : ℕ) : ℝ) / 2 ^ a) ((((j / 2 ^ (b - a) : ℕ) : ℝ) + 1) / 2 ^ a) := by
  set R := 2 ^ (b - a) with hR
  have hRpos : 0 < R := by positivity
  have e : (2 : ℝ) ^ b = 2 ^ a * R := by
    rw [hR, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, Nat.add_sub_cancel' hab]
  have h1 : (j / R : ℕ) * R ≤ j := Nat.div_mul_le_self j R
  have h2 : j + 1 ≤ (j / R + 1) * R := by
    have := Nat.lt_div_mul_add (a := j) hRpos
    linarith
  have h1' : ((j / R : ℕ) : ℝ) * R ≤ j := by exact_mod_cast h1
  have h2' : (j : ℝ) + 1 ≤ (((j / R : ℕ) : ℝ) + 1) * R := by exact_mod_cast h2
  have hpa : (0 : ℝ) < 2 ^ a := by positivity
  have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
  rw [e] at hx
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · calc ((j / R : ℕ) : ℝ) / 2 ^ a = ((j / R : ℕ) : ℝ) * R / (2 ^ a * R) := by
          field_simp
      _ ≤ (j : ℝ) / (2 ^ a * R) := by gcongr
      _ ≤ x := hx1
  · calc x ≤ ((j : ℝ) + 1) / (2 ^ a * R) := hx2
      _ ≤ (((j / R : ℕ) : ℝ) + 1) * R / (2 ^ a * R) := by gcongr
      _ = (((j / R : ℕ) : ℝ) + 1) / 2 ^ a := by field_simp

/-- The position of a line at the block of an ancestor label. -/
theorem pos_anc (d k j' c' : ℕ) (hv : S.valid (d + k) c') (b w : ℝ) (hw0 : 0 ≤ w)
    (hw : w ≤ S.β)
    (hx : S.cpos (d + k) c' ≤ b + (j' : ℝ) / 2 ^ S.T (d + k) * w ∧
      b + (j' : ℝ) / 2 ^ S.T (d + k) * w < S.cpos (d + k) c' + S.q (d + k)) :
    S.cpos d (c' / 2 ^ (S.T (d + k) - S.T d)) ≤
        b + ((j' / 2 ^ (S.T (d + k) - S.T d) : ℕ) : ℝ) / 2 ^ S.T d * w ∧
      b + ((j' / 2 ^ (S.T (d + k) - S.T d) : ℕ) : ℝ) / 2 ^ S.T d * w <
        S.cpos d (c' / 2 ^ (S.T (d + k) - S.T d)) + S.q d := by
  induction k generalizing j' c' with
  | zero => simpa using hx
  | succ k ih =>
    rw [show d + (k + 1) = d + k + 1 by ring] at hv hx ⊢
    set R := 2 ^ (S.T (d + k + 1) - S.T (d + k)) with hR
    have hTk := S.hT (d + k)
    have hRpos : 0 < R := by positivity
    have e2 : (2 : ℝ) ^ S.T (d + k + 1) = 2 ^ S.T (d + k) * R := by
      rw [hR, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, Nat.add_sub_cancel' (by omega)]
    -- the shift between the two block starts
    set sft := ((j' : ℝ) / 2 ^ S.T (d + k + 1) - ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k)) * w
      with hsft
    have hsft0 : 0 ≤ sft ∧ sft ≤ S.β * S.q (d + k) := by
      have hpk : (0 : ℝ) < 2 ^ S.T (d + k) := by positivity
      have hRr : (0 : ℝ) < R := by exact_mod_cast hRpos
      have h1 : ((j' / R : ℕ) : ℝ) * R ≤ j' := by exact_mod_cast Nat.div_mul_le_self j' R
      have h2 : (j' : ℝ) < ((j' / R : ℕ) : ℝ) * R + R := by
        have := Nat.lt_div_mul_add (a := j') hRpos
        exact_mod_cast this
      have hd : (j' : ℝ) / 2 ^ S.T (d + k + 1) - ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) =
          ((j' : ℝ) - ((j' / R : ℕ) : ℝ) * R) / (2 ^ S.T (d + k) * R) := by
        rw [e2]; field_simp
      have hd0 : 0 ≤ (j' : ℝ) / 2 ^ S.T (d + k + 1) - ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) := by
        rw [hd]; apply div_nonneg (by linarith); positivity
      have hd1 : (j' : ℝ) / 2 ^ S.T (d + k + 1) - ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) ≤
          S.q (d + k) := by
        rw [hd, div_le_iff₀ (by positivity)]
        unfold Grid.q
        field_simp
        linarith
      constructor
      · exact mul_nonneg hd0 hw0
      · calc sft ≤ S.q (d + k) * S.β := by rw [hsft]; exact mul_le_mul hd1 hw hw0 (S.q_pos _).le
          _ = S.β * S.q (d + k) := by ring
    have hpl := S.plateau (d + k) c' hv hx hsft0.1 hsft0.2
    have hrr : S.r (d + k) = R := rfl
    rw [hrr] at hpl
    have hx' : S.cpos (d + k) (c' / R) ≤ b + ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) * w ∧
        b + ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) * w < S.cpos (d + k) (c' / R) + S.q (d + k) := by
      have : b + (j' : ℝ) / 2 ^ S.T (d + k + 1) * w - sft =
          b + ((j' / R : ℕ) : ℝ) / 2 ^ S.T (d + k) * w := by rw [hsft]; ring
      rw [← this]; exact hpl
    have hv' : S.valid (d + k) (c' / R) := hv.2.2
    have := ih (j' / R) (c' / R) hv' hx'
    have hmono : S.T d ≤ S.T (d + k) := S.T_mono (by omega)
    have ediv : ∀ n : ℕ, n / R / 2 ^ (S.T (d + k) - S.T d) = n / 2 ^ (S.T (d + k + 1) - S.T d) := by
      intro n
      rw [Nat.div_div_eq_div_mul, hR, ← pow_add]
      congr 2
      omega
    rw [ediv, ediv] at this
    exact this

/-- The ancestor of a label. -/
def anc (d k : ℕ) (hk : d + k ≤ S.D) (L : S.Label (d + k)) : S.Label d :=
  (⟨(L.1 : ℕ) / 2 ^ (S.T (d + k) - S.T d), by
      have h1 := L.1.2
      have hm : S.T d ≤ S.T (d + k) := S.T_mono (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hm]
      exact h1⟩,
   ⟨⟨(L.2.1.1 : ℕ) / 2 ^ (S.T (d + k) - S.T d),
      S.valid_lt d _ (S.valid_anc d k _ L.2.1.2)⟩, S.valid_anc d k _ L.2.1.2⟩,
   ⟨(L.2.2.1 : ℕ) / 2 ^ (S.Ux (d + k) - S.Ux d), by
      have h1 := L.2.2.1.2
      have hm : S.Ux d ≤ S.Ux (d + k) := S.Ux_mono (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' hm]
      exact h1⟩,
   ⟨(L.2.2.2 : ℕ) / 2 ^ (S.e₁ * (S.Gh (d + k) - S.Gh d)), by
      have h1 := L.2.2.2.2
      have hm : S.Gh d ≤ S.Gh (d + k) := S.Gh_mono (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← mul_add,
        Nat.add_sub_cancel' hm]
      exact h1⟩)

/-- **Nesting.** A label's lines and block lie in its ancestor's. -/
theorem sA_anc (d k : ℕ) (hk : d + k ≤ S.D) (L : S.Label (d + k)) :
    S.sA (d + k) L ⊆ S.sA d (S.anc d k hk L) ∧
      blockI (S.T (d + k)) L.1 ⊆ blockI (S.T d) (S.anc d k hk L).1 := by
  constructor
  · intro l hl
    obtain ⟨hx, hu3, hb1, hu2, hi, hpre⟩ := hl
    refine ⟨?_, hu3, ?_, hu2, hi, ?_⟩
    · have hw0 : 0 ≤ S.β * l.2 3 := mul_nonneg S.β_pos.le hu3.1
      have hw : S.β * l.2 3 ≤ S.β := by
        have := S.β_pos; nlinarith [hu3.2]
      exact S.pos_anc d k L.1 L.2.1.1 L.2.1.2 (l.2 0) (S.β * l.2 3) hw0 hw hx
    · exact dyadic_anc (S.Ux d) (S.Ux (d + k)) L.2.2.1 (S.Ux_mono (by omega)) hb1
    · show pre S.e₁ S.G (S.Gh d) l.1 = (L.2.2.2 : ℕ) / 2 ^ (S.e₁ * (S.Gh (d + k) - S.Gh d))
      rw [← hpre]
      unfold pre
      have h1 : S.Gh d ≤ S.Gh (d + k) := S.Gh_mono (by omega)
      have h2 : S.Gh (d + k) ≤ S.G := S.hGhG _ hk
      rw [Nat.div_div_eq_div_mul, ← pow_add, ← mul_add]
      congr 3
      omega
  · intro t ht
    unfold blockI at ht ⊢
    have hm : S.T d ≤ S.T (d + k) := S.T_mono (by omega)
    exact dyadic_anc_Icc (S.T d) (S.T (d + k)) L.1 hm ht

/-- **Disjointness.** Distinct labels of one block have disjoint lines. -/
theorem sA_disjoint (d : ℕ) (L L' : S.Label d) (hne : L ≠ L') (hj : L.1 = L'.1) :
    Disjoint (S.sA d L) (S.sA d L') := by
  rw [Set.disjoint_left]
  intro l hl hl'
  obtain ⟨hx, -, hb1, -, -, hpre⟩ := hl
  obtain ⟨hx', -, hb1', -, -, hpre'⟩ := hl'
  rw [hj] at hx
  have hc : L.2.1.1 = L'.2.1.1 := by
    apply Fin.ext
    rw [← S.cellOf_eq d _ hx, ← S.cellOf_eq d _ hx']
  have hi2 : L.2.2.1 = L'.2.2.1 := by
    apply Fin.ext
    have hUp : (0 : ℝ) < 2 ^ S.Ux d := by positivity
    have e1 : ⌊l.2 1 * 2 ^ S.Ux d⌋₊ = (L.2.2.1 : ℕ) := by
      rw [Nat.floor_eq_iff (by nlinarith [hb1.1, (show (0:ℝ) ≤ ((L.2.2.1 : ℕ) : ℝ) / 2 ^ S.Ux d
        from by positivity)])]
      constructor
      · have := hb1.1; rw [div_le_iff₀ hUp] at this; linarith
      · have := hb1.2; rw [lt_div_iff₀ hUp] at this; linarith
    have e2 : ⌊l.2 1 * 2 ^ S.Ux d⌋₊ = (L'.2.2.1 : ℕ) := by
      rw [Nat.floor_eq_iff (by nlinarith [hb1'.1, (show (0:ℝ) ≤ ((L'.2.2.1 : ℕ) : ℝ) / 2 ^ S.Ux d
        from by positivity)])]
      constructor
      · have := hb1'.1; rw [div_le_iff₀ hUp] at this; linarith
      · have := hb1'.2; rw [lt_div_iff₀ hUp] at this; linarith
    rw [← e1, ← e2]
  have hh : L.2.2.2 = L'.2.2.2 := Fin.ext (hpre.symm.trans hpre')
  apply hne
  obtain ⟨j, ⟨c, hc1⟩, i2, h⟩ := L
  obtain ⟨j', ⟨c', hc1'⟩, i2', h'⟩ := L'
  simp only at hj hc hi2 hh
  subst hj hc hi2 hh
  rfl

end Synth

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
