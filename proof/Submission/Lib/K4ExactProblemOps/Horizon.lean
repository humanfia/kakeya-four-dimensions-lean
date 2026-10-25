import Submission.Lib.K4ExactProblemOps.Rescale

/-!
# Elementary horizon and narrowness facts

For the frozen true terminal systems `term`, the horizon `H` and the narrow terminal
systems `nt`: nonnegativity and monotonicity, `H ≤ h` from a system, `H ≤ L` from the
initial horizon bound, `nt h w ⟹ term (h + ρ)`, `term h ⟹ nt h 0` (from
`|det Q| 4^T ≤ κ² / 4`), and rescaling of `nt` under `N ↦ N ^ c`.
-/

noncomputable section

namespace Submission.Lib.K4ExactProblemOps

open MeasureTheory Filter

/-- The initial horizon bound, as a hypothesis of the frozen statements. -/
def InitialHorizonBound : Prop :=
  ∀ N K L d S η W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    ∀ h : ℝ, L < h → term N K L W ω ν E B f h

section

variable {N K : ℕ → ℝ} {L : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ} {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}

theorem term_nonneg (hN : ∀ k, 2 ≤ N k) {h : ℝ} (ht : term N K L W ω ν E B f h) : 0 ≤ h := by
  obtain ⟨M, D, hMD⟩ := ht
  obtain ⟨k, κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F, htime, -⟩ :=
    (hMD 1 (by norm_num)).exists
  by_contra hn
  have hlt : N k ^ h < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hN k]) (lt_of_not_ge hn)
  have hone : (1 : ℝ) ≤ 2 ^ T := one_le_pow₀ (by norm_num)
  linarith

theorem term_mono (hN : ∀ k, 1 ≤ N k) {h h' : ℝ} (ht : term N K L W ω ν E B f h)
    (hh : h ≤ h') : term N K L W ω ν E B f h' := by
  obtain ⟨M, D, hMD⟩ := ht
  refine ⟨M, D, fun ε hε => (hMD ε hε).mono fun k hk => ?_⟩
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F, htime, hrest⟩ := hk
  exact ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime.trans (Real.rpow_le_rpow_of_exponent_le (hN k) hh), hrest⟩

theorem term_bddBelow (hN : ∀ k, 2 ≤ N k) : BddBelow {h : ℝ | term N K L W ω ν E B f h} :=
  ⟨0, fun _ hh => term_nonneg hN hh⟩

theorem H_nonneg (hN : ∀ k, 2 ≤ N k) : 0 ≤ H N K L W ω ν E B f := by
  unfold H
  rcases Set.eq_empty_or_nonempty {h : ℝ | term N K L W ω ν E B f h} with he | hne
  · rw [he, Real.sInf_empty]
  · exact le_csInf hne fun _ hh => term_nonneg hN hh

theorem H_le_of_term (hN : ∀ k, 2 ≤ N k) {h : ℝ} (ht : term N K L W ω ν E B f h) :
    H N K L W ω ν E B f ≤ h :=
  csInf_le (term_bddBelow hN) ht

theorem not_term_of_lt_H (hN : ∀ k, 2 ≤ N k) {h : ℝ} (hh : h < H N K L W ω ν E B f) :
    ¬ term N K L W ω ν E B f h := fun ht => absurd (H_le_of_term hN ht) (not_le.2 hh)

theorem term_of_H_lt (hN : ∀ k, 2 ≤ N k) (hne : ∃ h, term N K L W ω ν E B f h) {h : ℝ}
    (hh : H N K L W ω ν E B f < h) : term N K L W ω ν E B f h := by
  obtain ⟨h₀, hh₀, hlt⟩ := exists_lt_of_csInf_lt hne hh
  exact term_mono (fun k => le_trans (by norm_num) (hN k)) hh₀ hlt.le

/-- Narrow terminal systems at horizon `h` are terminal systems at every larger horizon. -/
theorem term_of_nt (hN : ∀ k, 1 ≤ N k) {h w ρ : ℝ} (hnt : nt N K L W ω ν E B f h w)
    (hρ : 0 < ρ) : term N K L W ω ν E B f (h + ρ) := by
  obtain ⟨M, D, hMD⟩ := hnt
  refine ⟨M, D, fun ε hε => ?_⟩
  have he : 0 < min ε ρ := lt_min hε hρ
  apply (hMD (min ε ρ) he).mono
  intro k hk
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F, htime, -, hcount, hdisj, hcharts,
    hmass⟩ := hk
  refine ⟨κ, hκ, hKκ, hκN.trans ?_, T, C, γ, j, c, u, Q, R, A, F, htime.trans ?_, hcount,
    hdisj, hcharts, hmass⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_left _ _)
  · exact Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith [min_le_right ε ρ])

theorem H_le_of_nt (hN : ∀ k, 2 ≤ N k) {h w : ℝ} (hnt : nt N K L W ω ν E B f h w) :
    H N K L W ω ν E B f ≤ h := by
  apply le_of_forall_pos_le_add
  intro ρ hρ
  exact H_le_of_term hN (term_of_nt (fun k => le_trans (by norm_num) (hN k)) hnt hρ)

theorem nt_mono (hN : ∀ k, 1 ≤ N k) {h h' w w' : ℝ} (hnt : nt N K L W ω ν E B f h w)
    (hh : h ≤ h') (hw : w' ≤ w) : nt N K L W ω ν E B f h' w' := by
  obtain ⟨M, D, hMD⟩ := hnt
  refine ⟨M, D, fun ε hε => (hMD ε hε).mono fun k hk => ?_⟩
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F, htime, hwidth, hrest⟩ := hk
  refine ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    htime.trans (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)), fun b => ?_, hrest⟩
  exact (hwidth b).trans (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))

/-- A `2 × 2` matrix with entries summing to at most `a` has determinant at most `a² / 4`. -/
theorem abs_det_le_sq_sum (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    |Matrix.det Q| ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ^ 2 / 4 := by
  rw [Matrix.det_fin_two]
  simp only [Fin.sum_univ_two]
  have h1 := abs_nonneg (Q 0 0)
  have h2 := abs_nonneg (Q 0 1)
  have h3 := abs_nonneg (Q 1 0)
  have h4 := abs_nonneg (Q 1 1)
  calc |Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0| ≤ |Q 0 0| * |Q 1 1| + |Q 0 1| * |Q 1 0| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ (|Q 0 0| + |Q 0 1| + (|Q 1 0| + |Q 1 1|)) ^ 2 / 4 := by
        nlinarith [sq_nonneg (|Q 0 0| - |Q 1 1|), sq_nonneg (|Q 0 1| - |Q 1 0|),
          mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h2 h4, mul_nonneg h3 h4]

/-- A chart at scale `2 ^ T` with slack `κ` has `|det Q| 4 ^ T ≤ κ²`. -/
theorem abs_det_mul_four_pow_le {Q : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ} {T : ℕ}
    (hQ : (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T) :
    |Matrix.det Q| * (4 : ℝ) ^ T ≤ κ ^ 2 := by
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  have hsum : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hκ : 0 ≤ κ := by
    have := hsum.trans hQ
    rwa [le_div_iff₀ hpos, zero_mul] at this
  have h4 : (4 : ℝ) ^ T = (2 ^ T) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc |Matrix.det Q| * (4 : ℝ) ^ T ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ^ 2 / 4 * 4 ^ T :=
        mul_le_mul_of_nonneg_right (abs_det_le_sq_sum Q) (by positivity)
    _ ≤ (κ / 2 ^ T) ^ 2 / 4 * 4 ^ T := by gcongr
    _ = κ ^ 2 / 4 := by rw [h4]; field_simp
    _ ≤ κ ^ 2 := by nlinarith [sq_nonneg κ]

/-- Every true terminal system has narrowness at least `0` up to tolerance. -/
theorem nt_zero_of_term (hN : ∀ k, 1 ≤ N k) {h : ℝ} (ht : term N K L W ω ν E B f h) :
    nt N K L W ω ν E B f h 0 := by
  obtain ⟨M, D, hMD⟩ := ht
  refine ⟨M, D, fun ε hε => (hMD (ε / 2) (by positivity)).mono fun k hk => ?_⟩
  obtain ⟨κ, hκ, hKκ, hκN, T, C, γ, j, c, u, Q, R, A, F, htime, hcount, hdisj, hcharts,
    hmass⟩ := hk
  have hNk : 0 < N k := lt_of_lt_of_le one_pos (hN k)
  refine ⟨κ, hκ, hKκ, hκN.trans (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)),
    T, C, γ, j, c, u, Q, R, A, F,
    htime.trans (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)), fun b => ?_, hcount,
    hdisj, hcharts, hmass⟩
  have h1 := abs_det_mul_four_pow_le (hcharts b).2.2.2.1
  have h2 : κ ^ 2 ≤ N k ^ ε := by
    have h3 : κ ^ 2 ≤ (N k ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) hκN 2
    have h4 : (N k ^ (ε / 2)) ^ 2 = N k ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNk.le]
      norm_num
    rwa [h4] at h3
  rw [neg_zero, zero_add]
  exact h1.trans h2

/-- Horizon at most `L` from the initial horizon bound. -/
theorem H_le_of_IH (hIH : InitialHorizonBound) {d S η : ℝ} {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    (hp : prob N K L d S η W ω ν E P B f g G) : H N K L W ω ν E B f ≤ L := by
  apply le_of_forall_pos_le_add
  intro ρ hρ
  exact H_le_of_term hp.1 (hIH N K L d S η W ω ν E P B f g G hp (L + ρ) (by linarith))

end

end Submission.Lib.K4ExactProblemOps
