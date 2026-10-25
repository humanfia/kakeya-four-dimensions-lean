import Submission.Obl.k4_scalar_pair_atlas_assembly.Tables
import Submission.Obl.k4_scalar_pair_atlas_assembly.Counting

/-!
# Sparse representative tables

Proof of `SparseTables`.  At one scale, every old chart `i` gets the tag
`(γ i, coarse block of j i, source frame, nine-node block code)`; the output labels are the
tags that occur.  The output predictor of a tag is the old predictor of one chart carrying it,
its center is the frame center with velocity zero, and its width is `q₁`.  The compatibility
list of a witness chart `i'` collects the tags of its world and coarse block whose frame
center is within `8 N^(2σ) q₁` of the witness center and whose code is within one of the
witness code at that frame.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Set Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-! ## The coarse block of a fine block -/

/-- The coarse block containing a fine block. -/
def coarse {T₁ T : ℕ} (hT : T₁ ≤ T) (j : Fin (2 ^ T)) : Fin (2 ^ T₁) :=
  ⟨j.val / 2 ^ (T - T₁), by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_sub_of_le hT]
    exact j.isLt⟩

lemma child_coarse {T₁ T : ℕ} (hT : T₁ ≤ T) (j : Fin (2 ^ T)) :
    j = child hT (coarse hT j) ⟨j.val % 2 ^ (T - T₁), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  apply Fin.ext
  simp only [child, coarse]
  exact (Nat.div_add_mod' j.val (2 ^ (T - T₁))).symm

lemma I_subset_coarse {T₁ T : ℕ} (hT : T₁ ≤ T) (j : Fin (2 ^ T)) :
    I T j ⊆ I T₁ (coarse hT j) := by
  conv_lhs => rw [child_coarse hT j]
  exact child_interval_subset hT _ _

lemma eq_coarse_of_subset {T₁ T : ℕ} (hT : T₁ ≤ T) {j : Fin (2 ^ T)} {c : Fin (2 ^ T₁)}
    (hc : I T j ⊆ I T₁ c) : c = coarse hT j := by
  obtain ⟨r, hr⟩ := exists_child_of_subset hT c j hc
  apply Fin.ext
  simp only [coarse, hr, child]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt r.isLt, zero_add]

lemma mid_mem_I (T : ℕ) (b : Fin (2 ^ T)) : mid T b ∈ I T b := by
  have := node_mem_I T b 1
  simpa [off] using this

lemma abs_mid_le_one (T : ℕ) (b : Fin (2 ^ T)) : |mid T b| ≤ 1 := by
  have hb : (b : ℝ) + 1 ≤ (2 : ℝ) ^ T := by exact_mod_cast b.isLt
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  unfold mid
  rw [abs_of_nonneg (by positivity), div_le_one hpos]
  linarith

/-! ## Tags -/

/-- The tag of an old chart: world, coarse block, source frame and nine-node block code. -/
abbrev Tag (Wk T₁ : ℕ) := Fin Wk × Fin (2 ^ T₁) × ℤ × (Fin 3 → Fin 3 → ℤ)

/-- The tag of an old chart at code spacing `Δ`. -/
def tagOfChart {Wk T₁ T n : ℕ} (hT : T₁ ≤ T) (Δ : ℝ) (γ : Fin n → Fin Wk)
    (j : Fin n → Fin (2 ^ T)) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (i : Fin n) : Tag Wk T₁ :=
  (γ i, coarse hT (j i), srcFrame T₁ (coarse hT (j i)) (u i) (v i),
    blockCode Δ T₁ (coarse hT (j i)) (srcFrame T₁ (coarse hT (j i)) (u i) (v i)) (P i))


/-! ## Extended estimates of one old chart on its coarse block -/

/-- An old chart's strip, fit and frame localization on its whole coarse block. -/
lemma chart_extended {T₁ T : ℕ} (hT : T₁ ≤ T) {j₀ : Fin (2 ^ T)} {uu vv JJ s Lres : ℝ}
    {PP : MvPolynomial (Fin 2) ℝ} {AA : Set (ℕ × (Fin 5 → ℝ))}
    (hs1 : 1 ≤ s) (hJ : JJ ≤ s / (2 : ℝ) ^ T) (hv : |vv| ≤ s) (hdeg : PP.totalDegree ≤ 2)
    (hfit : ∀ l ∈ AA, ∀ t ∈ I T j₀, |y l t - uu - t * vv| ≤ s * JJ ∧
      |x l t - MvPolynomial.eval ![t, y l t] PP| ≤ s * Lres) :
    ∀ l ∈ AA, ∀ t ∈ I T₁ (coarse hT j₀),
      |y l t - uu - t * vv| ≤ 3 * s ^ 2 * width T₁ ∧
      |x l t - MvPolynomial.eval ![t, y l t] PP| ≤
        48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (s * Lres) ∧
      |y l t - frameCenter (width T₁) (srcFrame T₁ (coarse hT j₀) uu vv)| ≤
        4 * s ^ 2 * width T₁ := by
  intro l hl t ht
  have hext := fine_to_coarse hT (I_subset_coarse hT j₀) l uu vv (s * JJ) (s * Lres) PP hdeg
    (hfit l hl) t ht
  have hsplit := width_split hT
  have hwT := width_pos T
  have hw₁ := width_pos T₁
  have hR1 : (1 : ℝ) ≤ (2 : ℝ) ^ (T - T₁) := one_le_pow₀ (by norm_num)
  have hJw : s * JJ ≤ s ^ 2 * width T := by
    have : JJ ≤ s * width T := by
      unfold width; rw [← div_eq_mul_inv]; exact hJ
    calc s * JJ ≤ s * (s * width T) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = s ^ 2 * width T := by ring
  have hstrip : |y l t - uu - t * vv| ≤ 3 * s ^ 2 * width T₁ := by
    refine hext.1.trans ?_
    rw [← hsplit]
    have : 0 ≤ (2 : ℝ) ^ (T - T₁) := by positivity
    calc 3 * (2 : ℝ) ^ (T - T₁) * (s * JJ) ≤ 3 * (2 : ℝ) ^ (T - T₁) * (s ^ 2 * width T) :=
          mul_le_mul_of_nonneg_left hJw (by positivity)
      _ = 3 * s ^ 2 * ((2 : ℝ) ^ (T - T₁) * width T) := by ring
  refine ⟨hstrip, hext.2, ?_⟩
  have hloc := frame_localization ht l uu vv _ hstrip
  refine hloc.trans ?_
  have : |vv| * (width T₁ / 2) ≤ s * (width T₁ / 2) :=
    mul_le_mul_of_nonneg_right hv (by positivity)
  have h1 : s * width T₁ ≤ s ^ 2 * width T₁ := by
    apply mul_le_mul_of_nonneg_right _ hw₁.le; nlinarith
  have h2 : width T₁ ≤ s * width T₁ := by
    calc width T₁ = 1 * width T₁ := (one_mul _).symm
      _ ≤ s * width T₁ := mul_le_mul_of_nonneg_right hs1 hw₁.le
  linarith

/-! ## Numerics -/

lemma rpow_le_rpow_of_le_exp {N₀ α β : ℝ} (hN1 : 1 ≤ N₀) (h : α ≤ β) : N₀ ^ α ≤ N₀ ^ β :=
  Real.rpow_le_rpow_of_exponent_le hN1 h

/-- The final residual budget: extrapolation plus representative comparison fits under the
fixed depth margin `10 e` once `N ^ σ ≥ 2 ^ 21` and `8 σ ≤ ε`. -/
lemma resid_numeric {N₀ L a e ε σ R : ℝ} (hN1 : 1 ≤ N₀) (he : 0 < e) (ha : 1 ≤ a)
    (hσε : 8 * σ ≤ ε) (hbig : (2 : ℝ) ^ 21 ≤ N₀ ^ σ) (hR0 : 0 ≤ R)
    (hR : R ≤ 2 * N₀ ^ e) :
    48 * R ^ 2 * (N₀ ^ σ * N₀ ^ (-L)) +
        144 * N₀ ^ (-L + a * e) * (3 + 8 * (N₀ ^ σ) ^ 2) ^ 2 ≤
      N₀ ^ ε * N₀ ^ (-(L - (a + 10) * e)) := by
  have hN0 : 0 < N₀ := by linarith
  set s := N₀ ^ σ with hs
  set E := N₀ ^ e with hE
  set Z := N₀ ^ (-L + a * e) with hZ
  have hs1 : 1 ≤ s := le_trans (by norm_num) hbig
  have hE1 : 1 ≤ E := Real.one_le_rpow hN1 he.le
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos hN0 _
  have h1 : N₀ ^ (-L) ≤ Z / E := by
    rw [hZ, hE, ← Real.rpow_sub hN0]
    apply rpow_le_rpow_of_le_exp hN1
    nlinarith
  have h3 : N₀ ^ (-(L - (a + 10) * e)) = Z * E ^ 10 := by
    rw [hZ, hE, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have h4 : s ^ 8 ≤ N₀ ^ ε := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    apply rpow_le_rpow_of_le_exp hN1
    push_cast; linarith
  have hE10 : E ≤ E ^ 10 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 10 := pow_le_pow_right₀ hE1 (by norm_num)
  have hR2 : R ^ 2 ≤ 4 * E ^ 2 := by nlinarith
  have hs4 : (17616 : ℝ) ≤ s ^ 4 := by
    have : (2 : ℝ) ^ 84 ≤ s ^ 4 := by
      calc (2 : ℝ) ^ 84 = ((2 : ℝ) ^ 21) ^ 4 := by norm_num
        _ ≤ s ^ 4 := pow_le_pow_left₀ (by norm_num) hbig 4
    linarith [show (17616 : ℝ) ≤ 2 ^ 84 by norm_num]
  have hsq : (3 + 8 * s ^ 2) ^ 2 ≤ 121 * s ^ 4 := by
    have : 3 + 2 * (4 * s ^ 2 * 1) / 1 ≤ 11 * s ^ 2 := by nlinarith
    have h0 : 0 ≤ 3 + 2 * (4 * s ^ 2 * 1) / 1 := by positivity
    nlinarith
  have hfirst : 48 * R ^ 2 * (s * N₀ ^ (-L)) ≤ 192 * E * s * Z := by
    have hNL : 0 ≤ N₀ ^ (-L) := Real.rpow_nonneg hN0.le _
    calc 48 * R ^ 2 * (s * N₀ ^ (-L)) ≤ 48 * (4 * E ^ 2) * (s * (Z / E)) := by
          apply mul_le_mul (by nlinarith) (mul_le_mul_of_nonneg_left h1 (by linarith))
            (by positivity) (by positivity)
      _ = 192 * E * s * Z := by field_simp; ring
  have hsecond : 144 * Z * (3 + 8 * s ^ 2) ^ 2 ≤ 17424 * Z * s ^ 4 := by
    nlinarith
  have hs_le : s ≤ s ^ 4 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  rw [h3]
  calc 48 * R ^ 2 * (s * N₀ ^ (-L)) + 144 * Z * (3 + 8 * s ^ 2) ^ 2
      ≤ 192 * E * s * Z + 17424 * Z * s ^ 4 := add_le_add hfirst hsecond
    _ ≤ 17616 * E * s ^ 4 * Z := by
        have a1 : E * s * Z ≤ E * s ^ 4 * Z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_le (by linarith)) hZ0.le
        have a2 : Z * s ^ 4 ≤ E * s ^ 4 * Z := by
          have : 0 ≤ Z * s ^ 4 := by positivity
          calc Z * s ^ 4 = 1 * (Z * s ^ 4) := (one_mul _).symm
            _ ≤ E * (Z * s ^ 4) := mul_le_mul_of_nonneg_right hE1 this
            _ = E * s ^ 4 * Z := by ring
        linarith
    _ ≤ s ^ 4 * E * s ^ 4 * Z := by
        apply mul_le_mul_of_nonneg_right _ hZ0.le
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hs4 (by linarith)
    _ = s ^ 8 * Z * E := by ring
    _ ≤ N₀ ^ ε * (Z * E ^ 10) := by
        rw [← mul_assoc]
        apply mul_le_mul (mul_le_mul_of_nonneg_right h4 hZ0.le) hE10 (by linarith)
          (by positivity)


lemma pow_le_rpow_of_mul_le {N₀ σ ε : ℝ} (hN1 : 1 ≤ N₀) (m : ℕ) (h : (m : ℝ) * σ ≤ ε) :
    (N₀ ^ σ) ^ m ≤ N₀ ^ ε := by
  have hN0 : 0 < N₀ := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  apply rpow_le_rpow_of_le_exp hN1
  linarith

/-! ## The table at one scale -/

/-- At one scale with `N ^ σ ≥ 2 ^ 21`, an old true terminal chart system yields a sparse
representative table for the coarsening `T₁`. -/
theorem table_at_scale (p : Code) (k : ℕ) (h e a ε σ : ℝ) (B : ℕ)
    (hN : 2 ≤ N p k) (hσε : 8 * σ ≤ ε) (hσ1 : σ ≤ 1)
    (ha : 1 ≤ a) (he : 0 < e) (hbig : (2 : ℝ) ^ 21 ≤ N p k ^ σ)
    {T n : ℕ} {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set (ℕ × (Fin 5 → ℝ))} {C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)}
    {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hcd : ChartData p B (L p) (L p) (h + σ) σ true k T n γ j A C u v J P Λ)
    {T₁ : ℕ} (hT₁ : T₁ ≤ T) (hR : (2 : ℝ) ^ (T - T₁) ≤ 2 * N p k ^ e) :
    ∃ (m : ℕ) (g : Fin m → Fin (W p k)) (b : Fin m → Fin (2 ^ T₁))
      (code : Fin n → Fin m) (u' v' J' : Fin m → ℝ)
      (P' : Fin m → MvPolynomial (Fin 2) ℝ) (R : Fin n → Finset (Fin m)),
      Table p k (B + ⌈h⌉₊ + 1) (L p - (a + 10) * e) ε T T₁ n γ j A u v P a e
        m g b code u' v' J' P' R := by
  classical
  obtain ⟨hTh, hn, -, -, -, hper, -, -, -, -⟩ := hcd
  have hN0 : 0 < N p k := by linarith
  have hN1 : 1 ≤ N p k := by linarith
  have hs1 : 1 ≤ N p k ^ σ := le_trans (by norm_num) hbig
  have hs8 : (N p k ^ σ) ^ 8 ≤ N p k ^ ε :=
    pow_le_rpow_of_mul_le hN1 8 (by push_cast; linarith)
  have hs4 : (N p k ^ σ) ^ 4 ≤ N p k ^ (ε / 2) :=
    pow_le_rpow_of_mul_le hN1 4 (by push_cast; linarith)
  have hs2big : (2 : ℝ) ^ 42 ≤ (N p k ^ σ) ^ 2 := by
    calc (2 : ℝ) ^ 42 = ((2 : ℝ) ^ 21) ^ 2 := by norm_num
      _ ≤ (N p k ^ σ) ^ 2 := pow_le_pow_left₀ (by norm_num) hbig 2
  have hε1 : 1 ≤ N p k ^ ε := le_trans (one_le_pow₀ hs1) hs8
  have hΔpos : 0 < N p k ^ (-L p + a * e) := Real.rpow_pos_of_pos hN0 _
  have hq₁ := width_pos T₁
  have hq₁le : width T₁ ≤ 1 := by
    unfold width; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  -- per-chart facts
  have hJle : ∀ i, J i ≤ N p k ^ σ / (2 : ℝ) ^ T := fun i => (hper i).2.2.2.1
  have huv : ∀ i, |u i| + |v i| ≤ N p k ^ σ := fun i => (hper i).2.2.2.2.1
  have hv : ∀ i, |v i| ≤ N p k ^ σ := fun i => by
    have := huv i; have := abs_nonneg (u i); linarith
  have hdeg : ∀ i, (P i).totalDegree ≤ 2 := fun i => (hper i).2.2.2.2.2.1
  have hcoef : ∀ i c, |(P i).coeff c| ≤ N p k ^ (B : ℝ) := fun i => (hper i).2.2.2.2.2.2.1
  have hfit : ∀ i, ∀ l ∈ A i, ∀ t ∈ I T (j i), |y l t - u i - t * v i| ≤ N p k ^ σ * J i ∧
      |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ σ * N p k ^ (-L p) :=
    fun i => (hper i).2.2.2.2.2.2.2.2.2.2.1
  have hext : ∀ i, ∀ l ∈ A i, ∀ t ∈ I T₁ (coarse hT₁ (j i)),
      |y l t - u i - t * v i| ≤ 3 * (N p k ^ σ) ^ 2 * width T₁ ∧
      |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤
        48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ σ * N p k ^ (-L p)) ∧
      |y l t - frameCenter (width T₁) (srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i))| ≤
        4 * (N p k ^ σ) ^ 2 * width T₁ :=
    fun i => chart_extended hT₁ hs1 (hJle i) (hv i) (hdeg i) (hfit i)
  -- complexity exponent
  have hG : N p k ^ (B : ℝ) ≤ N p k ^ (((B + ⌈h⌉₊ + 1 : ℕ) : ℝ)) := by
    apply rpow_le_rpow_of_le_exp hN1; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈h⌉₊]
  have h2T₁ : (2 : ℝ) ^ T₁ ≤ N p k ^ (((B + ⌈h⌉₊ + 1 : ℕ) : ℝ)) := by
    calc (2 : ℝ) ^ T₁ ≤ (2 : ℝ) ^ T := pow_le_pow_right₀ (by norm_num) hT₁
      _ ≤ N p k ^ (h + σ) := hTh
      _ ≤ _ := by
        apply rpow_le_rpow_of_le_exp hN1
        push_cast
        have := Nat.le_ceil h
        linarith [Nat.cast_nonneg (α := ℝ) B]
  -- tags
  set Δ := N p k ^ (-L p + a * e) with hΔ
  let τ : Fin n → Tag (W p k) T₁ := tagOfChart hT₁ Δ γ j u v P
  let S : Finset (Tag (W p k) T₁) := Finset.univ.image τ
  let eqv : { z // z ∈ S } ≃ Fin S.card := S.equivFin
  let tg : Fin S.card → Tag (W p k) T₁ := fun o => (eqv.symm o).1
  have hrep : ∀ o, ∃ i, τ i = tg o := by
    intro o
    have := (eqv.symm o).2
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at this
    exact this
  choose rep hrep using hrep
  let code : Fin n → Fin S.card := fun i =>
    eqv ⟨τ i, Finset.mem_image_of_mem τ (Finset.mem_univ i)⟩
  have htg : ∀ i, tg (code i) = τ i := by
    intro i; simp only [tg, code, Equiv.symm_apply_apply]
  let g : Fin S.card → Fin (W p k) := fun o => (tg o).1
  let bb : Fin S.card → Fin (2 ^ T₁) := fun o => (tg o).2.1
  let fr : Fin S.card → ℤ := fun o => (tg o).2.2.1
  let cd : Fin S.card → Fin 3 → Fin 3 → ℤ := fun o => (tg o).2.2.2
  let K' : ℝ := 8 * (N p k ^ σ) ^ 2
  let cw : Fin n → ℝ := fun i => u i + mid T₁ (coarse hT₁ (j i)) * v i
  let R : Fin n → Finset (Fin S.card) := fun i' => Finset.univ.filter (fun o =>
    g o = γ i' ∧ bb o = coarse hT₁ (j i') ∧ |cw i' - frameCenter (width T₁) (fr o)| ≤ K' * width T₁ ∧
      ∀ m₁ m₂, |cd o m₁ m₂ - blockCode Δ T₁ (bb o) (fr o) (P i') m₁ m₂| ≤ 1)
  have hg : ∀ i, g (code i) = γ i := fun i => by simp only [g, htg]; rfl
  have hbb : ∀ i, bb (code i) = coarse hT₁ (j i) := fun i => by simp only [bb, htg]; rfl
  have hfr : ∀ i, fr (code i) = srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i) :=
    fun i => by simp only [fr, htg]; rfl
  have hcd' : ∀ i, cd (code i) = blockCode Δ T₁ (coarse hT₁ (j i))
      (srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i)) (P i) := fun i => by simp only [cd, htg]; rfl
  refine ⟨S.card, g, bb, code, fun o => frameCenter (width T₁) (fr o), fun _ => 0,
    fun _ => width T₁, fun o => P (rep o), R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- number of tags
    have hcard : S.card ≤ n := by
      calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
        _ = n := by simp
    calc (S.card : ℝ) ≤ n := by exact_mod_cast hcard
      _ ≤ N p k ^ (B : ℝ) := hn
      _ ≤ _ := hG
  · intro i
    exact ⟨hg i, by rw [hbb i]; exact I_subset_coarse hT₁ (j i)⟩
  · intro o
    have hro := hrep o
    have hfro : fr o = srcFrame T₁ (coarse hT₁ (j (rep o))) (u (rep o)) (v (rep o)) := by
      simp only [fr, ← hro]; rfl
    refine ⟨hq₁, ?_, ?_, ?_, hdeg (rep o), fun c => (hcoef (rep o) c).trans hG⟩
    · rw [show (width T₁)⁻¹ = (2 : ℝ) ^ T₁ by unfold width; rw [inv_inv]]
      exact h2T₁
    · rw [div_eq_mul_inv]
      calc width T₁ = 1 * ((2 : ℝ) ^ T₁)⁻¹ := by unfold width; ring
        _ ≤ N p k ^ ε * ((2 : ℝ) ^ T₁)⁻¹ := mul_le_mul_of_nonneg_right hε1 (by positivity)
    · show |frameCenter (width T₁) (fr o)| + |(0 : ℝ)| ≤ N p k ^ ε
      rw [abs_zero, add_zero, hfro]
      set c := u (rep o) + mid T₁ (coarse hT₁ (j (rep o))) * v (rep o) with hc
      have hcF := abs_sub_frameCenter_le (c := c) hq₁
      have hcabs : |c| ≤ N p k ^ σ := by
        have hm := abs_mid_le_one T₁ (coarse hT₁ (j (rep o)))
        calc |c| ≤ |u (rep o)| + |mid T₁ (coarse hT₁ (j (rep o))) * v (rep o)| := abs_add_le _ _
          _ ≤ |u (rep o)| + 1 * |v (rep o)| := by
              rw [abs_mul]; gcongr
          _ ≤ N p k ^ σ := by linarith [huv (rep o)]
      have : |frameCenter (width T₁) (srcFrame T₁ (coarse hT₁ (j (rep o))) (u (rep o))
          (v (rep o)))| ≤ N p k ^ σ + 1 / 4 := by
        unfold srcFrame
        rw [← hc]
        calc _ = |c - (c - frameCenter (width T₁) (frameIdx (width T₁) c))| := by ring_nf
          _ ≤ |c| + |c - frameCenter (width T₁) (frameIdx (width T₁) c)| := abs_sub _ _
          _ ≤ N p k ^ σ + 1 / 4 := by linarith
      refine this.trans (le_trans ?_ hs8)
      have h2 : (N p k ^ σ) ^ 2 ≤ (N p k ^ σ) ^ 8 := pow_le_pow_right₀ hs1 (by norm_num)
      have hs2 : (2 : ℝ) ≤ N p k ^ σ := le_trans (by norm_num) hbig
      nlinarith
  · -- the grouped assignments fit the representative predictors
    intro i l hl t ht
    rw [hbb i] at ht
    have hE := hext i l hl t ht
    have hro := hrep (code i)
    rw [htg i] at hro
    have hc0 : coarse hT₁ (j (rep (code i))) = coarse hT₁ (j i) := congrArg (fun z => z.2.1) hro
    have hf0 : srcFrame T₁ (coarse hT₁ (j (rep (code i)))) (u (rep (code i))) (v (rep (code i)))
        = srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i) := congrArg (fun z => z.2.2.1) hro
    have hb0 : blockCode Δ T₁ (coarse hT₁ (j (rep (code i))))
        (srcFrame T₁ (coarse hT₁ (j (rep (code i)))) (u (rep (code i))) (v (rep (code i))))
          (P (rep (code i))) = blockCode Δ T₁ (coarse hT₁ (j i))
        (srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i)) (P i) := congrArg (fun z => z.2.2.2) hro
    rw [hf0, hc0] at hb0
    have h4s : 4 * (N p k ^ σ) ^ 2 ≤ N p k ^ ε := by
      have h2 : (N p k ^ σ) ^ 4 ≤ (N p k ^ σ) ^ 8 := pow_le_pow_right₀ hs1 (by norm_num)
      have : 4 * (N p k ^ σ) ^ 2 ≤ (N p k ^ σ) ^ 4 := by nlinarith
      linarith
    constructor
    · show |y l t - frameCenter (width T₁) (fr (code i)) - t * 0| ≤ N p k ^ ε * width T₁
      rw [hfr i, mul_zero, sub_zero]
      exact hE.2.2.trans (mul_le_mul_of_nonneg_right h4s hq₁.le)
    · show |x l t - MvPolynomial.eval ![t, y l t] (P (rep (code i)))| ≤
        N p k ^ ε * N p k ^ (-(L p - (a + 10) * e))
      have hcmp := blockCode_eq_bound hΔpos (hdeg i) (hdeg (rep (code i))) hb0.symm ht (y l t)
      set F := frameCenter (width T₁) (srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i))
      have hyF := hE.2.2
      have h2 : 2 * |y l t - F| / width T₁ ≤ 8 * (N p k ^ σ) ^ 2 := by
        rw [div_le_iff₀ hq₁]; linarith
      have hsq : (3 + 2 * |y l t - F| / width T₁) ^ 2 ≤ (3 + 8 * (N p k ^ σ) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      have hnum := resid_numeric (L := L p) hN1 he ha hσε hbig
        (R := (2 : ℝ) ^ (T - T₁)) (by positivity) hR
      calc |x l t - MvPolynomial.eval ![t, y l t] (P (rep (code i)))|
          ≤ |x l t - MvPolynomial.eval ![t, y l t] (P i)| +
            |MvPolynomial.eval ![t, y l t] (P i) -
              MvPolynomial.eval ![t, y l t] (P (rep (code i)))| := abs_sub_le _ _ _
        _ ≤ 48 * ((2 : ℝ) ^ (T - T₁)) ^ 2 * (N p k ^ σ * N p k ^ (-L p)) +
            144 * Δ * (3 + 8 * (N p k ^ σ) ^ 2) ^ 2 := by
            apply add_le_add hE.2.1
            exact hcmp.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
        _ ≤ N p k ^ ε * N p k ^ (-(L p - (a + 10) * e)) := hnum
  · -- sparse compatibility lists
    intro i'
    have hK' : 0 ≤ K' := by positivity
    have hcount := card_le_of_near_codes (R i') {coarse hT₁ (j i')}
      (frameWindow (width T₁) (cw i') K') {i'} bb fr cd
      (fun w b d => blockCode Δ T₁ b d (P w)) ?_ ?_
    · have hwin := card_frameWindow_le (width T₁) (cw i') K' hK'
      have hs2 : (2 : ℝ) ^ 42 ≤ (N p k ^ σ) ^ 2 := hs2big
      calc ((R i').card : ℝ)
          ≤ ((1 * (frameWindow (width T₁) (cw i') K').card * 1 * 3 ^ 9 : ℕ) : ℝ) := by
            simp only [Finset.card_singleton] at hcount
            exact_mod_cast hcount
        _ = ((frameWindow (width T₁) (cw i') K').card : ℝ) * 3 ^ 9 := by push_cast; ring
        _ ≤ (8 * K' + 1) * 3 ^ 9 := by gcongr
        _ ≤ (N p k ^ σ) ^ 4 := by
            simp only [K']
            have : (8 * (8 * (N p k ^ σ) ^ 2) + 1) * 3 ^ 9 ≤ 65 * 3 ^ 9 * (N p k ^ σ) ^ 2 := by
              nlinarith
            have h4 : (N p k ^ σ) ^ 4 = (N p k ^ σ) ^ 2 * (N p k ^ σ) ^ 2 := by ring
            have : 65 * 3 ^ 9 * (N p k ^ σ) ^ 2 ≤ (N p k ^ σ) ^ 2 * (N p k ^ σ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [show (65 : ℝ) * 3 ^ 9 ≤ 2 ^ 42 by norm_num]
            linarith
        _ ≤ N p k ^ (ε / 2) := hs4
    · intro o ho o' ho' hb hf hc
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ho ho'
      have hgo : g o = g o' := by rw [ho.1, ho'.1]
      have htt : tg o = tg o' := Prod.ext hgo (Prod.ext hb (Prod.ext hf hc))
      have : eqv.symm o = eqv.symm o' := Subtype.ext htt
      exact eqv.symm.injective this
    · intro o ho
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ho
      refine ⟨by rw [ho.2.1]; exact Finset.mem_singleton_self _,
        mem_frameWindow hq₁ ho.2.2.1, i', Finset.mem_singleton_self _, ho.2.2.2⟩
  · -- list members share the witness world and block
    intro i o ho
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    exact ⟨ho.1, by rw [ho.2.1]; exact I_subset_coarse hT₁ (j i)⟩
  · -- good pairs: the source tag is in the witness list
    intro i i' hγ c hc hc' hne hA
    have e1 := eq_coarse_of_subset hT₁ hc
    have e2 := eq_coarse_of_subset hT₁ hc'
    subst e1
    obtain ⟨l, hl, hl'⟩ := hne
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [hg i, hγ], by rw [hbb i, e2], ?_, ?_⟩
    · rw [hfr i]
      have ht : mid T₁ (coarse hT₁ (j i)) ∈ I T₁ (coarse hT₁ (j i)) := mid_mem_I T₁ _
      have ht' : mid T₁ (coarse hT₁ (j i)) ∈ I T₁ (coarse hT₁ (j i')) := by
        rw [← e2]; exact ht
      have h1 := (hext i l hl _ ht).2.2
      have h2 := (hext i' l hl' _ ht').1
      have hw := frameCenter_near_witness ht h1 h2
      show |u i' + mid T₁ (coarse hT₁ (j i')) * v i' -
          frameCenter (width T₁) (srcFrame T₁ (coarse hT₁ (j i)) (u i) (v i))| ≤ K' * width T₁
      rw [← e2]
      refine hw.trans ?_
      have hvv : |v i'| * (width T₁ / 2) ≤ (N p k ^ σ) ^ 2 * width T₁ := by
        have : |v i'| ≤ (N p k ^ σ) ^ 2 := by nlinarith [hv i']
        nlinarith
      simp only [K']
      nlinarith
    · intro m₁ m₂
      rw [hcd' i, hbb i, hfr i]
      exact blockCode_near_of_agrees hA hΔpos m₁ m₂


/-! ## The geometric child -/

/-- Sparse representative tables exist at every large scale, with one complexity exponent
`G = B + ⌈h⌉ + 1` for all losses `ε`. -/
theorem sparseTables : SparseTables := by
  intro p hp h e a he heh ha hr B hB
  refine ⟨B + ⌈h⌉₊ + 1, by omega, ?_⟩
  intro ε hε
  have hσpos : 0 < min ε 1 / 8 := by positivity
  refine ⟨min ε 1 / 8, hσpos, by linarith [min_le_left ε 1], ?_⟩
  have hN2 : ∀ k, 2 ≤ N p k := hp.1.1
  have htend : Tendsto (N p) atTop atTop := hp.1.2.1
  have hev : ∀ᶠ k in atTop, (2 : ℝ) ^ 21 ≤ N p k ^ (min ε 1 / 8) :=
    ((tendsto_rpow_atTop hσpos).comp htend).eventually_ge_atTop _
  filter_upwards [hev] with k hk
  intro T n γ j A C u v J P Λ hcd T₁ hT₁ hR _
  exact table_at_scale p k h e a ε (min ε 1 / 8) B (hN2 k)
    (by linarith [min_le_left ε 1]) (by linarith [min_le_right ε 1]) ha he hk hcd hT₁ hR

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
