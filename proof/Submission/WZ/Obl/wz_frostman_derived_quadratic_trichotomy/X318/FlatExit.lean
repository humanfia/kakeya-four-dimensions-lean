-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatExit.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatParent
-- Copied from session x0318 (o070 branch, commit 2c4a35f, file FlatExit.lean), namespace renamed.

/-!
# Flat exit

`flat_exit`: exact covers by unit `ρ`-tubes whose fibres all factor through flat saturated o064
boxes give frozen (C) on a `δ^θ` share, through x0210's `flat_refinement_of_local_factor`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
open Set MeasureTheory
open scoped ENNReal

/-- Pigeonhole into `M` classes. -/
lemma exists_class {I : Type*} [DecidableEq I] (S : Finset I) (f : I → ℕ) {M : ℕ}
    (hM : 0 < M) (hf : ∀ i ∈ S, f i < M) :
    ∃ k < M, S.card ≤ M * (S.filter (fun i => f i = k)).card := by
  classical
  have hcover : S = (Finset.range M).biUnion (fun k => S.filter (fun i => f i = k)) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hi; exact ⟨f i, hf i hi, hi, rfl⟩
    · rintro ⟨_, _, hi, _⟩; exact hi
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  have hsum : S.card ≤ ∑ k ∈ Finset.range M, (S.filter (fun i => f i = k)).card := by
    conv_lhs => rw [hcover]
    exact Finset.card_biUnion_le
  have hlt : M * ∑ k ∈ Finset.range M, (S.filter (fun i => f i = k)).card < M * S.card := by
    rw [Finset.mul_sum]
    calc ∑ k ∈ Finset.range M, M * (S.filter (fun i => f i = k)).card
        < ∑ _k ∈ Finset.range M, S.card :=
          Finset.sum_lt_sum_of_nonempty (by simp; omega) (fun k hk => hno k (Finset.mem_range.mp hk))
      _ = M * S.card := by simp
  have := lt_of_mul_lt_mul_left hlt
  omega

/-- Dyadic class of a real number in `[lo, hi]` through `⌊hi/x⌋₊`. -/
lemma dyadic_bounds_of_log {x hi : ℝ} (hx : 0 < x) (hxhi : x ≤ hi) {α : ℕ}
    (hα : Nat.log 2 ⌊hi / x⌋₊ = α) : x ≤ hi / 2 ^ α ∧ hi / 2 ^ α < 2 * x := by
  have hhi : 0 < hi := hx.trans_le hxhi
  have h1 : 1 ≤ hi / x := by rw [le_div_iff₀ hx]; linarith
  have hfl : 1 ≤ ⌊hi / x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hlow : 2 ^ α ≤ ⌊hi / x⌋₊ := by rw [← hα]; exact Nat.pow_log_le_self 2 (by omega)
  have hup : ⌊hi / x⌋₊ < 2 ^ (α + 1) := by rw [← hα]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hlowR : (2 : ℝ) ^ α ≤ hi / x := by
    have h1 : ((2 ^ α : ℕ) : ℝ) ≤ (⌊hi / x⌋₊ : ℝ) := by exact_mod_cast hlow
    have h2 : (⌊hi / x⌋₊ : ℝ) ≤ hi / x := Nat.floor_le (by positivity)
    push_cast at h1
    linarith
  have hupR : hi / x < (2 : ℝ) ^ (α + 1) := by
    have := (Nat.floor_lt (by positivity)).mp hup
    exact_mod_cast this
  have h2α : (0 : ℝ) < 2 ^ α := by positivity
  constructor
  · rw [le_div_iff₀ h2α]
    have := (le_div_iff₀ hx).mp hlowR
    linarith
  · rw [div_lt_iff₀ h2α]
    have := (div_lt_iff₀ hx).mp hupR
    rw [pow_succ] at this
    linarith


/-- The arithmetic of the saturation step in `flat_exit`. -/
lemma flat_sat_arith {d κ A B c a b N : ℝ} (hd : 0 ≤ d) (h64 : 64 * d ≤ 1)
    (hκ : κ ≤ 2 * c) (hA : A ≤ 2 * a) (hB : B ≤ 2 * b) (hκ0 : 0 ≤ κ) (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hsat : d * c * a * b ≤ N) : d * d * κ * (8 * A * B) ≤ N := by
  have h1 : κ * (8 * A * B) ≤ (2 * c) * (8 * (2 * a) * (2 * b)) := by gcongr
  have h2 : d * d * κ * (8 * A * B) ≤ d * d * ((2 * c) * (8 * (2 * a) * (2 * b))) := by
    have : 0 ≤ d * d := mul_nonneg hd hd
    nlinarith
  have h3 : d * d * ((2 * c) * (8 * (2 * a) * (2 * b))) = (64 * d) * (d * c * a * b) := by ring
  have h4 : 0 ≤ d * c * a * b := by positivity
  have h5 : (64 * d) * (d * c * a * b) ≤ d * c * a * b := by nlinarith
  linarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Flat exit.** Exact covers by unit `ρ`-tubes in which every fibre has a flat saturated
o064 factorization (`b > Λ a`, as in `fibre_dichotomy`) give the frozen flat-prism structure
(C) on a `δ^θ` share of the family, through x0210's `flat_refinement_of_local_factor`. The
parents are pigeonholed into one dyadic class of `(a, min b ρ, c)` at a cost `hpig`. -/
theorem flat_exit {δ ρ ν Λ ζ ζ₂ ζ₃ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hζ : 0 ≤ ζ) (hζ₂ : 0 ≤ ζ₂) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hΛ : 16 * δ ^ (-ν - ζ₂ / 200) ≤ Λ) (h64 : 64 * δ ^ ν ≤ 1)
    {n q : ℕ} (hn : 0 < n)
    (hpig : (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν))
    (herror : localFlatLoss * δ ^ (ζ₃ - ζ - 5 * (2 * ν)) ≤ 1)
    (hretain : 2 * δ ^ (θ - 2 * ν) ≤ 1)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)))
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hRsep : Distinct (fun l => Tube ρ (z l) (w l)))
    (par : Fin n → Fin q) (hpar : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (par i)) (w (par i)))
    (huniq : ∀ i l, Tube δ (x i) (v i) ⊆ Tube ρ (z l) (w l) → l = par i)
    (hflat : ∀ l, (Finset.univ.filter (fun i => par i = l)).Nonempty → ∃ a b : ℝ,
      δ ≤ a ∧ Λ * a < b ∧ b ≤ 2 ∧
      LongFactor ν δ a b (fun j : Fin (Finset.univ.filter (fun i => par i = l)).card =>
        Tube δ (x ((Finset.univ.filter (fun i => par i = l)).equivFin.symm j))
          (v ((Finset.univ.filter (fun i => par i = l)).equivFin.symm j)))) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
      FlatPrisms ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
  set T : Fin n → Set Space := fun i => Tube δ (x i) (v i) with hT
  set fib : Fin q → Finset (Fin n) := fun l => Finset.univ.filter (fun i => par i = l) with hfib
  have hδν : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ ν
  have hδnν : 1 ≤ δ ^ (-ν) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hδνnν : δ ^ ν * δ ^ (-ν) = 1 := by rw [← Real.rpow_add hδ]; simp
  have hΛ16 : 16 * δ ^ (-ν) ≤ Λ := by
    refine le_trans ?_ hΛ
    have : δ ^ (-ν) ≤ δ ^ (-ν - ζ₂ / 200) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    linarith
  have hΛ8 : 8 ≤ Λ := by linarith
  -- per-parent data
  have hdata : ∀ l, ∃ (a b' c : ℝ) (G : Finset (Fin n)) (p : ℕ) (W : Fin p → Set Space)
      (c₀ e₁ e₂ e₃ : Fin p → Space), (fib l).Nonempty →
      δ ≤ a ∧ a ≤ 2 ∧ 2 * δ ≤ b' ∧ b' ≤ ρ ∧ Λ * a ≤ 8 * δ ^ (-ν) * b' ∧ 1 ≤ c ∧
      c ≤ n * δ ^ (-ν) ∧ G ⊆ fib l ∧ δ ^ ν * (fib l).card ≤ G.card ∧
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal ((G.filter (fun i => T i ⊆ U)).card * δ ^ 2) ≤
          ENNReal.ofReal c * volume U) ∧
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (∀ j, W j ⊆ Tube ρ (z l) (w l) ∩ {y | |inner ℝ (e₁ j) (y - c₀ j)| ≤ a ∧
        |inner ℝ (e₂ j) (y - c₀ j)| ≤ b'}) ∧
      (∀ i ∈ G, ∃ j, T i ⊆ W j) ∧
      (∀ i ∈ G, (ncard {j | T i ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
      (∀ j, δ ^ ν * c * a * b' ≤ (G.filter (fun i => T i ⊆ W j)).card * δ ^ 2) := by
    intro l
    by_cases hne : (fib l).Nonempty
    · obtain ⟨a, b, hδa, hΛab, hb2, hLF⟩ := hflat l hne
      have hFR : ∀ i ∈ fib l, Tube δ (x i) (v i) ⊆ Tube ρ (z l) (w l) := by
        intro i hi
        have : par i = l := (Finset.mem_filter.mp hi).2
        rw [← this]; exact hpar i
      obtain ⟨G, c, p, W, c₀, e₁, e₂, e₃, hGF, hGsize, hc1, hKT, hfr, hW, hcov, hdeg, hsat,
        hfl⟩ := normalize_flat_parent hδ hδ1 hν hρ hρ8 hΛ8 x v hv hball (hw l) (fib l) hFR
          hδa hΛab hb2 hLF
      have ha0 : 0 < a := hδ.trans_le hδa
      have hmin_le : min b ρ ≤ ρ := min_le_right _ _
      have hb'2a : 2 * a ≤ min b ρ := by
        have h1 : 16 * δ ^ (-ν) * a ≤ Λ * a := mul_le_mul_of_nonneg_right hΛ16 ha0.le
        have h2 : 16 * δ ^ (-ν) * a ≤ 8 * δ ^ (-ν) * min b ρ := h1.trans hfl
        nlinarith
      have hGcard_le : (G.card : ℝ) ≤ n := by
        have := Finset.card_le_univ G
        rw [Fintype.card_fin] at this
        exact_mod_cast this
      refine ⟨a, min b ρ, c, G, p, W, c₀, e₁, e₂, e₃, fun _ => ⟨hδa, by nlinarith, by linarith,
        hmin_le, hfl, hc1, ?_, hGF, hGsize, hKT, hfr, hW, hcov, hdeg, hsat⟩⟩
      -- `c ≤ n δ^(-ν)` from the saturation of one container
      obtain ⟨i, hi⟩ : G.Nonempty := by
        rw [← Finset.card_pos]
        have : (0 : ℝ) < G.card := lt_of_lt_of_le (by
          have : (0 : ℝ) < (fib l).card := by exact_mod_cast Finset.card_pos.mpr hne
          positivity) hGsize
        exact_mod_cast this
      obtain ⟨j, -⟩ := hcov i hi
      have hs := hsat j
      have hcnt : ((G.filter (fun i => T i ⊆ W j)).card : ℝ) ≤ n :=
        le_trans (by exact_mod_cast Finset.card_filter_le _ _) hGcard_le
      have hab2 : δ ^ 2 ≤ a * min b ρ := by nlinarith
      have h1 : δ ^ ν * c * δ ^ 2 ≤ n * δ ^ 2 := by
        have : δ ^ ν * c * (a * min b ρ) ≤ n * δ ^ 2 := by
          calc δ ^ ν * c * (a * min b ρ) = δ ^ ν * c * a * min b ρ := by ring
            _ ≤ _ := hs
            _ ≤ n * δ ^ 2 := mul_le_mul_of_nonneg_right hcnt (sq_nonneg δ)
        have hc0 : 0 ≤ δ ^ ν * c := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hab2 hc0]
      have h2 : δ ^ ν * c ≤ n := le_of_mul_le_mul_right h1 (by positivity)
      calc c = δ ^ (-ν) * (δ ^ ν * c) := by
            rw [← mul_assoc, mul_comm (δ ^ (-ν)), hδνnν, one_mul]
        _ ≤ δ ^ (-ν) * n := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = n * δ ^ (-ν) := by ring
    · exact ⟨1, 1, 1, ∅, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
        fun h => absurd h hne⟩
  choose a b' c G p W c₀ e₁ e₂ e₃ hP using hdata
  have hfibmem : ∀ i, i ∈ fib (par i) := fun i => by simp [hfib]
  have hfibne : ∀ i, (fib (par i)).Nonempty := fun i => ⟨i, hfibmem i⟩
  set La : ℕ := Nat.log 2 ⌊2 / δ⌋₊ with hLa
  set Lc : ℕ := Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ with hLc
  let kA : Fin n → ℕ := fun i => Nat.log 2 ⌊2 / a (par i)⌋₊
  let kB : Fin n → ℕ := fun i => Nat.log 2 ⌊2 / b' (par i)⌋₊
  let kC : Fin n → ℕ := fun i => Nat.log 2 ⌊c (par i)⌋₊
  have hkA : ∀ i, kA i < La + 1 := by
    intro i
    obtain ⟨hδa, -⟩ := hP (par i) (hfibne i)
    have : ⌊2 / a (par i)⌋₊ ≤ ⌊2 / δ⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_left (by norm_num) hδ hδa)
    exact Nat.lt_succ_of_le (Nat.log_mono_right this)
  have hkB : ∀ i, kB i < La + 1 := by
    intro i
    obtain ⟨-, -, h2δ, -⟩ := hP (par i) (hfibne i)
    have : ⌊2 / b' (par i)⌋₊ ≤ ⌊2 / δ⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_left (by norm_num) hδ (by linarith))
    exact Nat.lt_succ_of_le (Nat.log_mono_right this)
  have hkC : ∀ i, kC i < Lc + 1 := by
    intro i
    obtain ⟨-, -, -, -, -, -, hcn, -⟩ := hP (par i) (hfibne i)
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_le_floor hcn))
  obtain ⟨α, -, h1⟩ := exists_class Finset.univ kA (Nat.succ_pos La) (fun i _ => hkA i)
  set S₁ := Finset.univ.filter (fun i => kA i = α) with hS₁
  obtain ⟨β, -, h2⟩ := exists_class S₁ kB (Nat.succ_pos La) (fun i _ => hkB i)
  set S₂ := S₁.filter (fun i => kB i = β) with hS₂
  obtain ⟨γ, -, h3⟩ := exists_class S₂ kC (Nat.succ_pos Lc) (fun i _ => hkC i)
  set S₃ := S₂.filter (fun i => kC i = γ) with hS₃
  have hmemS₃ : ∀ i, i ∈ S₃ ↔ kA i = α ∧ kB i = β ∧ kC i = γ := by
    intro i; simp [hS₃, hS₂, hS₁, and_assoc]
  have hS₃size : n ≤ (La + 1) * (La + 1) * (Lc + 1) * S₃.card := by
    have h1' : n ≤ (La + 1) * S₁.card := by
      simpa [Finset.card_univ, Fintype.card_fin] using h1
    calc n ≤ (La + 1) * S₁.card := h1'
      _ ≤ (La + 1) * ((La + 1) * S₂.card) := Nat.mul_le_mul_left _ h2
      _ ≤ (La + 1) * ((La + 1) * ((Lc + 1) * S₃.card)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
      _ = (La + 1) * (La + 1) * (Lc + 1) * S₃.card := by ring
  have hS₃ne : S₃.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    have : S₃.card = 0 := by omega
    rw [this, mul_zero] at hS₃size
    omega
  -- class parents and their common bounds
  set Lcl : Finset (Fin q) := S₃.image par with hLcl
  have hLclS : ∀ l ∈ Lcl, ∃ i ∈ S₃, par i = l := by
    intro l hl; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl; exact ⟨i, hi, rfl⟩
  have hLclne : ∀ l ∈ Lcl, (fib l).Nonempty := by
    intro l hl; obtain ⟨i, -, rfl⟩ := hLclS l hl; exact hfibne i
  set A : ℝ := 2 / 2 ^ α with hA
  set B : ℝ := min (2 / 2 ^ β) ρ with hB
  set κ : ℝ := 2 ^ (γ + 1) with hκ
  have hbounds : ∀ l ∈ Lcl, a l ≤ A ∧ A < 2 * a l ∧ b' l ≤ B ∧ B < 2 * b' l ∧
      c l ≤ κ ∧ κ ≤ 2 * c l := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := hLclS l hl
    obtain ⟨hkAi, hkBi, hkCi⟩ := (hmemS₃ i).mp hi
    obtain ⟨hδa, ha2, h2δb, hbρ, -, hc1, -⟩ := hP (par i) (hfibne i)
    have ha0 : 0 < a (par i) := hδ.trans_le hδa
    have hb0 : 0 < b' (par i) := by linarith
    obtain ⟨hA1, hA2⟩ := dyadic_bounds_of_log ha0 ha2 hkAi
    obtain ⟨hB1, hB2⟩ := dyadic_bounds_of_log hb0 (by linarith : b' (par i) ≤ 2) hkBi
    have hcfl : 2 ^ γ ≤ ⌊c (par i)⌋₊ := by
      rw [← hkCi]; exact Nat.pow_log_le_self 2 (Nat.floor_pos.mpr hc1).ne'
    have hcfl2 : ⌊c (par i)⌋₊ < 2 ^ (γ + 1) := by
      rw [← hkCi]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hcR1 : (2 : ℝ) ^ γ ≤ c (par i) := by
      have h1 : ((2 ^ γ : ℕ) : ℝ) ≤ (⌊c (par i)⌋₊ : ℝ) := by exact_mod_cast hcfl
      have h2 : (⌊c (par i)⌋₊ : ℝ) ≤ c (par i) := Nat.floor_le (by linarith)
      push_cast at h1; linarith
    have hcR2 : c (par i) < (2 : ℝ) ^ (γ + 1) := by
      have h1 := Nat.lt_floor_add_one (c (par i))
      have h2 : ((⌊c (par i)⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (γ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcfl2
      push_cast at h2; linarith
    refine ⟨hA1, hA2, le_min hB1 hbρ, (min_le_left _ _).trans_lt hB2, hcR2.le, ?_⟩
    rw [hκ, pow_succ]; linarith
  -- the kept family
  set Gt : Finset (Fin n) := Lcl.biUnion G with hGt
  have hGsub : ∀ l ∈ Lcl, G l ⊆ fib l := fun l hl => (hP l (hLclne l hl)).2.2.2.2.2.2.2.1
  have hdisj : (Lcl : Set (Fin q)).PairwiseDisjoint G := by
    intro l hl l' hl' hll'
    refine Finset.disjoint_left.mpr fun i hi hi' => hll' ?_
    have e1 := (Finset.mem_filter.mp (hGsub l hl hi)).2
    have e2 := (Finset.mem_filter.mp (hGsub l' hl' hi')).2
    rw [← e1, ← e2]
  have hGtcard : (Gt.card : ℝ) = ∑ l ∈ Lcl, ((G l).card : ℝ) := by
    rw [hGt, Finset.card_biUnion hdisj]; push_cast; rfl
  have hS₃eq : S₃ = Lcl.biUnion fib := by
    ext i
    simp only [Finset.mem_biUnion, hfib, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi; exact ⟨par i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨i', hi', hpi'⟩ := hLclS _ hl
      have := (hmemS₃ i').mp hi'
      rw [hmemS₃]
      simp only [kA, kB, kC] at this ⊢
      rw [← hpi']
      exact this
  have hfibdisj : (Lcl : Set (Fin q)).PairwiseDisjoint fib := by
    intro l hl l' hl' hll'
    refine Finset.disjoint_left.mpr fun i hi hi' => hll' ?_
    rw [← (Finset.mem_filter.mp hi).2, ← (Finset.mem_filter.mp hi').2]
  have hGtsize : δ ^ (2 * ν) * n ≤ Gt.card := by
    have hsum : δ ^ ν * (S₃.card : ℝ) ≤ Gt.card := by
      rw [hGtcard, hS₃eq, Finset.card_biUnion hfibdisj]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun l hl => (hP l (hLclne l hl)).2.2.2.2.2.2.2.2.1
    have hM : (n : ℝ) ≤ δ ^ (-ν) * S₃.card := by
      have : (n : ℝ) ≤ (((La + 1) * (La + 1) * (Lc + 1) : ℕ) : ℝ) * S₃.card := by
        exact_mod_cast hS₃size
      exact this.trans (mul_le_mul_of_nonneg_right hpig (Nat.cast_nonneg _))
    have e2 : δ ^ (2 * ν) = δ ^ ν * δ ^ ν := by
      rw [← Real.rpow_add hδ]; ring_nf
    calc δ ^ (2 * ν) * n ≤ δ ^ (2 * ν) * (δ ^ (-ν) * S₃.card) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
      _ = δ ^ ν * S₃.card := by
          rw [e2, mul_assoc, ← mul_assoc (δ ^ ν) (δ ^ (-ν)), hδνnν, one_mul]
      _ ≤ Gt.card := hsum
  -- enumerations
  set eG : Fin Gt.card ≃ Gt := Gt.equivFin.symm with heG
  let gG : Fin Gt.card → Fin n := fun j => (eG j : Fin n)
  have hgG : Function.Injective gG := fun x y h => eG.injective (Subtype.ext h)
  have hgGmem : ∀ j, gG j ∈ Gt := fun j => (eG j).2
  have hcnt : ∀ (P : Fin n → Prop) [DecidablePred P],
      ncard {j | P (gG j)} = (Gt.filter P).card := by
    intro P _
    have hco : ((↑(Gt.filter P) : Set (Fin n))).ncard = (Gt.filter P).card :=
      Set.ncard_coe_finset _
    rw [← hco]
    have himg : (↑(Gt.filter P) : Set (Fin n)) = gG '' {j | P (gG j)} := by
      ext i
      simp only [Finset.coe_filter, mem_ofPred_eq, mem_image]
      constructor
      · rintro ⟨hi, hP'⟩
        refine ⟨eG.symm ⟨i, hi⟩, ?_, ?_⟩
        · simp only [gG, Equiv.apply_symm_apply]; exact hP'
        · simp only [gG, Equiv.apply_symm_apply]
      · rintro ⟨j, hj, rfl⟩; exact ⟨hgGmem j, hj⟩
    rw [himg, ncard_image_of_injective _ hgG]
  have hGtpar : ∀ i ∈ Gt, par i ∈ Lcl ∧ i ∈ G (par i) := by
    intro i hi
    obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp hi
    have hpl : par i = l := (Finset.mem_filter.mp (hGsub l hl hil)).2
    rw [hpl]; exact ⟨hl, hil⟩
  have hGlGt : ∀ l ∈ Lcl, G l ⊆ Gt := fun l hl => Finset.subset_biUnion_of_mem G hl
  -- containers
  let J := Σ l : Lcl, Fin (p l.1)
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let lab : Fin (Fintype.card J) → Fin q := fun j => (eJ j).1.1
  let WJ : Fin (Fintype.card J) → Set Space := fun j => W (eJ j).1.1 (eJ j).2
  let cJ : Fin (Fintype.card J) → Space := fun j => c₀ (eJ j).1.1 (eJ j).2
  let f₁ : Fin (Fintype.card J) → Space := fun j => e₁ (eJ j).1.1 (eJ j).2
  let f₂ : Fin (Fintype.card J) → Space := fun j => e₂ (eJ j).1.1 (eJ j).2
  let f₃ : Fin (Fintype.card J) → Space := fun j => e₃ (eJ j).1.1 (eJ j).2
  have hlabin : ∀ j, lab j ∈ Lcl := fun j => (eJ j).1.2
  have hWsub : ∀ j, WJ j ⊆ Tube ρ (z (lab j)) (w (lab j)) ∩
      {y | |inner ℝ (f₁ j) (y - cJ j)| ≤ a (lab j) ∧ |inner ℝ (f₂ j) (y - cJ j)| ≤ b' (lab j)} :=
    fun j => (hP (lab j) (hLclne _ (hlabin j))).2.2.2.2.2.2.2.2.2.2.2.1 (eJ j).2
  have hκ0 : 0 < κ := by positivity
  have hLF : LocalFactor (2 * ν) δ ρ A B T := by
    refine ⟨Gt.card, gG, hgG, ?_, hGtsize, q, z, w, hw, hRsep, κ, hκ0, ?_, Fintype.card J, WJ,
      lab, cJ, f₁, f₂, f₃, ?_, ?_, ?_, ?_, ?_⟩
    · have : (0 : ℝ) < Gt.card := lt_of_lt_of_le (by positivity) hGtsize
      exact_mod_cast this
    · -- parentwise Katz–Tao
      intro l U hU
      rw [hcnt (fun i => T i ⊆ Tube ρ (z l) (w l) ∧ T i ⊆ U)]
      by_cases hl : l ∈ Lcl
      · have hsub : Gt.filter (fun i => T i ⊆ Tube ρ (z l) (w l) ∧ T i ⊆ U) ⊆
            (G l).filter (fun i => T i ⊆ U) := by
          intro i hi
          rw [Finset.mem_filter] at hi ⊢
          have hpl : l = par i := huniq i l hi.2.1
          obtain ⟨-, hiG⟩ := hGtpar i hi.1
          rw [hpl]; exact ⟨hiG, hi.2.2⟩
        have hKT := (hP l (hLclne l hl)).2.2.2.2.2.2.2.2.2.1 U hU
        have hcκ := (hbounds l hl).2.2.2.2.1
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hKT.trans (by gcongr))
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
          (sq_nonneg δ)
      · have hempty : Gt.filter (fun i => T i ⊆ Tube ρ (z l) (w l) ∧ T i ⊆ U) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro i hi h
          have hpl : l = par i := huniq i l h.1
          exact hl (hpl ▸ (hGtpar i hi).1)
        rw [hempty]; simp
    · intro j; exact (hP (lab j) (hLclne _ (hlabin j))).2.2.2.2.2.2.2.2.2.2.1 (eJ j).2
    · intro j y hy
      obtain ⟨hR, h1, h2⟩ := hWsub j hy
      obtain ⟨haA, -, hbB, -⟩ := hbounds (lab j) (hlabin j)
      exact ⟨hR, h1.trans haA, h2.trans hbB⟩
    · intro i
      obtain ⟨hl, hiG⟩ := hGtpar (gG i) (hgGmem i)
      obtain ⟨jj, hjj⟩ := (hP _ (hLclne _ hl)).2.2.2.2.2.2.2.2.2.2.2.2.1 (gG i) hiG
      refine ⟨eJ.symm ⟨⟨par (gG i), hl⟩, jj⟩, ?_⟩
      show T (gG i) ⊆ W (eJ (eJ.symm ⟨⟨par (gG i), hl⟩, jj⟩)).1.1
        (eJ (eJ.symm ⟨⟨par (gG i), hl⟩, jj⟩)).2
      rw [Equiv.apply_symm_apply]
      exact hjj
    · intro i
      obtain ⟨hl, hiG⟩ := hGtpar (gG i) (hgGmem i)
      have hdeg := (hP (par (gG i)) (hLclne _ hl)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (gG i) hiG
      have hWl : ∀ (l' : Fin q) (hl' : l' ∈ Lcl) (jj : Fin (p l')),
          W l' jj ⊆ Tube ρ (z l') (w l') := fun l' hl' jj y hy =>
        ((hP l' (hLclne l' hl')).2.2.2.2.2.2.2.2.2.2.2.1 jj hy).1
      have hsub : {x : J | T (gG i) ⊆ W x.1.1 x.2} ⊆
          (fun jj : Fin (p (par (gG i))) => (⟨⟨par (gG i), hl⟩, jj⟩ : J)) ''
            {jj | T (gG i) ⊆ W (par (gG i)) jj} := by
        rintro ⟨⟨l', hl'⟩, jj'⟩ hT
        have hTl : T (gG i) ⊆ W l' jj' := hT
        have hl'eq : l' = par (gG i) := huniq (gG i) l' (hTl.trans (hWl l' hl' jj'))
        subst hl'eq
        exact ⟨jj', hTl, rfl⟩
      have hle : ncard {j | T (gG i) ⊆ WJ j} ≤
          ncard {jj : Fin (p (par (gG i))) | T (gG i) ⊆ W (par (gG i)) jj} := by
        calc ncard {j | T (gG i) ⊆ WJ j} ≤ ncard {x : J | T (gG i) ⊆ W x.1.1 x.2} :=
              ncard_le_ncard_of_injOn eJ (fun j hj => hj) eJ.injective.injOn (toFinite _)
          _ ≤ ncard ((fun jj : Fin (p (par (gG i))) => (⟨⟨par (gG i), hl⟩, jj⟩ : J)) ''
                {jj | T (gG i) ⊆ W (par (gG i)) jj}) := ncard_le_ncard hsub (toFinite _)
          _ ≤ ncard {jj : Fin (p (par (gG i))) | T (gG i) ⊆ W (par (gG i)) jj} :=
              ncard_image_le (toFinite _)
      calc (ncard {j | T (gG i) ⊆ WJ j} : ℝ)
          ≤ ncard {jj : Fin (p (par (gG i))) | T (gG i) ⊆ W (par (gG i)) jj} := by
            exact_mod_cast hle
        _ ≤ δ ^ (-ν) := hdeg
        _ ≤ δ ^ (-(2 * ν)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    · intro j
      have hlj := hlabin j
      obtain ⟨haA, hA2, hbB, hB2, hcκ, hκ2⟩ := hbounds (lab j) hlj
      obtain ⟨hδa, -, h2δb, -, -, hc1, -⟩ := hP (lab j) (hLclne _ hlj)
      have hsat := (hP (lab j) (hLclne _ hlj)).2.2.2.2.2.2.2.2.2.2.2.2.2.2 (eJ j).2
      have hcount : (((G (lab j)).filter (fun i => T i ⊆ W (lab j) (eJ j).2)).card : ℝ) ≤
          contained (fun i => T (gG i)) (WJ j) := by
        unfold contained
        rw [hcnt (fun i => T i ⊆ WJ j)]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (hGlGt _ hlj))
      have ha0 : 0 < a (lab j) := hδ.trans_le hδa
      have hb0 : 0 < b' (lab j) := by linarith
      have hc0 : 0 < c (lab j) := by linarith
      have hA0 : 0 ≤ A := by positivity
      have hB0 : 0 ≤ B := le_trans hb0.le hbB
      have e2 : δ ^ (2 * ν) = δ ^ ν * δ ^ ν := by rw [← Real.rpow_add hδ]; ring_nf
      have hsat' : δ ^ ν * c (lab j) * a (lab j) * b' (lab j) ≤
          (contained (fun i => T (gG i)) (WJ j) : ℝ) * δ ^ 2 :=
        hsat.trans (mul_le_mul_of_nonneg_right hcount (sq_nonneg δ))
      rw [e2]
      exact flat_sat_arith hδν.le h64 hκ2 hA2.le hB2.le hκ0.le hA0 hB0 hc0.le ha0.le hb0.le hsat'
  -- the final call
  obtain ⟨l₀, hl₀⟩ : Lcl.Nonempty := hS₃ne.image par
  obtain ⟨haA, hA2, hbB, hB2, -, -⟩ := hbounds l₀ hl₀
  obtain ⟨hδa, -, h2δb, -, hΛab, -⟩ := hP l₀ (hLclne l₀ hl₀)
  have hBρ : B ≤ ρ := min_le_right _ _
  have hΛ0 : 0 < Λ := by linarith
  have hB0 : 0 < B := by linarith
  have e3 : δ ^ (-ν - ζ₂ / 200) * δ ^ (ζ₂ / 200) = δ ^ (-ν) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hflatAB : A ≤ δ ^ (ζ₂ / 200) * B := by
    have hδnν0 : 0 ≤ δ ^ (-ν) := by positivity
    have h1 : Λ * A ≤ 16 * δ ^ (-ν) * B := by
      calc Λ * A ≤ Λ * (2 * a l₀) := mul_le_mul_of_nonneg_left hA2.le hΛ0.le
        _ = 2 * (Λ * a l₀) := by ring
        _ ≤ 2 * (8 * δ ^ (-ν) * b' l₀) := by linarith
        _ ≤ 2 * (8 * δ ^ (-ν) * B) := by
            have := mul_le_mul_of_nonneg_left hbB (by positivity : (0:ℝ) ≤ 8 * δ ^ (-ν))
            linarith
        _ = 16 * δ ^ (-ν) * B := by ring
    have h2 : 16 * δ ^ (-ν) ≤ Λ * δ ^ (ζ₂ / 200) := by
      have hpos : 0 ≤ δ ^ (ζ₂ / 200) := by positivity
      have := mul_le_mul_of_nonneg_right hΛ hpos
      rw [mul_assoc, e3] at this
      linarith
    have h3 : Λ * A ≤ Λ * (δ ^ (ζ₂ / 200) * B) := by
      calc Λ * A ≤ 16 * δ ^ (-ν) * B := h1
        _ ≤ Λ * δ ^ (ζ₂ / 200) * B := mul_le_mul_of_nonneg_right h2 hB0.le
        _ = Λ * (δ ^ (ζ₂ / 200) * B) := by ring
    exact le_of_mul_le_mul_left h3 hΛ0
  have hAB : A ≤ B := by
    have : δ ^ (ζ₂ / 200) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
    calc A ≤ δ ^ (ζ₂ / 200) * B := hflatAB
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right this hB0.le
      _ = B := one_mul B
  exact flat_refinement_of_local_factor x v hδ hδ1 hρ (by linarith) (by positivity) hζ
    (hδa.trans haA) hAB hBρ hflatAB herror hretain hv hF hLF


/-- `Nat.log 2 m ≤ log m / log 2`. -/
lemma natLog_two_le_log {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
  have h := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have h' : ((2 : ℝ) ^ Nat.log 2 m) ≤ m := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at hlog

/-- `Nat.log 2 ⌊y⌋₊ ≤ log y / log 2` for `y ≥ 1`. -/
lemma natLog_floor_le {y : ℝ} (hy : 1 ≤ y) :
    (Nat.log 2 ⌊y⌋₊ : ℝ) * Real.log 2 ≤ Real.log y := by
  have hfl : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  refine (natLog_two_le_log hfl).trans ?_
  exact Real.log_le_log (by exact_mod_cast hfl) (Nat.floor_le (by linarith))

/-- The polylogarithmic class count of `flat_exit` is eventually below `δ^(-ν)` when
`n ≤ C δ^(-4)`. -/
theorem flat_exit_pig_eventually (ν C : ℝ) (hν : 0 < ν) (hC : 1 ≤ C) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ n : ℕ, (n : ℝ) ≤ C * δ ^ (-4 : ℝ) →
      (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
        (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ δ ^ (-ν) := by
  -- with `t = log (1/δ)`, everything is a cubic polynomial in `t` against `exp (ν t)`
  set l2 := Real.log 2 with hl2
  have hl2pos : 0 < l2 := Real.log_pos (by norm_num)
  set A : ℝ := (2 + 1 / l2) ^ 2 * (2 + (Real.log C + 1) / l2 + (5 + ν) / l2) with hA
  have hA0 : 0 < A := by
    have : 0 ≤ Real.log C := Real.log_nonneg hC
    positivity
  set T : ℝ := max 1 (192 * A / ν ^ 4) with hT
  refine ⟨Real.exp (-T), Real.exp_pos _, ?_, ?_⟩
  · have hT1 : 1 ≤ T := le_max_left _ _
    have : Real.exp (-T) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      norm_num; linarith
    linarith
  intro δ hδ hδd n hn
  set t : ℝ := Real.log (1 / δ) with ht
  have hδ1 : δ < 1 := by
    have : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr (by have := le_max_left 1 (192 * A / ν ^ 4); linarith)
    linarith
  have htT : T ≤ t := by
    rw [ht, one_div, Real.log_inv, le_neg]
    calc Real.log δ ≤ Real.log (Real.exp (-T)) := Real.log_le_log hδ hδd
      _ = -T := Real.log_exp _
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) htT
  have ht0 : 0 ≤ t := by linarith
  have hδt : δ = Real.exp (-t) := by
    rw [ht, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  -- the three logarithms
  have h1 : (Nat.log 2 ⌊2 / δ⌋₊ : ℝ) ≤ (l2 + t) / l2 := by
    have hy : 1 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have := natLog_floor_le hy
    rw [le_div_iff₀ hl2pos]
    calc (Nat.log 2 ⌊2 / δ⌋₊ : ℝ) * l2 ≤ Real.log (2 / δ) := this
      _ = l2 + t := by
          rw [Real.log_div (by norm_num) hδ.ne', ht, one_div, Real.log_inv]; ring
  have h3 : (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ : ℝ) ≤ (Real.log C + (4 + ν) * t) / l2 := by
    by_cases hy : 1 ≤ (n : ℝ) * δ ^ (-ν)
    · have := natLog_floor_le hy
      rw [le_div_iff₀ hl2pos]
      refine this.trans ?_
      have hpos : 0 < (n : ℝ) * δ ^ (-ν) := by linarith
      have hbound : (n : ℝ) * δ ^ (-ν) ≤ C * Real.exp ((4 + ν) * t) := by
        have hδ4 : δ ^ (-4 : ℝ) = Real.exp (4 * t) := by
          rw [hδt, ← Real.exp_mul]; ring_nf
        have hδν : δ ^ (-ν) = Real.exp (ν * t) := by
          rw [hδt, ← Real.exp_mul]; ring_nf
        calc (n : ℝ) * δ ^ (-ν) ≤ C * δ ^ (-4 : ℝ) * δ ^ (-ν) :=
              mul_le_mul_of_nonneg_right hn (by positivity)
          _ = C * Real.exp ((4 + ν) * t) := by
              rw [hδ4, hδν, mul_assoc, ← Real.exp_add]; ring_nf
      calc Real.log ((n : ℝ) * δ ^ (-ν)) ≤ Real.log (C * Real.exp ((4 + ν) * t)) :=
            Real.log_le_log hpos hbound
        _ = Real.log C + (4 + ν) * t := by
            rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    · have hfl : ⌊(n : ℝ) * δ ^ (-ν)⌋₊ = 0 := Nat.floor_eq_zero.mpr (not_le.mp hy)
      rw [hfl, Nat.log_zero_right, Nat.cast_zero]
      have : 0 ≤ Real.log C := Real.log_nonneg hC
      positivity
  -- polynomial against exponential
  have hpoly : (((Nat.log 2 ⌊2 / δ⌋₊ + 1) * (Nat.log 2 ⌊2 / δ⌋₊ + 1) *
      (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ + 1) : ℕ) : ℝ) ≤ A * t ^ 3 := by
    push_cast
    have e1 : (Nat.log 2 ⌊2 / δ⌋₊ : ℝ) + 1 ≤ (2 + 1 / l2) * t := by
      have : (l2 + t) / l2 = 1 + t / l2 := by field_simp
      rw [this] at h1
      have : t / l2 ≤ (1 / l2) * t := by rw [div_eq_mul_inv, one_div, mul_comm]
      nlinarith
    have e3 : (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ : ℝ) + 1 ≤
        (2 + (Real.log C + 1) / l2 + (5 + ν) / l2) * t := by
      have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
      have h3' : (Real.log C + (4 + ν) * t) / l2 ≤ ((Real.log C + 1) / l2 + (5 + ν) / l2) * t := by
        rw [← add_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2pos]
        nlinarith
      nlinarith
    have hn0 : 0 ≤ (Nat.log 2 ⌊2 / δ⌋₊ : ℝ) + 1 := by positivity
    have hn3 : 0 ≤ (Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ : ℝ) + 1 := by positivity
    calc ((Nat.log 2 ⌊2 / δ⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊2 / δ⌋₊ : ℝ) + 1) *
          ((Nat.log 2 ⌊(n : ℝ) * δ ^ (-ν)⌋₊ : ℝ) + 1)
        ≤ ((2 + 1 / l2) * t) * ((2 + 1 / l2) * t) *
            ((2 + (Real.log C + 1) / l2 + (5 + ν) / l2) * t) := by gcongr
      _ = A * t ^ 3 := by rw [hA]; ring
  have hexp : A * t ^ 3 ≤ δ ^ (-ν) := by
    have hδν : δ ^ (-ν) = Real.exp (ν * t) := by
      rw [hδt, ← Real.exp_mul]; ring_nf
    rw [hδν]
    have hνt : 0 ≤ ν * t := by positivity
    have hTa : 192 * A / ν ^ 4 ≤ t := le_trans (le_max_right _ _) htT
    have hfact := Real.pow_div_factorial_le_exp (ν * t) hνt 4
    norm_num [Nat.factorial] at hfact
    have hν4 : 0 < ν ^ 4 := by positivity
    have h192 : 192 * A ≤ t * ν ^ 4 := by
      rw [div_le_iff₀ hν4] at hTa; linarith
    have : A * t ^ 3 ≤ (ν * t) ^ 4 / 24 := by
      have : (ν * t) ^ 4 / 24 = t ^ 3 * (t * ν ^ 4) / 24 := by ring
      rw [this]
      have ht3 : 0 ≤ t ^ 3 := by positivity
      nlinarith
    linarith
  linarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
